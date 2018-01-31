(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Term
open Termops
open Univ
open Evd
open Environ
open EConstr
open Vars
open Context.Rel.Declaration

(** This module implements a call by name reduction used by (at
    least) evarconv unification and cbn tactic.

    It has an ability to "refold" constants by storing constants and
    their parameters in its stack.
*)

(** Support for reduction effects *)

(** create a persistent set to store effect functions *)
module ConstrMap = Map.Make (Constr)

(* Table bindings a constant to an effect *)
let constant_effect_table = Summary.ref ~name:"machine-reduction-side-effect" ConstrMap.empty

(* Table bindings function key to effective functions *)
let effect_table = Summary.ref ~name:"machine-reduction-function-effect" String.Map.empty

(** a test to know whether a constant is actually the effect function *)
let reduction_effect_hook env sigma termkey c =
  try
    let funkey = ConstrMap.find termkey !constant_effect_table in
    let effect = String.Map.find funkey !effect_table in
    effect env sigma (Lazy.force c)
  with Not_found -> ()

(** Machinery about stack of unfolded constants *)
module Cst_stack = struct
  open EConstr
  (** constant * params * args

      - constant applied to params = term in head applied to args
      - there is at most one arguments with an empty list of args, it must be the first.
      - in args, the int represents the indice of the first arg to consider *)
  type t = (constr * constr list * (int * constr array) list)  list

  let empty = []

  let drop_useless = function
    | _ :: ((_,_,[])::_ as q) -> q
    | l -> l

  let add_param h cst_l =
    let append2cst = function
      | (c,params,[]) -> (c, h::params, [])
      | (c,params,((i,t)::q)) when i = pred (Array.length t) ->
          (c, params, q)
      | (c,params,(i,t)::q) ->
          (c, params, (succ i,t)::q)
    in
    drop_useless (List.map append2cst cst_l)

  let add_args cl =
    List.map (fun (a,b,args) -> (a,b,(0,cl)::args))

  let add_cst cst = function
    | (_,_,[]) :: q as l -> l
    | l -> (cst,[],[])::l

  let best_cst = function
    | (cst,params,[])::_ -> Some(cst,params)
    | _ -> None

  let reference sigma t = match best_cst t with
    | Some (c, _) when isConst sigma c -> Some (fst (destConst sigma c))
    | _ -> None

  (** [best_replace d cst_l c] makes the best replacement for [d]
      by [cst_l] in [c] *)
  let best_replace sigma d cst_l c =
    let reconstruct_head = List.fold_left
                             (fun t (i,args) -> mkApp (t,Array.sub args i (Array.length args - i))) in
    List.fold_right
      (fun (cst,params,args) t -> Termops.replace_term sigma
                                    (reconstruct_head d args)
                                    (applist (cst, List.rev params))
                                    t) cst_l c

  let pr l =
    let open Pp in
    let p_c c = Termops.print_constr c in
    prlist_with_sep pr_semicolon
      (fun (c,params,args) ->
         hov 1 (str"(" ++ p_c c ++ str ")" ++ spc () ++ pr_sequence p_c params ++ spc () ++ str "(args:" ++
                pr_sequence (fun (i,el) -> prvect_with_sep spc p_c (Array.sub el i (Array.length el - i))) args ++
                str ")")) l
end


(** The type of (machine) stacks (= lambda-bar-calculus' contexts) *)
module Stack :
sig
  open EConstr
  type 'a app_node
  val pr_app_node : ('a -> Pp.std_ppcmds) -> 'a app_node -> Pp.std_ppcmds

  type cst_member =
    | Cst_const of pconstant
    | Cst_proj of projection

  type 'a member =
    | App of 'a app_node
    | Case of case_info * 'a * 'a array * Cst_stack.t
    | Proj of int * int * projection * Cst_stack.t
    | Fix of ('a, 'a) pfixpoint * 'a t * Cst_stack.t
    | Cst of cst_member * int * int list * 'a t * Cst_stack.t
    | Shift of int
    | Update of 'a
  and 'a t = 'a member list

  exception IncompatibleFold2

  val pr : ('a -> Pp.std_ppcmds) -> 'a t -> Pp.std_ppcmds
  val empty : 'a t
  val is_empty : 'a t -> bool
  val append_app : 'a array -> 'a t -> 'a t
  val decomp : 'a t -> ('a * 'a t) option
  val decomp_node_last : 'a app_node -> 'a t -> ('a * 'a t)
  val compare_shape : 'a t -> 'a t -> bool
  val map : ('a -> 'a) -> 'a t -> 'a t
  val fold2 : ('a -> constr -> constr -> 'a) -> 'a ->
    constr t -> constr t -> 'a * int * int
  val append_app_list : 'a list -> 'a t -> 'a t
  val strip_app : 'a t -> 'a t * 'a t
  val strip_n_app : int -> 'a t -> ('a t * 'a * 'a t) option
  val not_purely_applicative : 'a t -> bool
  val list_of_app_stack : constr t -> constr list option
  val assign : 'a t -> int -> 'a -> 'a t
  val args_size : 'a t -> int
  val tail : int -> 'a t -> 'a t
  val nth : 'a t -> int -> 'a
  val best_state : evar_map -> constr * constr t -> Cst_stack.t -> constr * constr t
  val zip : ?refold:bool -> evar_map -> constr * constr t -> constr
end =
struct
  open EConstr
  type 'a app_node = int * 'a array * int
  (* first releavnt position, arguments, last relevant position *)

  (* Invariant that this module must ensure : (behare of direct access to
     app_node by the rest of Reductionops) - in app_node (i,_,j) i <= j - There
     is no array realocation (outside of debug printing) *)

  let pr_app_node pr (i,a,j) =
    let open Pp in surround (
      prvect_with_sep pr_comma pr (Array.sub a i (j - i + 1))
    )


  type cst_member =
    | Cst_const of pconstant
    | Cst_proj of projection

  type 'a member =
    | App of 'a app_node
    | Case of Term.case_info * 'a * 'a array * Cst_stack.t
    | Proj of int * int * projection * Cst_stack.t
    | Fix of ('a, 'a) pfixpoint * 'a t * Cst_stack.t
    | Cst of cst_member * int * int list * 'a t * Cst_stack.t
    | Shift of int
    | Update of 'a
  and 'a t = 'a member list

  let rec pr_member pr_c member =
    let open Pp in
    let pr_c x = hov 1 (pr_c x) in
    match member with
    | App app -> str "ZApp" ++ pr_app_node pr_c app
    | Case (_,_,br,cst) ->
        str "ZCase(" ++
        prvect_with_sep (pr_bar) pr_c br
        ++ str ")"
    | Proj (n,m,p,cst) ->
        str "ZProj(" ++ int n ++ pr_comma () ++ int m ++
        pr_comma () ++ pr_con (Projection.constant p) ++ str ")"
    | Fix (f,args,cst) ->
        str "ZFix(" ++ Termops.pr_fix pr_c f
        ++ pr_comma () ++ pr pr_c args ++ str ")"
    | Cst (mem,curr,remains,params,cst_l) ->
        str "ZCst(" ++ pr_cst_member pr_c mem ++ pr_comma () ++ int curr
        ++ pr_comma () ++
        prlist_with_sep pr_semicolon int remains ++
        pr_comma () ++ pr pr_c params ++ str ")"
    | Shift i -> str "ZShift(" ++ int i ++ str ")"
    | Update t -> str "ZUpdate(" ++ pr_c t ++ str ")"
  and pr pr_c l =
    let open Pp in
    prlist_with_sep pr_semicolon (fun x -> hov 1 (pr_member pr_c x)) l

  and pr_cst_member pr_c c =
    let open Pp in
    match c with
    | Cst_const (c, u) ->
        if Univ.Instance.is_empty u then Constant.print c
        else str"(" ++ Constant.print c ++ str ", " ++
             Univ.Instance.pr Univ.Level.pr u ++ str")"
    | Cst_proj p ->
        str".(" ++ Constant.print (Projection.constant p) ++ str")"

  let empty = []
  let is_empty = CList.is_empty

  let append_app v s =
    let le = Array.length v in
    if Int.equal le 0 then s else App (0,v,pred le) :: s

  let decomp_node (i,l,j) sk =
    if i < j then (l.(i), App (succ i,l,j) :: sk)
    else (l.(i), sk)

  let decomp = function
    | App node::s -> Some (decomp_node node s)
    | _ -> None

  let decomp_node_last (i,l,j) sk =
    if i < j then (l.(j), App (i,l,pred j) :: sk)
    else (l.(j), sk)

  let compare_shape stk1 stk2 =
    let rec compare_rec bal stk1 stk2 =
      match (stk1,stk2) with
        ([],[]) -> Int.equal bal 0
      | ((Update _|Shift _)::s1, _) -> compare_rec bal s1 stk2
      | (_, (Update _|Shift _)::s2) -> compare_rec bal stk1 s2
      | (App (i,_,j)::s1, _) -> compare_rec (bal + j + 1 - i) s1 stk2
      | (_, App (i,_,j)::s2) -> compare_rec (bal - j - 1 + i) stk1 s2
      | (Case(c1,_,_,_)::s1, Case(c2,_,_,_)::s2) ->
          Int.equal bal 0 (* && c1.ci_ind  = c2.ci_ind *) && compare_rec 0 s1 s2
      | (Proj (n1,m1,p,_)::s1, Proj(n2,m2,p2,_)::s2) ->
          Int.equal bal 0 && compare_rec 0 s1 s2
      | (Fix(_,a1,_)::s1, Fix(_,a2,_)::s2) ->
          Int.equal bal 0 && compare_rec 0 a1 a2 && compare_rec 0 s1 s2
      | (Cst (_,_,_,p1,_)::s1, Cst (_,_,_,p2,_)::s2) ->
          Int.equal bal 0 && compare_rec 0 p1 p2 && compare_rec 0 s1 s2
      | (_,_) -> false in
    compare_rec 0 stk1 stk2

  exception IncompatibleFold2
  let fold2 f o sk1 sk2 =
    let rec aux o lft1 sk1 lft2 sk2 =
      let fold_array =
        Array.fold_left2 (fun a x y -> f a (Vars.lift lft1 x) (Vars.lift lft2 y))
      in
      match sk1,sk2 with
      | [], [] -> o,lft1,lft2
      | Shift n :: q1, _ -> aux o (lft1+n) q1 lft2 sk2
      | _, Shift n :: q2 -> aux o lft1 sk1 (lft2+n) q2
      | App n1 :: q1, App n2 :: q2 ->
          let t1,l1 = decomp_node_last n1 q1 in
          let t2,l2 = decomp_node_last n2 q2 in
          aux (f o (Vars.lift lft1 t1) (Vars.lift lft2 t2))
            lft1 l1 lft2 l2
      | Case (_,t1,a1,_) :: q1, Case (_,t2,a2,_) :: q2 ->
          aux (fold_array
                 (f o (Vars.lift lft1 t1) (Vars.lift lft2 t2))
                 a1 a2) lft1 q1 lft2 q2
      | Proj (n1,m1,p1,_) :: q1, Proj (n2,m2,p2,_) :: q2 ->
          aux o lft1 q1 lft2 q2
      | Fix ((_,(_,a1,b1)),s1,_) :: q1, Fix ((_,(_,a2,b2)),s2,_) :: q2 ->
          let (o',lft1',lft2') = aux (fold_array (fold_array o b1 b2) a1 a2)
                                   lft1 (List.rev s1) lft2 (List.rev s2) in
          aux o' lft1' q1 lft2' q2
      | Cst (cst1,_,_,params1,_) :: q1, Cst (cst2,_,_,params2,_) :: q2 ->
          let (o',lft1',lft2') =
            aux o lft1 (List.rev params1) lft2 (List.rev params2)
          in aux o' lft1' q1 lft2' q2
      | (((Update _|App _|Case _|Proj _|Fix _| Cst _) :: _|[]), _) ->
          raise IncompatibleFold2
    in aux o 0 (List.rev sk1) 0 (List.rev sk2)

  let rec map f x = List.map (function
    | Update _ -> assert false
    | (Proj (_,_,_,_) | Shift _) as e -> e
    | App (i,a,j) ->
        let le = j - i + 1 in
        App (0,Array.map f (Array.sub a i le), le-1)
    | Case (info,ty,br,alt) -> Case (info, f ty, Array.map f br, alt)
    | Fix ((r,(na,ty,bo)),arg,alt) ->
        Fix ((r,(na,Array.map f ty, Array.map f bo)),map f arg,alt)
    | Cst (cst,curr,remains,params,alt) ->
        Cst (cst,curr,remains,map f params,alt)
  ) x

  let append_app_list l s =
    let a = Array.of_list l in
    append_app a s

  let rec args_size = function
    | App (i,_,j)::s -> j + 1 - i + args_size s
    | Shift(_)::s -> args_size s
    | Update(_)::s -> args_size s
    | (Case _|Fix _|Proj _|Cst _)::_ | [] -> 0

  let strip_app s =
    let rec aux out = function
      | ( App _ | Shift _ as e) :: s -> aux (e :: out) s
      | s -> List.rev out,s
    in aux [] s
  let strip_n_app n s =
    let rec aux n out = function
      | Shift k as e :: s -> aux n (e :: out) s
      | App (i,a,j) as e :: s ->
          let nb = j  - i + 1 in
          if n >= nb then
            aux (n - nb) (e::out) s
          else
            let p = i+n in
            Some (CList.rev
                    (if Int.equal n 0 then out else App (i,a,p-1) :: out),
                  a.(p),
                  if j > p then App(succ p,a,j)::s else s)
      | s -> None
    in aux n [] s

  let not_purely_applicative args =
    List.exists (function (Fix _ | Case _ | Proj _ | Cst _) -> true | _ -> false) args

  let list_of_app_stack s =
    let rec aux = function
      | App (i,a,j) :: s ->
          let (k,(args',s')) = aux s in
          let a' = Array.map (Vars.lift k) (Array.sub a i (j - i + 1)) in
          k,(Array.fold_right (fun x y -> x::y) a' args', s')
      | Shift n :: s ->
          let (k,(args',s')) = aux s in (k+n,(args', s'))
      | s -> (0,([],s)) in
    let (lft,(out,s')) = aux s in
    let init = match s' with [] when Int.equal lft 0 -> true | _ -> false in
    Option.init init out

  let assign s p c =
    match strip_n_app p s with
    | Some (pre,_,sk) -> pre @ (App (0,[|c|],0)::sk)
    | None -> assert false

  let tail n0 s0 =
    let rec aux lft n s =
      let out s = if Int.equal lft 0 then s else Shift lft :: s in
      if Int.equal n 0 then out s else
        match s with
        | App (i,a,j) :: s ->
            let nb = j  - i + 1 in
            if n >= nb then
              aux lft (n - nb) s
            else
              let p = i+n in
              if j >= p then App(p,a,j)::s else s
        | Shift k :: s' -> aux (lft+k) n s'
        | _ -> raise (Invalid_argument "Reductionops.Stack.tail")
    in aux 0 n0 s0

  let nth s p =
    match strip_n_app p s with
    | Some (_,el,_) -> el
    | None -> raise Not_found

  (** This function breaks the abstraction of Cst_stack ! *)
  let best_state sigma (_,sk as s) l =
    let rec aux sk def = function
      |(cst, params, []) -> (cst, append_app_list (List.rev params) sk)
      |(cst, params, (i,t)::q) -> match decomp sk with
        | Some (el,sk') when EConstr.eq_constr sigma el t.(i) ->
            if i = pred (Array.length t)
            then aux sk' def (cst, params, q)
            else aux sk' def (cst, params, (succ i,t)::q)
        | _ -> def
    in List.fold_left (aux sk) s l

  let constr_of_cst_member f sk =
    match f with
    | Cst_const (c, u) -> mkConstU (c, EInstance.make u), sk
    | Cst_proj p ->
        match decomp sk with
        | Some (hd, sk) -> mkProj (p, hd), sk
        | None -> assert false

  let zip ?(refold=false) sigma s =
    let rec zip = function
      | f, [] -> f
      | f, (App (i,a,j) :: s) ->
          let a' = if Int.equal i 0 && Int.equal j (Array.length a - 1)
            then a
            else Array.sub a i (j - i + 1) in
          zip (mkApp (f, a'), s)
      | f, (Case (ci,rt,br,cst_l)::s) when refold ->
          zip (best_state sigma (mkCase (ci,rt,f,br), s) cst_l)
      | f, (Case (ci,rt,br,_)::s) -> zip (mkCase (ci,rt,f,br), s)
      | f, (Fix (fix,st,cst_l)::s) when refold ->
          zip (best_state sigma (mkFix fix, st @ (append_app [|f|] s)) cst_l)
      | f, (Fix (fix,st,_)::s) -> zip
                                    (mkFix fix, st @ (append_app [|f|] s))
      | f, (Cst (cst,_,_,params,cst_l)::s) when refold ->
          zip (best_state sigma (constr_of_cst_member cst (params @ (append_app [|f|] s))) cst_l)
      | f, (Cst (cst,_,_,params,_)::s) ->
          zip (constr_of_cst_member cst (params @ (append_app [|f|] s)))
      | f, (Shift n::s) -> zip (lift n f, s)
      | f, (Proj (n,m,p,cst_l)::s) when refold ->
          zip (best_state sigma (mkProj (p,f),s) cst_l)
      | f, (Proj (n,m,p,_)::s) -> zip (mkProj (p,f),s)
      | _, (Update _::_) -> assert false
    in
    zip s

end

(** The type of (machine) states (= lambda-bar-calculus' cuts) *)
type state = constr * constr Stack.t


(*************************************)
(*** Reduction Functions Operators ***)
(*************************************)

let safe_meta_value sigma ev =
  try Some (Evd.meta_value sigma ev)
  with Not_found -> None

(*************************************)
(*** Reduction using bindingss ***)
(*************************************)

(* Beta Reduction tools *)

let apply_subst recfun env sigma t stack =
  let rec aux env t stack =
    match (Stack.decomp stack, EConstr.kind sigma t) with
    | Some (h,stacktl), Lambda (_,_,c) ->
        aux (h::env) c stacktl
    | _ -> recfun sigma (substl env t, stack)
  in aux env t stack

(** @return c if there is a constant c whose body is bd
    @return bd else.

    It has only a meaning because internal representation of "Fixpoint f x
    := t" is Definition f := fix f x => t

    Even more fragile that we could hope because do Module M. Fixpoint
    f x := t. End M. Definition f := u. and say goodbye to any hope
    of refolding M.f this way ...
*)
let magicaly_constant_of_fixbody env sigma reference bd = function
  | Name.Anonymous -> bd
  | Name.Name id ->
      try
        let (cst_mod,cst_sect,_) = Constant.repr3 reference in
        let cst = Constant.make3 cst_mod cst_sect (Label.of_id id) in
        let (cst, u), ctx = Universes.fresh_constant_instance env cst in
        match constant_opt_value_in env (cst,u) with
        | None -> bd
        | Some t ->
            let csts = EConstr.eq_constr_universes sigma (EConstr.of_constr t) bd in
            begin match csts with
            | Some csts ->
                let subst = Universes.Constraints.fold (fun (l,d,r) acc ->
                  Univ.LMap.add (Option.get (Universe.level l)) (Option.get (Universe.level r)) acc)
                  csts Univ.LMap.empty
                in
                let inst = Instance.subst_fn (fun u -> Univ.LMap.find u subst) u in
                mkConstU (cst, EInstance.make inst)
            | None -> bd
            end
      with
      | Not_found -> bd

let contract_cofix ?env sigma ?reference (bodynum,(names,types,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let make_Fi j =
    let ind = nbodies-j-1 in
    if Int.equal bodynum ind then mkCoFix (ind,typedbodies)
    else
      let bd = mkCoFix (ind,typedbodies) in
      match env with
      | None -> bd
      | Some e ->
          match reference with
          | None -> bd
          | Some r -> magicaly_constant_of_fixbody e sigma r bd names.(ind) in
  let closure = List.init nbodies make_Fi in
  substl closure bodies.(bodynum)

(** Similar to the "fix" case below *)
let reduce_and_refold_cofix recfun env sigma cofix sk =
  let raw_answer =
    contract_cofix sigma cofix in
  apply_subst
    (fun sigma (t,sk') -> recfun (t,sk'))
    [] sigma raw_answer sk

(* contracts fix==FIX[nl;i](A1...Ak;[F1...Fk]{B1....Bk}) to produce
   Bi[Fj --> FIX[nl;j](A1...Ak;[F1...Fk]{B1...Bk})] *)

let contract_fix ?env sigma ((recindices,bodynum),(names,types,bodies as typedbodies)) =
  let nbodies = Array.length recindices in
  let make_Fi j =
    let ind = nbodies-j-1 in
    if Int.equal bodynum ind then mkFix ((recindices,ind),typedbodies)
    else
      let bd = mkFix ((recindices,ind),typedbodies) in
      match env with
      | None -> bd
      | Some e -> bd in
  let closure = List.init nbodies make_Fi in
  substl closure bodies.(bodynum)

(** First we substitute the Rel bodynum by the fixpoint and then we try to
    replace the fixpoint by the best constant from [cst_l]
    Other rels are directly substituted by constants "magically found from the
    context" in contract_fix *)
let reduce_and_refold_fix recfun env sigma fix sk =
  let raw_answer =
    contract_fix sigma fix in
  apply_subst
    (fun sigma (t,sk') -> recfun (t,sk'))
    [] sigma raw_answer sk

(** Generic reduction function with environment

    Here is where unfolded constant are stored in order to be
    eventualy refolded.

    If tactic_mode is true, it uses ReductionBehaviour, prefers
    refold constant instead of value and tries to infer constants
    fix and cofix came from.

    It substitutes fix and cofix by the constant they come from in
    contract_* in any case .
*)

let debug_RAKAM = ref (false)
(* let _ = Goptions.declare_bool_option { *)
(*   Goptions.optdepr = false; *)
(*   Goptions.optname = *)
(*     "Print states of the Reductionops abstract machine"; *)
(*   Goptions.optkey = ["Debug";"RAKAM"]; *)
(*   Goptions.optread = (fun () -> !debug_RAKAM); *)
(*   Goptions.optwrite = (fun a -> debug_RAKAM:=a); *)
(* } *)

let rec whd_state_gen flags env fixs sigma =
  let open Context.Named.Declaration in
  let safe_lookup_named_body id =
    try
      match lookup_named id env with
      | LocalDef (_,body,_) -> Some body
      | _ -> None
    with Not_found ->
      let open Context.Named in
      try
        get_value (lookup id fixs)
      with Not_found ->
        None
  in
  let cst_l = Cst_stack.empty in
  let rec whrec (x, stack) =
    let () = if !debug_RAKAM then
        let open Pp in
        let pr c = Termops.print_constr c in
        Feedback.msg_notice
          (h 0 (str "<<" ++ pr x ++
                str "|" ++ cut () ++ Cst_stack.pr cst_l ++
                str "|" ++ cut () ++ Stack.pr pr stack ++
                str ">>"))
    in
    let c0 = EConstr.kind sigma x in
    let fold () =
      let () = if !debug_RAKAM then
          let open Pp in Feedback.msg_notice (str "<><><><><>") in
      ((EConstr.of_kind c0, stack),cst_l)
    in
    match c0 with
    | Rel n when CClosure.RedFlags.red_set flags CClosure.RedFlags.fDELTA ->
        (match lookup_rel n env with
         | LocalDef (_,body,_) -> whrec (lift n body, stack)
         | _ -> fold ())
    | Var id when CClosure.RedFlags.red_set flags (CClosure.RedFlags.fVAR id) ->
        let body = safe_lookup_named_body id in
        begin
          match body with
          | Some body ->
              whrec (body, stack)
          | _ -> fold ()
        end
    | Var id when CClosure.RedFlags.red_set flags CClosure.RedFlags.fFIX ->
        let body =
          try
            let open Context.Named in
            get_value (lookup id fixs)
          with Not_found -> None
        in
        begin
          match body with
          | Some body ->
              whrec (body, stack)
          | _ -> fold ()
        end
    | Evar ev -> fold ()
    | Meta ev ->
        (match safe_meta_value sigma ev with
         | Some body -> whrec (EConstr.of_constr body, stack)
         | None -> fold ())
    | Const (c,u) ->
        reduction_effect_hook env sigma (EConstr.to_constr sigma x)
          (lazy (EConstr.to_constr sigma (Stack.zip sigma (x,stack))));
        if CClosure.RedFlags.red_set flags (CClosure.RedFlags.fCONST c) then
          let u' = EInstance.kind sigma u in
          (match constant_opt_value_in env (c, u') with
           | None -> fold ()
           | Some body ->
               let body = EConstr.of_constr body in
               whrec (body, stack)
          )
        else fold ()

    | Proj (p, c) when CClosure.RedFlags.red_projection flags p ->
        let pb = lookup_projection p env in
        let npars = pb.Declarations.proj_npars
        and arg = pb.Declarations.proj_arg in
        let stack' = (c, Stack.Proj (npars, arg, p, Cst_stack.empty (*cst_l*)) :: stack) in
        whrec stack'

    | LetIn (_,b,_,c) when CClosure.RedFlags.red_set flags CClosure.RedFlags.fZETA ->
        apply_subst (fun _ -> whrec) [b] sigma c stack
    | Cast (c,_,_) -> whrec (c, stack)
    | App (f,cl)  ->
        whrec (f, Stack.append_app cl stack)
    | Lambda (na,t,c) ->
        (match Stack.decomp stack with
         | Some _ when CClosure.RedFlags.red_set flags CClosure.RedFlags.fBETA ->
             apply_subst (fun _ -> whrec) [] sigma x stack
         | None when CClosure.RedFlags.red_set flags CClosure.RedFlags.fETA ->
             let env' = push_rel (LocalAssum (na, t)) env in
             let whrec' = whd_state_gen flags env' fixs sigma in
             (match EConstr.kind sigma (Stack.zip sigma (fst (whrec' (c, Stack.empty)))) with
              | App (f,cl) ->
                  let napp = Array.length cl in
                  if napp > 0 then
                    let (x', l'),_ = whrec' (Array.last cl, Stack.empty) in
                    match EConstr.kind sigma x', l' with
                    | Rel 1, [] ->
                        let lc = Array.sub cl 0 (napp-1) in
                        let u = if Int.equal napp 1 then f else mkApp (f,lc) in
                        if noccurn sigma 1 u then (pop u,Stack.empty),Cst_stack.empty else fold ()
                    | _ -> fold ()
                  else fold ()
              | _ -> fold ())
         | _ -> fold ())

    | Case (ci,p,d,lf) ->
        whrec (d, Stack.Case (ci,p,lf,cst_l) :: stack)

    | Fix ((ri,n),_ as f) ->
        (match Stack.strip_n_app ri.(n) stack with
         |None -> fold ()
         |Some (bef,arg,s') ->
             whrec (arg, Stack.Fix(f,bef,cst_l)::s'))

    | Construct ((ind,c),u) ->
        let use_match = CClosure.RedFlags.red_set flags CClosure.RedFlags.fMATCH in
        let use_fix = CClosure.RedFlags.red_set flags CClosure.RedFlags.fFIX in
        if use_match || use_fix then
          match Stack.strip_app stack with
          |args, (Stack.Case(ci, _, lf,_)::s') when use_match ->
              whrec (lf.(c-1), (Stack.tail ci.ci_npar args) @ s')
          |args, (Stack.Proj (n,m,p,_)::s') when use_match ->
              whrec (Stack.nth args (n+m), s')
          |args, (Stack.Fix (f,s',cst_l)::s'') when use_fix ->
              let x' = Stack.zip sigma (x, args) in
              let out_sk = s' @ (Stack.append_app [|x'|] s'') in
              reduce_and_refold_fix whrec env sigma f out_sk
          |args, (Stack.Cst (const,curr,remains,s',cst_l) :: s'') ->
              let x' = Stack.zip sigma (x, args) in
              begin match remains with
              | [] ->
                  (match const with
                   | Stack.Cst_const const ->
                       (match constant_opt_value_in env const with
                        | None -> fold ()
                        | Some body ->
                            let body = EConstr.of_constr body in
                            whrec
                              (body, s' @ (Stack.append_app [|x'|] s'')))
                   | Stack.Cst_proj p ->
                       let pb = lookup_projection p env in
                       let npars = pb.Declarations.proj_npars in
                       let narg = pb.Declarations.proj_arg in
                       let stack = s' @ (Stack.append_app [|x'|] s'') in
                       match Stack.strip_n_app 0 stack with
                       | None -> assert false
                       | Some (_,arg,s'') ->
                           whrec (arg, Stack.Proj (npars,narg,p,cst_l) :: s''))
              | next :: remains' -> match Stack.strip_n_app (next-curr-1) s'' with
                | None -> fold ()
                | Some (bef,arg,s''') ->
                    whrec
                      (arg,
                       Stack.Cst (const,next,remains',s' @ (Stack.append_app [|x'|] bef),cst_l) :: s''')
              end
          |_, (Stack.App _|Stack.Update _|Stack.Shift _)::_ -> assert false
          |_, _ -> fold ()
        else fold ()

    | CoFix cofix ->
        if CClosure.RedFlags.red_set flags CClosure.RedFlags.fCOFIX then
          match Stack.strip_app stack with
          |args, ((Stack.Case _ |Stack.Proj _)::s') ->
              reduce_and_refold_cofix whrec env sigma cofix stack
          |_ -> fold ()
        else fold ()

    | Rel _ | Var _ | LetIn _ | Proj _ -> fold ()
    | Sort _ | Ind _ | Prod _ -> fold ()
  in
  whrec

(* Drops the Cst_stack *)
let iterate_whd_gen refold flags env sigma s =
  let rec aux t =
    let (hd,sk),_ = whd_state_gen flags env Context.Named.empty sigma (t,Stack.empty) in
    let whd_sk = Stack.map aux sk in
    Stack.zip sigma ~refold (hd,whd_sk)
  in aux s
