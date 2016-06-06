(** This module defines the interpretation of MetaCoq constr
*)

open Declarations

open List
open String

open Pp
open Term
open Termops
open Reductionops
open Environ
open Evarutil
open Evd
open Names
open Closure
open Util
open Evarconv
open Libnames

open Constrs

module Stack = Reductionops.Stack

let reduce_value = Tacred.compute


module MetaCoqNames = struct
  let metaCoq_module_name = "MetaCoq.MetaCoq.MetaCoq"
  let mkConstr e = Constr.mkConstr (metaCoq_module_name ^ "." ^ e)
  let mkBuilder e = ConstrBuilder.from_string (metaCoq_module_name ^ "." ^ e)
  let mkT_lazy = mkConstr "MetaCoq"
  let mkUConstr e = (Constr.mkUConstr (metaCoq_module_name ^ "." ^ e))

  let isConstr e =
    let c = Lazy.force (mkConstr e) in
    eq_constr c

  let mkCase = mkConstr "mkCase"

  let mkelem = mkConstr "elem"
  let mkdyn = mkConstr "dyn"
  let mkDyn = mkConstr "Dyn"

end

let constr_to_string t = string_of_ppcmds (Termops.print_constr t)

module Exceptions = struct

  let mkInternalException = MetaCoqNames.mkConstr

  let mkNullPointer = mkInternalException "NullPointer"
  let mkTermNotGround = mkInternalException "TermNotGround"
  let mkOutOfBounds = mkInternalException "ArrayOutOfBounds"
  let mkWrongTerm = mkInternalException "WrongTerm"
  let mkMissingDependency = mkInternalException "MissingDependency"
  let mkLtacError (s, ppm) =
    let e = mkInternalException "LtacError" in
    let expl = string_of_ppcmds ppm in
    let coqexp = CoqString.to_coq (s ^ ": " ^ expl) in
    mkApp(Lazy.force e, [|coqexp|])

  let mkNotUnifiable a x y =
    let e = mkInternalException "NotUnifiableException" in
    mkApp(Lazy.force e, [|a;x;y|])

  (* HACK: we put Prop as the type of the raise. We can put an evar, but
     what's the point anyway? *)
  let mkRaise e =
    let c = Lazy.force (MetaCoqNames.mkConstr "raise") in
    let a = Lazy.force (MetaCoqNames.mkConstr e) in
    mkApp(c, [|mkProp; a|])

  let error_stuck t = "Cannot reduce term, perhaps an opaque definition? " ^ constr_to_string t
  let error_param = "Parameter appears in returned value"
  let error_abs x = "Cannot abstract non variable " ^ (constr_to_string x)
  let error_abs_env = "Cannot abstract variable in a context depending on it"
  let error_abs_type = "Variable is appearing in the returning type"
  let error_abs_ref = "Variable is appearing in type of reference"
  let error_abs_let = "Trying to let-abstract a variable without definition"
  let error_array_zero = "Array must have non-zero length"
  let unknown_reduction_strategy = "Unknown reduction strategy"

  let block = Errors.error
end

module ReductionStrategy = struct
  let isRedNone c = MetaCoqNames.isConstr "RedNone" c
  let isRedSimpl c = MetaCoqNames.isConstr "RedSimpl" c
  let isRedWhd c = MetaCoqNames.isConstr "RedWhd" c
  let isRedOneStep c = MetaCoqNames.isConstr "RedOneStep" c
  let isReduce c = MetaCoqNames.isConstr "reduce" c

  let has_definition ts env t =
    if isVar t then
      let var = destVar t in
      if not (Closure.is_transparent_variable ts var) then
        false
      else
        let (_, v,_) = Environ.lookup_named var env in
        match v with
        | Some _ -> true
        | _ -> false
    else if isRel t then
      let n = destRel t in
      let (_,v,_) = Environ.lookup_rel n env in
      match v with
      | Some _ -> true
      | _ -> false
    else if isConst t then
      let (c, _) = destConst t in
      Closure.is_transparent_constant ts c && Environ.evaluable_constant c env
    else
      false

  let get_definition env t =
    if isVar t then
      let var = destVar t in
      let (_, v,_) = Environ.lookup_named var env in
      match v with
      | Some c -> c
      | _ -> Errors.anomaly (Pp.str "get_definition for var didn't have definition!")
    else if isRel t then
      let n = destRel t in
      let (_,v,_) = Environ.lookup_rel n env in
      match v with
      | Some v -> (Vars.lift n) v
      | _ -> Errors.anomaly (Pp.str "get_definition for rel didn't have definition!")
    else if isConst t then
      let c = destConst t in
      let (d,_) = Environ.constant_value env c in
      d
    else
      Errors.anomaly (Pp.str "get_definition didn't have definition!")

  let try_unfolding ts env t =
    if has_definition ts env t then
      get_definition env t
    else
      t

  let one_step env sigma c =
    let ts = Conv_oracle.get_transp_state (Environ.oracle env) in
    let h, args = decompose_app c in
    let h = whd_evar sigma h in
    let r =
      match kind_of_term h with
      | Lambda (_, _, trm) when args <> [] ->
          (Vars.subst1 (List.hd args) trm, List.tl args)
      | LetIn (_, trm, _, body) -> (Vars.subst1 trm body, args)
      | Var _ | Rel _ | Const _ -> (try_unfolding ts env h, args)
      | _ -> h, args
    in applist r

  let reduce sigma env strategy c =
    if isRedNone strategy then
      c
    else if isRedSimpl strategy then
      Tacred.simpl env sigma c
    else if isRedWhd strategy then
      whd_betadeltaiota env sigma c
    else if isRedOneStep strategy then
      one_step env sigma c
    else
      Exceptions.block Exceptions.unknown_reduction_strategy

end

module UnificationStrategy = struct
  let isUniNormal e = MetaCoqNames.isConstr "UniNormal" e
  let isUniMatch e = MetaCoqNames.isConstr "UniMatch" e
  let isUniCoq e = MetaCoqNames.isConstr "UniCoq" e

  let find_pbs sigma evars =
    let (_, pbs) = extract_all_conv_pbs sigma in
    List.filter (fun (_,_,c1,c2) ->
      List.exists (fun e ->
        Termops.occur_term e c1 || Termops.occur_term e c2) evars) pbs

  let unify sigma env strategy t1 t2 =
    let open Evarsolve in
    let ts = Conv_oracle.get_transp_state (Environ.oracle env) in
    if isUniNormal strategy then
      let r = Munify.unify_evar_conv ts env sigma Reduction.CUMUL t1 t2 in
      match r with
      | Success sigma -> Some sigma
      | _ -> None
    else if isUniMatch strategy then
      let evars = Evar.Map.domain (Evd.undefined_map sigma) in
      let r = Munify.unify_match evars ts env sigma Reduction.CUMUL t1 t2 in
      match r with
      | Success sigma -> Some sigma
      | _ -> None
    else if isUniCoq strategy then
      try
        let sigma = the_conv_x ~ts env t2 t1 sigma in
        Some (consider_remaining_unif_problems env sigma)
      with _ -> None
    else
      Exceptions.block "Unknown unification strategy"

end

module Pattern = struct
  open ConstrBuilder

  let baseB = MetaCoqNames.mkBuilder "pbase"
  let teleB = MetaCoqNames.mkBuilder "ptele"

  exception NotAPattern

  let open_pattern env sigma p =
    let rec op sigma p evars =
      let (c, args) = whd_betadeltaiota_stack env sigma p in
      if equal baseB c then
        (sigma, evars, List.nth args 4, List.nth args 5)
      else if equal teleB c then
        begin
          let ty = List.nth args 4 in
          let func = List.nth args 5 in
          let (sigma, evar) =
            if Term.isSort ty && ty <> mkProp then
              let (sigma, (evar, _)) = Evarutil.new_type_evar env sigma Evd.UnivRigid in
              (sigma, evar)
            else
              Evarutil.new_evar env sigma ty
          in
          let evars = Evar.Set.add (fst (destEvar evar)) evars in
          op sigma (mkApp (func, [|evar|])) evars
        end
      else
        raise NotAPattern
    in
    op sigma p (Evar.Set.empty)

end


module GrowingArray = struct
  type 'a t = 'a array ref * 'a * int ref

  let make i t = (ref (Array.make i t), t, ref 0)
  let length g = let (_, _, i) = g in !i

  exception OutOfBounds

  let get g i =
    let (a, _, l) = g in
    if i < !l then
      Array.get !a i
    else
      raise OutOfBounds

  let set g i =
    let (a, _, l) = g in
    if i < !l then
      Array.set !a i
    else
      raise OutOfBounds

  let add g t =
    let (a, e, i) = g in
    begin
      if Array.length !a <= !i then
        a := Array.append !a (Array.make (Array.length !a / 2) e)
      else
        ()
    end;
    Array.set !a !i t;
    i := !i+1

end

(*
   OUTDATED EXPLANATION: instead of storing one cell references we store arrays

   The context of the references is never changed, except when a new
   parameter is inserted using (nu x, t). Then, when exiting the context
   of nu x, we need to make sure that no reference refers to x. For this
   reason, we keep a list of references to lists enumerating the references
   pointing to x. To make it clear, the argument 'undo' used by many of the
   functions has the following shape:

   [ r1 ; r2 ; ... ; rn ]

   where r1 corresponds to the innermost nu executed, and rn to the outermost.
   Each ri is a reference to a list [x1 ; ...; xim] of im references pointing
   to values that refer to the binder noted by i.

   When leaving the scope of x, the execution makes sure every reference listed
   in the list referred on the top of the undo list is invalidated, that is,
   pointing to "null".
*)
module ArrayRefFactory =
struct
  let mkArrRef= Constr.mkConstr (MetaCoqNames.metaCoq_module_name ^ ".carray")

  let isArrRef =  Constr.isConstr mkArrRef

  let to_coq a i n =
    Term.mkApp (Lazy.force mkArrRef, [|a ; CoqN.to_coq i; n|])

  let from_coq (env, evd as ctx) c =
    let c = whd_betadeltaiota env evd c in
    if isApp c && isArrRef (fst (destApp c)) then
      CoqN.from_coq ctx (snd (destApp c)).(1)
    else
      Exceptions.block "Not a reference"

end

module ArrayRefs = struct

  let init () = GrowingArray.make 4 ((None, 0), [||])

  let bag = ref (init ())

  let clean () =
    bag := init ()

  let get_parameters params t = Int.Set.filter (fun i -> i <= params) (free_rels t)

  let check_context undo index i arr =
    match arr.(i) with
    | Some (c', _) ->
        let level = List.length undo in
        (* check if the db index points to the nu context *)
        let params = get_parameters level c' in
        Int.Set.iter (fun k ->
          let rl = List.nth undo (k -1) in
          rl := ((index, i) :: !rl) (* mark this location as 'dirty' *)
        ) params
    | _ -> ()


  (* A, x : A |-
     a <- make_array (Rel 2) 5 (Rel 1); // 5 copies of x
     // a is equal to [| (0, Rel 2), (0, Rel 1), ..., (0, Rel 1) |]
     // where 0 is the level
     nu y : A,
     // now the context is A, x : A, y : A
     // therefore the level is now 1
     let _ := array_get A a 0;
     // A is Rel 3 now, so in order to compare the type with the type of the array
     // we need to lift by 1 (level - l), where l is the level of the type
     array_set A a 0 y
  *)
  let new_array evd sigma undo ty n c =
    let level = List.length undo in
    let size = CoqN.from_coq (evd, sigma) n in
    let arr = Array.make size (Some (c, level)) in
    let index = GrowingArray.length !bag in
    let params = get_parameters level ty in
    Int.Set.iter (fun k ->
      let rl = List.nth undo (k -1) in
      rl := ((index, -1) :: !rl) (* mark this location as 'dirty' *)
    ) params;
    GrowingArray.add !bag ((Some ty, level), arr);
    Array.iteri (fun i t -> check_context undo index i arr) arr;
    ArrayRefFactory.to_coq ty index n

  exception NullPointerException
  exception OutOfBoundsException
  exception WrongTypeException
  exception WrongIndexException

  let get env evd undo i ty k =
    let level = List.length undo in
    let index = ArrayRefFactory.from_coq (env, evd) i in
    let arri = CoqN.from_coq (env, evd) k in
    try
      let ((aty, al), v) = GrowingArray.get !bag index in
      match aty, v.(arri) with
      | None,  _ -> raise WrongIndexException
      | _, None -> raise NullPointerException
      | Some aty, Some (c, l) ->
          try
            let aty = Vars.lift (level - al) aty in
            let evd = the_conv_x env aty ty evd in
            (evd, Vars.lift (level - l) c)
          with _ -> raise WrongTypeException
    with Invalid_argument _ -> raise OutOfBoundsException
       | GrowingArray.OutOfBounds -> raise WrongIndexException

  (* HACK SLOW *)
  let remove_all undo index k =
    List.iter (fun rl ->
      rl := List.filter (fun i -> i <> (index, k)) !rl) undo

  let set env evd undo i k ty c =
    let level = List.length undo in
    let index = ArrayRefFactory.from_coq (env, evd) i in
    let arri = CoqN.from_coq (env, evd) k in
    remove_all undo index arri;
    try
      let ((aty, al), v) = GrowingArray.get !bag index in
      match aty with
      | Some aty ->
          let aty = Vars.lift (level - al) aty in
          let evd = the_conv_x env aty ty evd in
          v.(arri) <- Some (c, level);
          check_context undo index arri v;
          evd
      | None -> raise WrongTypeException
    with Invalid_argument _ -> raise OutOfBoundsException
       | GrowingArray.OutOfBounds -> raise WrongIndexException
       | _ -> raise WrongTypeException

  let invalidate (index, k) =
    let ((ty, i), v) = GrowingArray.get !bag index in
    if k < 0 then
      GrowingArray.set !bag index ((None, i), v)
    else
      v.(k) <- None

end

module ExistentialSet = Evar.Set

type elem = (evar_map * ExistentialSet.t * constr)

type data =
  | Val of elem
  | Err of elem

let rec (>>=) v g =
  match v with
  | Val v' -> g v'
  | Err _ -> v

let return s es t = Val (s, es, t)

let fail s es t = Err (s, es, t)

let print env sigma s = Printf.printf "[DEBUG] %s\n"
                          (CoqString.from_coq (env, sigma) s)

exception AbstractingArrayType

let mysubstn t n c =
  let rec substrec in_arr depth c = match kind_of_term c with
    | Rel k    ->
        if k<=depth then c
        else if k = depth+n then
          Vars.lift depth t
        else mkRel (k+1)
    | _ -> map_constr_with_binders succ (substrec in_arr) depth c in
  substrec false 0 c

(* checks that no variable in env to the right of i (that is, smaller
   to i) depends on i. *)
let noccurn_env env i =
  let rec noc n =
    if n = 1 then true
    else
      let (_, t, a) = Environ.lookup_rel (i-n+1) env in
      Vars.noccurn (n-1) a
      && (if t = None then true else Vars.noccurn (n-1) (Option.get t))
      && noc (n-1)
  in noc i

let name_occurn_env env n =
  let ids = Environ.fold_named_context_reverse
              (fun s (n', _, _) -> Id.Set.add n' s)
              ~init:Id.Set.empty env in (* compute set of ids in env *)
  let ids = Id.Set.remove n ids in (* remove n *)
  let ids = Environ.really_needed env ids in (* and compute closure of ids *)
  Id.Set.mem n ids (* to finally check if n is in it *)


let dest_Case (env, sigma) t_type t =
  let nil = Constr.mkConstr "Coq.Init.Datatypes.nil" in
  let cons = Constr.mkConstr "Coq.Init.Datatypes.cons" in
  let mkCase = Lazy.force MetaCoqNames.mkCase in
  let dyn = Lazy.force MetaCoqNames.mkdyn in
  let cDyn = Lazy.force MetaCoqNames.mkDyn in
  try
    let t = whd_betadeltaiota env sigma t in
    let (info, return_type, discriminant, branches) = Term.destCase t in
    let branch_dyns = Array.fold_left (
      fun l t ->
        let dyn_type = Retyping.get_type_of env sigma t in
        Term.applist (Lazy.force cons, [dyn; Term.applist (cDyn, [dyn_type; t]); l])
    ) (Lazy.force nil) branches in
    let ind_type = Retyping.get_type_of env sigma discriminant in
    let return_type_type = Retyping.get_type_of env sigma return_type in
    (sigma, (Term.applist(mkCase,
                          [ind_type; discriminant; t_type;
                           Term.applist(cDyn, [return_type_type; return_type]);
                           branch_dyns
                          ])
            )
    )
  with
  | Not_found ->
      Exceptions.block "Something specific went wrong. TODO: find out what!"
  | Term.DestKO ->
      Exceptions.block "This is not a case construct."
  | _ ->
      Exceptions.block "Something not so specific went wrong."

let make_Case (env, sigma) case =
  let elem = Lazy.force MetaCoqNames.mkelem in
  let cDyn = Lazy.force MetaCoqNames.mkDyn in
  let case_ind = Lazy.force (MetaCoqNames.mkConstr "case_ind") in
  let case_val = Lazy.force (MetaCoqNames.mkConstr "case_val") in
  let case_return = Lazy.force (MetaCoqNames.mkConstr "case_return") in
  let case_branches = Lazy.force (MetaCoqNames.mkConstr "case_branches") in
  let repr_ind = Term.applist(case_ind, [case]) in
  let repr_val = Term.applist(case_val, [case]) in
  let repr_val_red = whd_betadeltaiota env sigma repr_val in
  let repr_return = Term.applist(case_return, [case]) in
  let repr_return_unpack = Term.applist(elem, [repr_return]) in
  let repr_return_red = whd_betadeltaiota env sigma repr_return_unpack in
  let repr_branches = Term.applist(case_branches, [case]) in
  let repr_branches_list = CoqList.from_coq (env, sigma) repr_branches in
  let repr_branches_dyns =
    List.map (fun t -> Term.applist(elem, [t])) repr_branches_list in
  let repr_branches_red =
    List.map (fun t -> whd_betadeltaiota env sigma t) repr_branches_dyns in
  let t_type, l = Term.decompose_app (whd_betadeltaiota env sigma repr_ind) in
  if Term.isInd t_type then
    match Term.kind_of_term t_type with
    | Term.Ind ((mind, ind_i), _) ->
        let case_info = Inductiveops.make_case_info env (mind, ind_i)
                          Term.LetPatternStyle in
        let match_term = Term.mkCase (case_info, repr_return_red, repr_val_red,
                                      Array.of_list (repr_branches_red)) in
        let match_type = Retyping.get_type_of env sigma match_term in
        (sigma, Term.applist(cDyn, [match_type;  match_term]))
    | _ -> assert false
  else
    Exceptions.block "case_type is not an inductive type"


let get_Constrs (env, sigma) t =
  let t_type, args = Term.decompose_app (whd_betadeltaiota env sigma t) in
  if Term.isInd t_type then
    match Term.kind_of_term t_type with
    | Term.Ind ((mind, ind_i), _) ->
        let mbody = Environ.lookup_mind mind env in
        let ind = Array.get (mbody.mind_packets) ind_i in
        let dyn = Lazy.force MetaCoqNames.mkdyn in
        let cDyn = Lazy.force MetaCoqNames.mkDyn in
        let l = Array.fold_right
                  (fun i l ->
                     let constr = Names.ith_constructor_of_inductive (mind, ind_i) i in
                     let coq_constr = Term.applist (Term.mkConstruct constr, args) in
                     let ty = Retyping.get_type_of env sigma coq_constr in
                     let dyn_constr = Term.applist (cDyn, [ty; coq_constr]) in
                     CoqList.makeCons dyn dyn_constr l
                  )
                  (* this is just a dirty hack to get the indices of constructors *)
                  (Array.mapi (fun i t -> i+1) ind.mind_consnames)
                  (CoqList.makeNil dyn)
        in
        (sigma, l)
    | _ -> assert false
  else
    Exceptions.block "The argument of Mconstrs is not an inductive type"

module Hypotheses = struct

  let ahyp_constr = MetaCoqNames.mkBuilder "ahyp"

  let mkAHyp ty n t =
    let t = match t with
      | None -> CoqOption.mkNone ty
      | Some t -> CoqOption.mkSome ty t
    in ConstrBuilder.build_app ahyp_constr [|ty; n; t|]

  let mkHypType = MetaCoqNames.mkConstr "Hyp"


  let cons_hyp ty n t renv sigma env =
    let hyptype = Lazy.force mkHypType in
    let hyp = mkAHyp ty n t in
    (sigma, CoqList.makeCons hyptype hyp renv)

  let from_coq (env, sigma as ctx) c =
    let fvar = fun c ->
      if Term.isVar c || isRel c then c
      else Exceptions.block "Not a variable in hypothesis"
    in
    let fdecl = fun d -> CoqOption.from_coq ctx d in
    let args = ConstrBuilder.from_coq ahyp_constr ctx c in
    (fvar args.(1), fdecl args.(2), args.(0))

  let from_coq_list (env, sigma as ctx) =
    CoqList.from_coq_conv ctx (from_coq ctx)

end

(* It replaces each ii by ci in l = [(i1,c1) ... (in, cn)] in c.
   It throws Not_found if there is a variable not in l *)
let multi_subst l c =
  let rec substrec depth c = match kind_of_term c with
    | Rel k    ->
        if k<=depth then c
        else
          List.assoc (k - depth) l
    | _ -> map_constr_with_binders succ substrec depth c in
  substrec 0 c

(* check if x \not\in FV(t) union FV(env) *)
let check_dependencies env x t =
  if isRel x then
    let rel = destRel x in
    Vars.noccurn rel t && noccurn_env env rel
  else if isVar x then
    let name = destVar x in
    not (Termops.occur_var env name t) && not (name_occurn_env env name)
  else
    failwith "check_dependencies should not be called with not a var or rel"


(** Abstract *)
type abs = AbsProd | AbsFun | AbsLet | AbsFix

(* n is only for fixpoint *)
let abs case (env, sigma, metas) a p x y n : data =
  (*  let x = whdbetadeltaiota env sigma x in *) (* for let-ins is problemtaic *)
  (* check if the type p does not depend of x, and that no variable
     created after x depends on it.  otherwise, we will have to
     substitute the context, which is impossible *)
  if isRel x || isVar x then
    if check_dependencies env x p then
      if isRel x then
        let rel = destRel x in
        try
          let (name, ot, ty) = lookup_rel rel env in
          let y' = mysubstn (mkRel 1) rel y in
          let t =
            match case, ot with
            | AbsProd, _ -> Term.mkProd (name, a, y')
            | AbsFun, _ -> Term.mkLambda (name, a, y')
            | AbsLet, Some t -> Term.mkLetIn (name, t, ty, y')
            | AbsLet, None -> Exceptions.block Exceptions.error_abs_let
            | AbsFix, _ -> (* TODO: check enough products *)
                Term.mkFix (([|n|], 0), ([|name|], [|ty|], [|y'|]))
          in
          return sigma metas t
        with AbstractingArrayType ->
          Exceptions.block Exceptions.error_abs_ref
      else
        let name = destVar x in
        let y' = Vars.subst_vars [name] y in
        let t =
          match case with
          | AbsProd -> Term.mkProd (Name name, a, y')
          | AbsFun -> Term.mkLambda (Name name, a, y')
          | AbsLet ->
              let (_, ot, ty) = lookup_named name env in
              begin
                match ot with
                | Some t -> Term.mkLetIn (Name name, t, ty, y')
                | None -> Exceptions.block Exceptions.error_abs_let
              end
          | AbsFix ->
              (* TODO: check enough products *)
              let (_, _, ty) = lookup_named name env in
              Term.mkFix (([|n|], 0), ([|Name name|], [|ty|], [|y'|]))
        in
        return sigma metas t
    else
      Exceptions.block Exceptions.error_abs_env
  else
    Exceptions.block (Exceptions.error_abs x)

exception MissingDep
let cvar (env, sigma, metas) ty hyp =
  let hyp = Hypotheses.from_coq_list (env, sigma) hyp in
  let check_vars e t vars =
    Idset.subset (Termops.collect_vars t) vars &&
    if Option.has_some e then
      Idset.subset (Termops.collect_vars (Option.get e)) vars
    else true
  in
  let b, (_, _, subs, env') =
    try
      true, List.fold_right (fun (i, e, t) (avoid, avoids, subs, env') ->
        let t = Reductionops.nf_evar sigma t in
        let e = Option.map (Reductionops.nf_evar sigma) e in
        if isRel i then
          let n = destRel i in
          let na, _, _ = List.nth (rel_context env) (n-1) in
          let id = Namegen.next_name_away na avoid in
          let e = try Option.map (multi_subst subs) e with Not_found -> Exceptions.block "Not well-formed hypotheses 1" in
          let t = try multi_subst subs t with Not_found -> Exceptions.block "Not well-formed hypotheses 2" in
          let b = check_vars e t avoids in
          let d = (id, e, t) in
          if b then
            (id::avoid, Idset.add id avoids, (n, mkVar id) :: subs, push_named d env')
          else
            raise MissingDep
        else
          let id = destVar i in
          if check_vars e t avoids then
            (id::avoid, Idset.add id avoids, subs, push_named (id, e, t) env')
          else
            raise MissingDep
      ) hyp ([], Idset.empty, [], empty_env)
    with MissingDep -> false, ([], Idset.empty, [], empty_env)
  in
  if not b then
    fail sigma metas (Lazy.force Exceptions.mkMissingDependency)
  else
    let vars = List.map (fun (v, _, _)->v) hyp in
    try
      if List.distinct vars then
        let evi = Evd.make_evar (Environ.named_context_val env') (multi_subst subs ty) in
        let (sigma, e) = Evarutil.new_pure_evar_full sigma evi in
        return sigma metas (mkEvar (e, Array.of_list vars))
      else
        Exceptions.block "Duplicated variable in hypotheses"
    with Not_found ->
      Exceptions.block "Hypothesis not found"

(* if [f] is a function, we use its variable to get the name, otherwise we
   apply [f] to a fresh new variable. *)
let get_func_name env sigma s f =
  let s = CoqString.from_coq (env, sigma) s in
  let s = Names.Id.of_string s in
  let s = Namegen.next_ident_away_in_goal s (ids_of_context env) in
  Names.Name s, Term.mkApp(Vars.lift 1 f, [|Term.mkRel 1|])

let get_name (env, sigma) t =
  let t = whd_betadeltaiota env sigma t in
  let name =
    if isVar t then Some (Name (destVar t))
    else if isRel t then
      let (n, _, _) = lookup_rel (destRel t) env in Some n
    else if isLambda t then
      let (n, _, _) = destLambda t in Some n
    else if isProd t then
      let (n, _, _) = destProd t in Some n
    else if isLetIn t then
      let (n, _, _, _) = destLetIn t in Some n
    else
      None
  in
  match name with
  | Some (Name i) -> Some (CoqString.to_coq (Names.Id.to_string i))
  | Some _ -> Some (CoqString.to_coq "x")
  | _ -> None

let clean = List.iter ArrayRefs.invalidate

(* return the reflected hash of a term *)
let hash (env, _, sigma, undo, _) c size =
  let size = CoqN.from_coq (env, sigma) size in
  let nus = List.length undo in
  let rec upd depth t =
    match kind_of_term t with
    | Rel k ->
        if depth < k then
          begin
            if k > depth + nus then
              mkRel (k - nus)
            else
              mkRel (k + nus - (2 * (k -1)))
          end
        else
          t
    | _ -> map_constr_with_binders succ upd depth t
  in
  let h = Term.hash_constr (upd 0 c) in
  CoqN.to_coq (Pervasives.abs (h mod size))

(* reflects the hypotheses in [env] in a list of [ahyp] *)
let build_hypotheses sigma env =
  let renv = List.mapi (fun i (_, t, ty)->(mkRel (i+1), t, ty))
               (rel_context env)
             @ (List.map (fun (n, t, ty)->(mkVar n, t, ty))
                  (named_context env)) in
  (* the list is reversed: [H : x > 0, x : nat] *)
  let rec build renv =
    match renv with
    | [] -> let ty = Lazy.force Hypotheses.mkHypType in
        (sigma, CoqList.makeNil ty)
    | (n, t, ty) :: renv ->
        let (sigma, r) = build renv in
        Hypotheses.cons_hyp ty n t r sigma env
  in
  build renv

let env_without sigma env renv x =
  let name_env = named_context env in
  let rel_env = rel_context env in
  let env = Environ.reset_context env in
  if isVar x then
    let nx = destVar x in
    let env = Context.fold_named_context (fun (n, _, _ as decl) e -> if n = nx then e else push_named decl e)
                name_env ~init:(env:env) in
    let env = push_rel_context rel_env env in
    env, build_hypotheses sigma env
  else
    let i = destRel x in
    let _, env = Context.fold_rel_context (fun (n, ot, ty as decl) (j,e) ->
      if j > i then (j-1, push_rel decl e)
      else if j = i then (j-1, e)
      else (j-1, push_rel (n, Option.map Termops.pop ot, Termops.pop ty) e))
      rel_env ~init:(List.length rel_env,env) in
    let env = push_named_context name_env env in
    env, build_hypotheses sigma env

let rec run' (env, renv, sigma, undo, metas as ctxt) t =
  let (t,sk as appr) = Reductionops.whd_nored_state sigma (t, []) in
  let (h, args) = Reductionops.whd_betadeltaiota_nolet_state env sigma appr in
  let nth = Stack.nth args in
  if Term.isLetIn h then
    let (_, b, _, t) = Term.destLetIn h in
    let (h, args') = Term.decompose_appvect b in
    if ReductionStrategy.isReduce h && Array.length args' = 3 then
      let b = ReductionStrategy.reduce sigma env (Array.get args' 0) (Array.get args' 2) in
      run' ctxt (Stack.zip (Vars.subst1 b t, args))
    else
      run' ctxt (Stack.zip (Vars.subst1 b t, args))
  else
    let constr c =
      if Term.isConstruct c then
        let ((m, ix), _) = Term.destConstruct c in
        if Names.eq_ind m (fst (Term.destInd (Lazy.force MetaCoqNames.mkT_lazy))) then
          ix
        else
          Exceptions.block (Exceptions.error_stuck c)
      else
        Exceptions.block (Exceptions.error_stuck c)
    in
    match constr h with
    | 1 -> (* ret *)
        return sigma metas (nth 1)

    | 2 -> (* bind *)
        run' ctxt (nth 2) >>= fun (sigma', metas, v) ->
        let t' = mkApp(nth 3, [|v|]) in
        run' (env, renv, sigma', undo, metas) t'

    | 3 -> (* try *)
        begin
          match run' ctxt (nth 1) with
          | Val (sigma', metas, v) -> return sigma' metas v
          | Err (sigma', metas, i) ->
              let t' = mkApp(nth 2, [|i|]) in
              run' (env, renv, sigma', undo, metas) t'
        end

    | 4 -> (* raise *)
        fail sigma metas (nth 1)

    | 5 -> (* fix1 *)
        let a, b, s, i, f, x = nth 0, nth 1, nth 2, nth 3, nth 4, nth 5 in
        run_fix ctxt h [|a|] b s i f [|x|]

    | 6 -> (* fix 2 *)
        let a1, a2, b, s, i, f, x1, x2 =
          nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7 in
        run_fix ctxt h [|a1; a2|] b s i f [|x1; x2|]

    | 7 -> (* fix 3 *)
        let a1, a2, a3, b, s, i, f, x1, x2, x3 =
          nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7, nth 8, nth 9 in
        run_fix ctxt h [|a1; a2; a3|] b s i f [|x1; x2; x3|]

    | 8 -> (* fix 4 *)
        let a1, a2, a3, a4, b, s, i, f, x1, x2, x3, x4 =
          nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7, nth 8, nth 9, nth 10, nth 11 in
        run_fix ctxt h [|a1; a2; a3; a4|] b s i f [|x1; x2; x3; x4|]

    | 9 -> (* fix 5 *)
        let a1, a2, a3, a4, a5, b, s, i, f, x1, x2, x3, x4, x5 =
          nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7, nth 8, nth 9, nth 10, nth 11, nth 12, nth 13 in
        run_fix ctxt h [|a1; a2; a3; a4; a5|] b s i f [|x1; x2; x3; x4; x5|]

    | 10 -> (* is_var *)
        let e = whd_betadeltaiota env sigma (nth 1) in
        if isRel e || isVar e then
          return sigma metas CoqBool.mkTrue
        else
          return sigma metas CoqBool.mkFalse

    | 11 -> (* nu *)
        let a, s, ot, f = nth 0, nth 2, nth 3, nth 4 in
        let x, fx = get_func_name env sigma s f in
        let ot = CoqOption.from_coq (env, sigma) ot in
        let renv = Vars.lift 1 renv in
        let ur = ref [] in
        let env = push_rel (x, ot, a) env in
        let (sigma, renv) = Hypotheses.cons_hyp a (mkRel 1) ot renv sigma env in
        begin
          match run' (env, renv, sigma, (ur :: undo), metas) fx with
          | Val (sigma', metas, e) ->
              clean !ur;
              if Int.Set.mem 1 (free_rels e) then
                Exceptions.block Exceptions.error_param
              else
                return sigma' metas (pop e)
          | Err (sigma', metas, e) ->
              clean !ur;
              if Int.Set.mem 1 (free_rels e) then
                Exceptions.block Exceptions.error_param
              else
                fail sigma' metas (pop e)
        end

    | 12 -> (* abs *)
        let a, p, x, y = nth 0, nth 1, nth 2, nth 3 in
        abs AbsFun (env, sigma, metas) a p x y 0

    | 13 -> (* abs_let *)
        let a, p, x, y = nth 0, nth 1, nth 2, nth 3 in
        abs AbsLet (env, sigma, metas) a p x y 0

    | 14 -> (* abs_prod *)
        let a, p, x, y = nth 0, nth 1, nth 2, nth 3 in
        abs AbsProd (env, sigma, metas) a p x y 0

    | 15 -> (* abs_fix *)
        let a, f, t, n = nth 0, nth 1, nth 2, nth 3 in
        let n = CoqN.from_coq (env, sigma) n in
        (* HACK: put mkProp as returning type *)
        abs AbsFix (env, sigma, metas) a mkProp f t n

    | 16 -> (* get_binder_name *)
        let t = nth 1 in
        let s = get_name (env, sigma) t in
        begin
          match s with
          | Some s -> return sigma metas s
          | None -> fail sigma metas (Lazy.force Exceptions.mkWrongTerm)
        end

    | 17 -> (* remove *)
        let x, t = nth 2, nth 3 in
        let x = whd_betadeltaiota env sigma x in
        if isVar x || isRel x then
          if check_dependencies env x t then
            (* if it's a rel we need to update the indices in t, since there is one element less in the context *)
            let t = if isRel x then Vars.liftn (-1) (destRel x) t else t in
            let env, (sigma, renv) = env_without sigma env renv x in
            run' (env, renv, sigma, undo, metas) t >>= fun (sigma, metas, v)->
            return sigma metas (if isRel x then Vars.liftn (+1) (destRel x) v else v)
          else
            Exceptions.block "Environment or term depends on variable"
        else
          Exceptions.block "Not a variable"

    | 18 -> (* evar *)
        let t = nth 0 in
        let (sigma', ev) = Evarutil.new_evar env sigma t in
        return sigma' (ExistentialSet.add (fst (destEvar ev)) metas) ev

    | 19 -> (* Cevar *)
        let ty, hyp = nth 0, nth 1 in
        cvar (env, sigma, metas) ty hyp

    | 20 -> (* is_evar *)
        let e = whd_betadeltaiota env sigma (nth 1) in
        if isEvar e then
          return sigma metas CoqBool.mkTrue
        else
          return sigma metas CoqBool.mkFalse

    | 21 -> (* hash *)
        return sigma metas (hash ctxt (nth 1) (nth 2))

    | 22 -> (* solve_typeclasses *)
        let evd' = Typeclasses.resolve_typeclasses ~fail:false env sigma in
        return evd' metas (Lazy.force CoqUnit.mkTT)

    | 23 -> (* new_array *)
        let ty, n, c = nth 0, nth 1, nth 2 in
        let a = ArrayRefs.new_array env sigma undo ty n c in
        return sigma metas a

    | 24 -> (* get *)
        let ty, a, i = nth 0, nth 1, nth 2 in
        begin
          try
            let (sigma, e) = ArrayRefs.get env sigma undo a ty i in
            return sigma metas e
          with ArrayRefs.NullPointerException ->
            let e = Lazy.force Exceptions.mkNullPointer in
            fail sigma metas e
             | ArrayRefs.OutOfBoundsException ->
                 let e = Lazy.force Exceptions.mkOutOfBounds in
                 fail sigma metas e
             | ArrayRefs.WrongTypeException ->
                 Exceptions.block "Wrong type!"
             | ArrayRefs.WrongIndexException ->
                 Exceptions.block "Wrong array!"
        end

    | 25 -> (* set *)
        let ty, a, i, c = nth 0, nth 1, nth 2, nth 3 in
        begin
          try
            let sigma = ArrayRefs.set env sigma undo a i ty c in
            return sigma metas (Lazy.force CoqUnit.mkTT)
          with ArrayRefs.OutOfBoundsException ->
            let e = Lazy.force Exceptions.mkOutOfBounds in
            fail sigma metas e
             | ArrayRefs.WrongTypeException ->
                 Exceptions.block "Wrong type!"
             | ArrayRefs.WrongIndexException ->
                 Exceptions.block "Wrong array!"
        end

    | 26 -> (* print *)
        let s = nth 0 in
        print env sigma s;
        return sigma metas (Lazy.force CoqUnit.mkTT)

    | 27 -> (* pretty_print *)
        let t = nth 1 in
        let t = nf_evar sigma t in
        let s = string_of_ppcmds (Termops.print_constr_env env t) in
        return sigma metas (CoqString.to_coq s)

    | 28 -> (* hypotheses *)
        return sigma metas renv

    | 29 -> (* dest case *)
        let t_type = nth 0 in
        let t = nth 1 in
        let (sigma', case) = dest_Case (env, sigma) t_type t in
        return sigma' metas case

    | 30 -> (* get constrs *)
        let t = nth 1 in
        let (sigma', constrs) = get_Constrs (env, sigma) t in
        return sigma' metas constrs

    | 31 -> (* make case *)
        let case = nth 0 in
        let (sigma', case) = make_Case (env, sigma) case in
        return sigma' metas case

    | 32 -> (* munify *)
        let a, x, y, uni = nth 0, nth 1, nth 2, nth 3 in
        let feqT = CoqEq.mkAppEq a x y in
        begin
          let r = UnificationStrategy.unify sigma env uni x y in
          match r with
          | Some sigma ->
              let feq = CoqEq.mkAppEqRefl a x in
              let someFeq = CoqOption.mkSome feqT feq in
              return sigma metas someFeq
          | _ ->
              let none = CoqOption.mkNone feqT in
              return sigma metas none
        end

    | 33 -> (* call_ltac *)
        let concl, name, args = nth 0, nth 1, nth 2 in
        let name, args = CoqString.from_coq (env, sigma) name, CoqList.from_coq (env, sigma) args in
        (* let name = Lib.make_kn (Names.Id.of_string name) in *)
        (* let tac = Tacenv.interp_ml_tactic name in *)
        let tac =
          let rec aux = function
            | [] -> raise Not_found
            | (k, _)::_ when String.equal (Names.KerName.to_string k) name ->
                let args =
                  let aux x =
                    let x = CoqSig.from_coq (env, sigma) x in
                    let x = Detyping.detype false [] env sigma x in
                    Tacexpr.ConstrMayEval (Genredexpr.ConstrTerm (x (*Glob_term.GVar (Loc.ghost, Term.destVar x*), None))
                  in
                  List.map aux args
                in
                Tacexpr.TacArg (Loc.ghost, (Tacexpr.TacCall (Loc.ghost, Misctypes.ArgArg (Loc.ghost, k), args)))
            | (k, _)::xs -> aux xs
          in
          aux (KNmap.bindings (Tacenv.ltac_entries ()))
        in
        begin
          try
            let (c, sigma) = Pfedit.refine_by_tactic env sigma concl (Tacinterp.eval_tactic tac) in
            let evars = List.filter (fun (i, _)->Evd.is_undefined sigma i) (Evd.evar_list c) in
            let cDyn = Lazy.force MetaCoqNames.mkDyn in
            let dyn = Lazy.force MetaCoqNames.mkdyn in
            let evars = CoqList.to_coq (Lazy.force MetaCoqNames.mkdyn) (fun e->
              mkApp(cDyn, [|Evd.existential_type sigma e; mkEvar e|])) evars in
            return sigma metas (CoqPair.mkPair concl (CoqList.makeType dyn) c evars)
          with Errors.UserError(s,ppm) ->
            fail sigma metas (Exceptions.mkLtacError (s, ppm))
        end
    (* Tac (sigma, metas, Tacinterp.eval_tactic tac, fun v -> Val v) *)

    | 34 -> (* list_ltac *)
        let aux k _ = Pp.msg_info (Pp.str (Names.KerName.to_string k)) in
        KNmap.iter aux (Tacenv.ltac_entries ());
        return sigma metas (nth 1)

    | 35 -> (* match_and_run *)
        let a, b, t, p = nth 0, nth 1, nth 2, nth 3 in
        match_and_run ctxt a b t p

    | _ ->
        Exceptions.block "I have no idea what is this construct of T that you have here"


and run_fix (env, renv, sigma, _, _ as ctxt) h a b s i f x =
  let fixf = mkApp(h, Array.append a [|b;s;i;f|]) in
  let c = mkApp (f, Array.append [| fixf|] x) in
  run' ctxt c

and match_and_run (env, renv, sigma0, undo, metas) a b t p =
  try
    let open Munify in
    let open Pattern in
    let open Evarsolve in
    let (sigma, evars, x, func) = open_pattern env sigma0 p in
    (* func has Coq type x = t -> M (B x) *)
    let ts = Conv_oracle.get_transp_state (Environ.oracle env) in
    let bt = mkApp(b, [|t|]) in
    match unify_match evars ts env sigma Reduction.CONV x t with
    | Success sigma ->
        if Evar.Set.for_all (Evd.is_defined sigma) evars then
          begin
            let func = Evarutil.nf_evar sigma func in
            let sigma = Evar.Set.fold (fun e sigma->Evd.remove sigma e) evars sigma in
            let eqrefl = CoqEq.mkAppEqRefl a t in
            let r = run' (env, renv, sigma, undo, metas) (mkApp (func, [|eqrefl|])) in
            match r with
            | Val (sigma, metas, r) ->
                return sigma metas (CoqOption.mkSome bt r)
            | _ -> r
          end
        else
          Exceptions.(block (error_stuck p))
    | _ ->
        return sigma0 metas (CoqOption.mkNone bt)
  with Pattern.NotAPattern ->
    Exceptions.(block (error_stuck p))

(* Takes a [sigma], a set of evars [metas], and a [term],
   and garbage collects all the [metas] in [sigma] that do not appear in
   [term]. *)
let clean_unused_metas sigma metas term =
  let rec rem (term : constr) (metas : ExistentialSet.t) =
    let fms = Evd.evars_of_term term in
    let metas = ExistentialSet.diff metas fms in
    (* we also need to remove all metas that occur in the
       types, context, and terms of other metas *)
    ExistentialSet.fold (fun ev metas ->
      let ev_info = Evd.find sigma ev  in
      let metas = rem (Evd.evar_concl ev_info) metas in
      let metas = List.fold_right (fun (_, body, ty) metas ->
        let metas = rem ty metas in
        match body with
        | None -> metas
        | Some v -> rem v metas) (Evd.evar_context ev_info) metas in
      match Evd.evar_body ev_info with
      | Evar_empty -> metas
      | Evar_defined b -> rem b metas
    ) fms metas
  in
  let metas = rem term metas in
  (* remove all the reminding metas, also from the future goals *)
  let sigma = ExistentialSet.fold
                (fun ev sigma -> Evd.remove sigma ev) metas sigma in
  let future_goals = Evd.future_goals sigma in
  let principal_goal = Evd.principal_future_goal sigma in
  let sigma = Evd.reset_future_goals sigma in
  let alive = List.filter (fun e->not (ExistentialSet.mem e metas)) future_goals in
  let principal_goal =
    match principal_goal with
    | Some e ->
        if not (ExistentialSet.mem e metas) then
          Some e
        else
          None
    | None -> None
  in
  Evd.restore_future_goals sigma alive principal_goal

let run (env, sigma) t  =
  let _ = ArrayRefs.clean () in
  let (sigma, renv) = build_hypotheses sigma env in
  match run' (env, renv, sigma, [], ExistentialSet.empty) (nf_evar sigma t) with
  | Err (sigma', metas, v) ->
      Err (sigma', metas, nf_evar sigma' v)
  | Val (sigma', metas, v) ->
      (* let sigma' = clean_unused_metas sigma' metas v in *)
      Val (sigma', ExistentialSet.empty, nf_evar sigma' v)
