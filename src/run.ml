(** This module defines the interpretation of mtac constr
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

let reduce_value = Tacred.compute

module Constr = struct
  exception Constr_not_found of string
  exception Constr_poly of string

  let mkConstr name = lazy (
    try Universes.constr_of_global
          (Nametab.global_of_path (Libnames.path_of_string name))
    with Not_found -> raise (Constr_not_found name)
       | Invalid_argument _ -> raise (Constr_poly name)
  )

  let mkUConstr name sigma env =
    try Evd.fresh_global env sigma
          (Nametab.global_of_path (Libnames.path_of_string name))
    with Not_found -> raise (Constr_not_found name)

  let isConstr = fun r c -> eq_constr (Lazy.force r) c

  let isUConstr r sigma env = fun c ->
    eq_constr_nounivs (snd (mkUConstr r sigma env)) c

  let eq_ind i1 i2 = Names.eq_ind (fst i1) (fst i2)

end

module ConstrBuilder = struct

  type t = string

  let from_string (s:string) : t = s

  let build_app s args = mkApp (Lazy.force (Constr.mkConstr s), args)

  let equal s = Constr.isConstr (Constr.mkConstr s)

  exception WrongConstr of t * constr

  let from_coq s (env, sigma as ctx) cterm =
    let (head, args) = whd_betadeltaiota_stack env sigma cterm in
    let args = Array.of_list args in
    if equal s head then
      args
    else
      raise (WrongConstr (s, head))
end

module UConstrBuilder = struct

  type t = string

  let from_string (s:string) : t = s

  let build_app s sigma env args =
    let (sigma, c) = Constr.mkUConstr s sigma env in
    (sigma, mkApp (c, args))

  let equal = Constr.isUConstr

  exception WrongConstr of t * constr

  let from_coq s (env, sigma as ctx) cterm =
    let (head, args) = whd_betadeltaiota_stack env sigma cterm in
    let args = Array.of_list args in
    if equal s sigma env head then
      args
    else
      raise (WrongConstr (s, head))
end

module CoqOption = struct
  let noneBuilder = ConstrBuilder.from_string "Coq.Init.Datatypes.None"

  let mkNone ty = ConstrBuilder.build_app noneBuilder [|ty|]

  let someBuilder = ConstrBuilder.from_string "Coq.Init.Datatypes.Some"

  let mkSome ty t = ConstrBuilder.build_app someBuilder [|ty; t|]

  let from_coq (env, sigma as ctx) cterm fsome =
    try
      let _ = ConstrBuilder.from_coq noneBuilder ctx cterm in
      None
    with ConstrBuilder.WrongConstr _ ->
      let arr = ConstrBuilder.from_coq someBuilder ctx cterm in
      Some (fsome arr.(0))

end

module MtacNames = struct
  let mtac_module_name = "Mtac2.Mtac2.Mtac"
  let mkConstr e sigma env = (sigma, Lazy.force (Constr.mkConstr (mtac_module_name ^ "." ^ e)))
  let mkBuilder e = ConstrBuilder.from_string (mtac_module_name ^ "." ^ e)
  let mkT_lazy = mkConstr "Mtac"
  let mkUConstr e = (Constr.mkUConstr (mtac_module_name ^ "." ^ e))

  let isConstr e sigma env =
    let (_, c) = mkConstr e sigma env in
    eq_constr c

  let mkBase = mkConstr "base"
  let mkTele = mkConstr "tele"

  let isBase = isConstr "base"
  let isTele = isConstr "tele"

end

let constr_to_string t = string_of_ppcmds (Termops.print_constr t)

module Exceptions = struct

  let mkInternalException = MtacNames.mkConstr

  let mkNullPointer = mkInternalException  "NullPointer"
  let mkTermNotGround = mkInternalException  "TermNotGround"
  let mkOutOfBounds = mkInternalException  "ArrayOutOfBounds"
  let noPatternMatches = "NoPatternMatches"

  (* HACK: we put Prop as the type of the raise. We can put an evar, but
     what's the point anyway? *)
  let mkRaise e env sigma =
    let (sigma, c) = MtacNames.mkConstr "raise" sigma env in
    let (sigma, a) = MtacNames.mkConstr e sigma env in
    (sigma, mkApp(c, [|mkProp; a|]))

  let error_stuck = "Cannot reduce term, perhaps an opaque definition?"
  let error_param = "Parameter appears in returned value"
  let error_abs x = "Cannot abstract non variable " ^ (constr_to_string x)
  let error_abs_env = "Cannot abstract variable in a context depending on it"
  let error_abs_type = "Variable is appearing in the returning type"
  let error_abs_ref = "Variable is appearing in type of reference"
  let error_array_zero = "Array must have non-zero length"
  let unknown_reduction_strategy = "Unknown reduction strategy"

  let block = Errors.error
end

module ReductionStrategy = struct
(*
     let redNone = MtacNames.mkConstr "RedNone"
     let redSimpl = MtacNames.mkConstr "RedSimpl"
     let redWhd = MtacNames.mkConstr "RedWhd"
     let redOneStep = MtacNames.mkConstr "RedOneStep"
  *)
  let isRedNone = MtacNames.isConstr "RedNone"
  let isRedSimpl = MtacNames.isConstr "RedSimpl"
  let isRedWhd = MtacNames.isConstr "RedWhd"
  let isRedOneStep = MtacNames.isConstr "RedOneStep"

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
    let h, args = decompose_app c in
    let h = whd_evar sigma h in
    let r =
      match kind_of_term h with
      | Lambda (_, _, trm) when args <> [] ->
          (Vars.subst1 (List.hd args) trm, List.tl args)
      | LetIn (_, trm, _, body) -> (Vars.subst1 trm body, args)
      | Var _ | Rel _ | Const _ -> (try_unfolding Closure.all_transparent env h, args)
      | _ -> h, args
    in applist r

  let reduce sigma env strategy c =
    if isRedNone sigma env strategy then
      c
    else if isRedSimpl sigma env strategy then
      Tacred.simpl env sigma c
    else if isRedWhd sigma env strategy then
      whd_betadeltaiota env sigma c
    else if isRedOneStep sigma env strategy then
      one_step env sigma c
    else
      Exceptions.block Exceptions.unknown_reduction_strategy

end

module UnificationStrategy = struct
(*
     let mkUni = fun s -> lazy (MtacNames.mkConstr s)
     let uniRed = mkUni "UniRed"
     let uniSimpl = mkUni "UniSimpl"
     let uniMuni = mkUni "UniMuni"

     let test = fun r c -> eq_constr (Lazy.force r) c
  *)
  let isUniRed = MtacNames.isConstr "UniRed"
  let isUniSimpl = MtacNames.isConstr "UniSimpr"
  let isUniMuni = MtacNames.isConstr "UniMuni"

  let find_pbs sigma evars =
    let (_, pbs) = extract_all_conv_pbs sigma in
    List.filter (fun (_,_,c1,c2) ->
      List.exists (fun e ->
        Termops.occur_term e c1 || Termops.occur_term e c2) evars) pbs

  let unify rsigma env evars strategy t1 t2 =
    if isUniRed !rsigma env strategy then
      try
        let sigma = the_conv_x env t2 t1 !rsigma in
        rsigma := consider_remaining_unif_problems env sigma;
        List.length (find_pbs !rsigma evars) = 0
      with _ -> false
    else
      Exceptions.block "Unknown unification strategy"

end

module CoqList = struct
  let mkNil  = Constr.mkConstr "Coq.Init.Datatypes.nil"
  let mkCons = Constr.mkConstr "Coq.Init.Datatypes.cons"

  let makeNil ty = Term.mkApp (Lazy.force mkNil, [| ty |])
  let makeCons t x xs = Term.mkApp (Lazy.force mkCons, [| t ; x ; xs |])

  let mkListType ty =
    mkApp (Lazy.force (Constr.mkConstr "Coq.Init.Datatypes.cons"),
           [|ty|])

  let isNil  = Constr.isConstr mkNil
  let isCons = Constr.isConstr mkCons

  let rec from_coq_conv (env, sigma as ctx) (fconv : Term.constr -> 'a) cterm =
    let (constr, args) = whd_betadeltaiota_stack env sigma cterm in
    if isNil constr then [] else
    if not (isCons constr) then invalid_arg "not a list" else
      let elt = List.nth args 1 in
      let ctail = List.nth args 2 in
      fconv elt :: from_coq_conv ctx fconv ctail

  let from_coq (env, sigma as ctx) =
    from_coq_conv ctx (fun x->x)

end

module CoqEq = struct
  let mkEq = Constr.mkConstr "Coq.Init.Logic.eq"
  let mkEqRefl = Constr.mkConstr "Coq.Init.Logic.eq_refl"

  let mkAppEq a x y = mkApp(Lazy.force mkEq, [|a;x;y|])
  let mkAppEqRefl a x = mkApp(Lazy.force mkEqRefl, [|a;x|])
end

module CoqSigT = struct
  let mkExistT  = Constr.mkConstr "Coq.Init.Specif.existT"

  let mkAppExistT a p x px =
    mkApp (Lazy.force mkExistT, [|a; p; x; px|])
end

module CoqNat = struct
  let mkZero = Constr.mkConstr "Coq.Init.Datatypes.O"
  let mkSucc = Constr.mkConstr "Coq.Init.Datatypes.S"

  let isZero = Constr.isConstr mkZero
  let isSucc = Constr.isConstr mkSucc

  let rec to_coq = function
    | 0 -> Lazy.force mkZero
    | n -> Term.mkApp (Lazy.force mkSucc, [| to_coq (pred n) |])

  let from_coq env evd c =
    let rec fc c =
      if isZero c then
        0
      else
        let (s, n) = destApp c in
        begin
          if isSucc s then
            1 + (fc (n.(0)))
          else
            Exceptions.block "Not a nat"
        end
    in
    let c' = reduce_value env evd c in
    fc c'

end

module CoqPositive = struct
  let xI = Constr.mkConstr "Coq.Numbers.BinNums.xI"
  let xO = Constr.mkConstr "Coq.Numbers.BinNums.xO"
  let xH = Constr.mkConstr "Coq.Numbers.BinNums.xH"

  let isH = Constr.isConstr xH
  let isI = Constr.isConstr xI
  let isO = Constr.isConstr xO

  let from_coq env evd c =
    let rec fc i c =
      if isH c then
        1
      else
        let (s, n) = destApp c in
        begin
          if isI s then
            (fc (i+1) (n.(0)))*2 + 1
          else if isO s then
            (fc (i+1) (n.(0)))*2
          else
            Exceptions.block"Not a positive"
        end
    in
    let c' = reduce_value env evd c in
    fc 0 c'

  let rec to_coq n =
    if n = 1 then
      Lazy.force xH
    else if n mod 2 = 0 then
      mkApp(Lazy.force xO, [|to_coq (n / 2)|])
    else
      mkApp(Lazy.force xI, [|to_coq ((n-1)/2)|])

end

module CoqN = struct
  let tN = Constr.mkConstr "Coq.Numbers.BinNums.N"
  let h0 = Constr.mkConstr "Coq.Numbers.BinNums.N0"
  let hP = Constr.mkConstr "Coq.Numbers.BinNums.Npos"

  let is0 = Constr.isConstr h0
  let isP = Constr.isConstr hP

  let from_coq env evd c =
    let rec fc c =
      if is0 c then
        0
      else
        let (s, n) = destApp c in
        begin
          if isP s then
            CoqPositive.from_coq env evd (n.(0))
          else
            Exceptions.block "Not a positive"
        end
    in
    let c' = reduce_value env evd c in
    fc c'

  let to_coq n =
    if n = 0 then
      Lazy.force h0
    else
      mkApp(Lazy.force hP, [|CoqPositive.to_coq n|])
end

module CoqBool = struct

  let mkTrue = Constr.mkConstr "Coq.Init.Datatypes.true"
  let mkFalse = Constr.mkConstr "Coq.Init.Datatypes.false"

  let isTrue = Constr.isConstr mkTrue

end

module CoqAscii = struct

  let from_coq env sigma c =
    let (h, args) = whd_betadeltaiota_stack env sigma c in
    let rec from_bits n bits =
      match bits with
      | [] -> 0
      | (b :: bs) -> (if CoqBool.isTrue b then 1 else 0) lsl n + from_bits (n+1) bs
    in
    let n = from_bits 0 args in
    Char.escaped (Char.chr n)

end

module CoqString = struct

  let mkEmpty = Constr.mkConstr "Coq.Strings.String.EmptyString"
  let mkString = Constr.mkConstr "Coq.Strings.String.String"

  let isEmpty = Constr.isConstr mkEmpty
  let isString = Constr.isConstr mkString

  let rec from_coq env sigma s =
    let (h, args) = whd_betadeltaiota_stack env sigma s in
    if isEmpty h then
      ""
    else if isString h then
      let c, s' = List.nth args 0, List.nth args 1 in
      CoqAscii.from_coq env sigma c ^ from_coq env sigma s'
    else
      Exceptions.block "Not a string"
end

module CoqUnit = struct
  let mkTT = Constr.mkConstr "Coq.Init.Datatypes.tt"
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
  let mkArrRef= Constr.mkConstr (MtacNames.mtac_module_name ^ ".carray")

  let isArrRef =  Constr.isConstr mkArrRef

  let to_coq a i n =
    Term.mkApp (Lazy.force mkArrRef, [|a ; CoqN.to_coq i; n|])

  let from_coq env evd c =
    let c = whd_betadeltaiota env evd c in
    if isApp c && isArrRef (fst (destApp c)) then
      CoqN.from_coq env evd (snd (destApp c)).(1)
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
    let size = CoqN.from_coq evd sigma n in
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
    let index = ArrayRefFactory.from_coq env evd i in
    let arri = CoqN.from_coq env evd k in
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
    let index = ArrayRefFactory.from_coq env evd i in
    let arri = CoqN.from_coq env evd k in
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

type data = Val of (evar_map * ExistentialSet.t * constr)
          | Err of (evar_map * ExistentialSet.t * constr)

let (>>=) v g =
  match v with
  | Val v' -> g v'
  | _ -> v

let return s es t = Val (s, es, t)

let fail s es t = Err (s, es, t)

let rec open_pattern (env, sigma) p evars =
  let (patt, args) = whd_betadeltaiota_stack env sigma p in
  let length = List.length args in
  let nth = List.nth args in
  if MtacNames.isBase sigma env patt && length = 6 then
    let p = nth 3 in
    let b = nth 4 in
    let strategy = nth 5 in
    Some (sigma, evars, p, b, strategy)
  else if MtacNames.isTele sigma env patt && length = 5 then
    let c = nth 2 in
    let f = nth 4 in
    let (sigma', evar) = Evarutil.new_evar env sigma c in
    open_pattern (env, sigma') (mkApp (f, [|evar|])) (evar :: evars)
  else
    None



let rec runmatch' (env, sigma as ctxt) t ty patts' i =
  let (patts, args) =  whd_betadeltaiota_stack env sigma patts' in
  if CoqList.isNil patts && List.length args = 1 then
    Exceptions.mkRaise Exceptions.noPatternMatches env sigma
  else if CoqList.isCons patts && List.length args = 3 then
    match open_pattern ctxt (List.nth args 1) [] with
      Some (sigma', evars, p, body, strategy) ->
        let rsigma' = ref sigma' in
        let devars = destEvars evars in
        begin
          if unify env rsigma' evars strategy p t && all_defined rsigma' devars then
            let body = nf_evar !rsigma' body in
            let () = remove_all rsigma' devars in
            let body' = mkApp(body, [|CoqEq.mkAppEqRefl ty t|]) in
            (!rsigma', body')
          else
            runmatch' ctxt t ty (List.nth args 2) (i+1)
        end
    | None -> Exceptions.block Exceptions.error_stuck
  else
    Exceptions.block Exceptions.error_stuck

and destEvars =
  (* fun l -> l *)
  List.map (fun e-> let ev, _ = destEvar e in ev)

and all_defined rsigma =
  (* List.fold_left (fun b e -> b && Evd.meta_defined !rsigma e) true *)
  (*
     List.fold_left (fun b e -> b && Evd.is_defined !rsigma e) true
  *)
  (fun _->true)

and remove_all rsigma =
  fun l -> ()
(* List.iter (fun e -> rsigma := Evd.remove !rsigma e) *)

and unify env rsigma evars strategy t1 t2 =
  UnificationStrategy.unify rsigma env evars strategy t1 t2


let runmatch (env, sigma as ctxt) t ty patts =
  runmatch' ctxt t ty patts 0


let print env sigma s = Printf.printf "[DEBUG] %s\n" (CoqString.from_coq env sigma s)
let print_term t = Printf.printf "[DEBUG] "; msg (Termops.print_constr t); Printf.printf "\n"

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
  let (sigma, mkCase) = MtacNames.mkConstr "mkCase" sigma env in
  let (sigma, dyn) = MtacNames.mkUConstr "dyn" sigma env in
  let (sigma, mkDyn) = MtacNames.mkUConstr "Dyn" sigma env in
  try
    let t = whd_betadeltaiota env sigma t in
    let (info, return_type, discriminant, branches) = Term.destCase t in
    let branch_dyns = Array.fold_left (
      fun l t ->
        let dyn_type = Retyping.get_type_of env sigma t in
        Term.applist (Lazy.force cons, [dyn; Term.applist (mkDyn, [dyn_type; t]); l])
    ) (Lazy.force nil) branches in
    let ind_type = Retyping.get_type_of env sigma discriminant in
    let return_type_type = Retyping.get_type_of env sigma return_type in
    (* (sigma, (Term.applist(mkCase, [t_type; t; ind_type; discriminant; branch_dyns]))) *)
    (sigma, (Term.applist(mkCase,
                          [ind_type; discriminant; t_type;
                           Term.applist(mkDyn, [return_type_type; return_type]);
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
  let map = Constr.mkConstr "List.map" in
  let (sigma, elem) = MtacNames.mkUConstr "elem" sigma env in
  let (sigma, mkDyn) = MtacNames.mkUConstr "Dyn" sigma env in
  let (sigma, case_ind) = MtacNames.mkConstr "case_ind" sigma env in
  let (sigma, case_val) = MtacNames.mkConstr "case_val" sigma env in
  let (sigma, case_type) = MtacNames.mkConstr "case_type" sigma env  in
  let (sigma, case_return) = MtacNames.mkConstr "case_return" sigma env in
  let (sigma, case_branches) = MtacNames.mkConstr "case_branches" sigma env in
  let repr_ind = Term.applist(case_ind, [case]) in
  let repr_val = Term.applist(case_val, [case]) in
  let repr_val_red = whd_betadeltaiota env sigma repr_val in
  let repr_type = Term.applist(case_type, [case]) in
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
        let mbody = Environ.lookup_mind mind env in
        let ind = Array.get mbody.mind_packets ind_i in
        let case_info = Inductiveops.make_case_info env (mind, ind_i)
                          Term.LetPatternStyle in
        let match_term = Term.mkCase (case_info, repr_return_red, repr_val_red,
                                      Array.of_list (List.rev repr_branches_red)) in
        let match_type = Retyping.get_type_of env sigma match_term in
        (sigma, Term.applist(mkDyn, [match_type;  match_term]))
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
        let (sigma, dyn) = MtacNames.mkUConstr "dyn" sigma env in
        let (sigma, mkDyn) = MtacNames.mkUConstr "Dyn" sigma env in
        let l = Array.fold_left
                  (fun l i ->
                     let constr = Names.ith_constructor_of_inductive (mind, ind_i) i in
                     let coq_constr = Term.applist (mkDyn, [CoqList.makeNil dyn]) in (* what is the sense of this line? it's being shadowed in the next one *)
                     let coq_constr = Term.applist (Term.mkConstruct constr, args) in
                     let ty = Retyping.get_type_of env sigma coq_constr in
                     let dyn_constr = Term.applist (mkDyn, [ty; coq_constr]) in
                     CoqList.makeCons dyn dyn_constr l
                  )
                  (CoqList.makeNil dyn )
                  (* this is just a dirty hack to get the indices of constructors *)
                  (Array.mapi (fun i t -> i+1) ind.mind_consnames)
        in
        (sigma, l)
    | _ -> assert false
  else
    Exceptions.block "The argument of Mconstrs is not an inductive type"

module Hypotheses = struct

  let ahyp_constr = MtacNames.mkBuilder "ahyp"

  let mkAHyp ty n t sigma env =
    let t = match t with
      | None -> CoqOption.mkNone ty
      | Some t -> CoqOption.mkSome ty t
    in UConstrBuilder.build_app ahyp_constr sigma env [|ty; n; t|]

  let mkHypType = MtacNames.mkConstr "Hyp"


  let cons_hyp ty n t renv sigma env =
    let (sigma, hyptype) = mkHypType sigma env in
    let (sigma, hyp) = mkAHyp ty n t sigma env in
    (sigma, CoqList.makeCons hyptype hyp renv)

  let from_coq (env, sigma as ctx) c =
    let fvar = fun c ->
      if Term.isVar c || isRel c then c
      else Exceptions.block "Not a variable in hypothesis"
    in
    let fdecl = fun d -> CoqOption.from_coq ctx d (fun c->c) in
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

(** Abstract *)
let abs ?(mkprod=false) (env, sigma, metas) a p x y =
  let x = whd_betadeltaiota env sigma x in
  (* check if the type p does not depend of x, and that no variable
     created after x depends on it.  otherwise, we will have to
     substitute the context, which is impossible *)
  if isRel x then
    let rel = destRel x in
    if Vars.noccurn rel p then
      if noccurn_env env rel then
        try
          let y' = mysubstn (mkRel 1) rel y in
          let t =
            if mkprod then Term.mkProd (Names.Anonymous, a, y')
            else Term.mkLambda (Names.Anonymous, a, y') in
          return sigma metas t
        with AbstractingArrayType ->
          Exceptions.block Exceptions.error_abs_ref
      else
        Exceptions.block Exceptions.error_abs_env
    else
      Exceptions.block Exceptions.error_abs_type
  else if isVar x then
    let name = destVar x in
    if not (Termops.occur_var env name p) then
      if not (name_occurn_env env name) then
        let y' = Vars.subst_vars [name] y in
        let t =
          if mkprod then Term.mkProd (Name name, a, y')
          else Term.mkLambda (Name name, a, y') in
        return sigma metas t
      else
        Exceptions.block Exceptions.error_abs_env
    else
      Exceptions.block Exceptions.error_abs_type
  else
    Exceptions.block (Exceptions.error_abs x)

let cvar (env, sigma, metas) ty hyp =
  let hyp = Hypotheses.from_coq_list (env, sigma) hyp in
  let check_vars e t vars = Idset.subset (Termops.collect_vars t) vars &&
                            if Option.has_some e then
                              Idset.subset (Termops.collect_vars (Option.get e)) vars
                            else true
  in
  let _, _, subs, env' = List.fold_right (fun (i, e, t) (avoid, avoids, subs, env') ->
    if isRel i then
      let n = destRel i in
      let na, _, _ = List.nth (rel_context env) (n-1) in
      let id = Namegen.next_name_away na avoid in
      let e = try Option.map (multi_subst subs) e with Not_found -> Exceptions.block "Not well-formed hypotheses" in
      let t = try multi_subst subs t with Not_found -> Exceptions.block "Not well-formed hypotheses" in
      let b = check_vars e t avoids in
      let d = (id, e, t) in
      if b then
        (id::avoid, Idset.add id avoids, (n, mkVar id) :: subs, push_named d env')
      else
        Exceptions.block "Not well-formed hypotheses"
    else
      let id = destVar i in
      if check_vars e t avoids then
        (id::avoid, Idset.add id avoids, subs, push_named (id, e, t) env')
      else
        Exceptions.block "Not well-formed hypotheses"
  ) hyp ([], Idset.empty, [], empty_env)
  in
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


let rec run' (env, renv, sigma, undo, metas as ctxt) t =
  let t = whd_betadeltaiota env sigma t in
  let (h, args) = Term.decompose_app t in
  let nth = List.nth args in
  let constr c =
    if Term.isConstruct c then
      let ((m, ix), _) = Term.destConstruct c in
      if Names.eq_ind m (fst (Term.destInd (snd (MtacNames.mkT_lazy sigma env)))) then
        ix
      else
        Exceptions.block Exceptions.error_stuck
    else
      Exceptions.block Exceptions.error_stuck
  in
  match constr h with
  | 1 -> (* ret *)
      return sigma metas (ReductionStrategy.reduce sigma env (nth 1) (nth 2))

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
      fail sigma metas (List.nth args 1)

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

  | 10 -> (* match *)
      let (sigma', body) = runmatch (env, sigma) (nth 2) (nth 0) (nth 3) in
      run' (env, renv, sigma', undo, metas) body

  | 11 -> (* print *)
      let s = nth 0 in
      print env sigma s;
      return sigma metas (Lazy.force CoqUnit.mkTT)

  | 12 -> (* nu *)
      let a, f = nth 0, nth 2 in
      let fx = mkApp(Vars.lift 1 f, [|mkRel 1|]) in
      let renv = Vars.lift 1 renv in
      let ur = ref [] in
      begin
        let env = push_rel (Anonymous, None, a) env in
        let (sigma, renv) = Hypotheses.cons_hyp a (mkRel 1) None renv sigma env in
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

  | 13 -> (* is_param *)
      let e = whd_betadeltaiota env sigma (nth 1) in
      if isRel e then
        return sigma metas (Lazy.force CoqBool.mkTrue)
      else
        return sigma metas (Lazy.force CoqBool.mkFalse)

  | 14 -> (* abs *)
      let a, p, x, y = nth 0, nth 1, nth 2, nth 3 in
      abs (env, sigma, metas) a p x y
(*
     | 15 -> (* abs_eq *)
     let a, p, x, y = nth 0, nth 1, nth 2, nth 3 in
     abs env sigma metas a p x y true
  *)
  | 16 -> (* evar *)
      let t = nth 0 in
      let (sigma', ev) = Evarutil.new_evar env sigma t in
      return sigma' (ExistentialSet.add (fst (destEvar ev)) metas) ev

  | 17 -> (* is_evar *)
      let e = whd_betadeltaiota env sigma (nth 1) in
      if isEvar e then
        return sigma metas (Lazy.force CoqBool.mkTrue)
      else
        return sigma metas (Lazy.force CoqBool.mkFalse)

  | 18 -> (* hash *)
      return sigma metas (hash ctxt (nth 1) (nth 2))

  | 19 -> (* nu_let *)
      let a, t, f = nth 0, nth 2, nth 3 in
      let fx = mkApp(Vars.lift 1 f, [|mkRel 1;CoqEq.mkAppEqRefl a (mkRel 1)|]) in
      let renv = Vars.lift 1 renv in
      let ur = ref [] in
      begin
        let env = push_rel (Anonymous, Some t, a) env in
        let (sigma, renv) = Hypotheses.cons_hyp a (mkRel 1) (Some t) renv sigma env in
        match run' (env, renv, sigma, (ur :: undo), metas) fx with
        | Val (sigma', metas, e) ->
            clean !ur;
            return sigma' metas (mkLetIn (Anonymous, t, a, e))
        | Err (sigma', metas, e) ->
            clean !ur;
            if Int.Set.mem 1 (free_rels e) then
              Exceptions.block Exceptions.error_param
            else
              fail sigma' metas (pop e)
      end

  | 20 -> (* solve_typeclasses *)
      let evd' = Typeclasses.resolve_typeclasses ~fail:false env sigma in
      return evd' metas (Lazy.force CoqUnit.mkTT)

  | 21 -> (* new_array *)
      let ty, n, c = nth 0, nth 1, nth 2 in
      let a = ArrayRefs.new_array env sigma undo ty n c in
      return sigma metas a

  | 22 -> (* get *)
      let ty, a, i = nth 0, nth 1, nth 2 in
      begin
        try
          let (sigma, e) = ArrayRefs.get env sigma undo a ty i in
          return sigma metas e
        with ArrayRefs.NullPointerException ->
          let (sigma, e) = Exceptions.mkNullPointer sigma env in
          fail sigma metas e
           | ArrayRefs.OutOfBoundsException ->
               let (sigma, e) = Exceptions.mkOutOfBounds sigma env in
               fail sigma metas e
           | ArrayRefs.WrongTypeException ->
               Exceptions.block "Wrong type!"
           | ArrayRefs.WrongIndexException ->
               Exceptions.block "Wrong array!"
      end

  | 23 -> (* set *)
      let ty, a, i, c = nth 0, nth 1, nth 2, nth 3 in
      begin
        try
          let sigma = ArrayRefs.set env sigma undo a i ty c in
          return sigma metas (Lazy.force CoqUnit.mkTT)
        with ArrayRefs.OutOfBoundsException ->
          let (sigma, e) = Exceptions.mkOutOfBounds sigma env in
          fail sigma metas e
           | ArrayRefs.WrongTypeException ->
               Exceptions.block "Wrong type!"
           | ArrayRefs.WrongIndexException ->
               Exceptions.block "Wrong array!"
      end

  | 24 -> (* print term *)
      let t = nth 1 in
      print_term t;
      return sigma metas (Lazy.force CoqUnit.mkTT)

  | 25 -> (* hypotheses *)
      return sigma metas renv

  | 26 -> (* dest case *)
      let t_type = nth 0 in
      let t = nth 1 in
      let (sigma', case) = dest_Case (env, sigma) t_type t in
      return sigma' metas case

  | 27 -> (* get constrs *)
      let t = nth 1 in
      let (sigma', constrs) = get_Constrs (env, sigma) t in
      return sigma' metas constrs

  | 28 -> (* make case *)
      let case = nth 0 in
      let (sigma', case) = make_Case (env, sigma) case in
      return sigma' metas case

  | 29 -> (* Cevar *)
      let ty, hyp = nth 0, nth 1 in
      cvar (env, sigma, metas) ty hyp

  | 30 -> (* pabs *)
      let a, p, x, y = nth 0, nth 1, nth 2, nth 3 in
      abs ~mkprod:true (env, sigma, metas) a p x y

  | _ ->
      Exceptions.block "I have no idea what is this construct of T that you have here"




and clean =
  List.iter (fun i -> ArrayRefs.invalidate i)

and run_fix (env, renv, sigma, _, _ as ctxt) h a b s i f x =
  let fixf = mkApp(h, Array.append a [|b;s;i;f|]) in
  let c = mkApp (f, Array.append [| fixf|] x) in
  run' ctxt c

and hash (env, renv, sigma, undo, metas) c size =
  let size = CoqN.from_coq env sigma size in
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

let clean_unused_metas sigma metas term =
  let rec rem (term : constr) (metas : ExistentialSet.t) =
    let fms = Evd.evars_of_term term in
    let metas = ExistentialSet.diff metas fms in
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
  (* remove all the reminding metas *)
  ExistentialSet.fold (fun ev sigma -> Evd.remove sigma ev) metas sigma

let build_hypotheses sigma env =
  let renv = List.mapi (fun n (_, t, ty) -> (mkRel (n+1), t, ty)) (rel_context env)
             @ List.rev (List.map (fun (n, t, ty) -> (mkVar n, t, ty)) (named_context env))
  in (* [H : x > 0, x : nat] *)
  let rec build renv =
    match renv with
    | [] -> let (sigma, ty) = Hypotheses.mkHypType sigma env in
        (sigma, CoqList.makeNil ty)
    | (n, t, ty) :: renv ->
        let (sigma, r) = build renv in
        Hypotheses.cons_hyp ty n t r sigma env
  in
  build renv

let run (env, sigma) t  =
  let _ = ArrayRefs.clean () in
  let (sigma, renv) = build_hypotheses sigma env in
  match run' (env, renv, sigma, [], ExistentialSet.empty) (nf_evar sigma t) with
  | Err i ->
      Err i
  | Val (sigma', metas, v) ->
      let sigma' = clean_unused_metas sigma' metas v in
      Val (sigma', ExistentialSet.empty, nf_evar sigma' v)
