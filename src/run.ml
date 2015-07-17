(** This module defines the interpretation of mtac constr
*)

open Term
open Evd

let reduce_value = Tacred.compute

(**  *)
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
    Term.eq_constr_nounivs (snd (mkUConstr r sigma env)) c

  let eq_ind i1 i2 = Names.eq_ind (fst i1) (fst i2)

end

(**  *)
module ConstrBuilder = struct

  type t = string

  let from_string (s:string) : t = s

  let build_app s args = mkApp (Lazy.force (Constr.mkConstr s), args)

  let equal s = Constr.isConstr (Constr.mkConstr s)

  exception WrongConstr of t * constr

  let from_coq s (env, sigma) cterm =
    let (head, args) = Reductionops.whd_betadeltaiota_stack env sigma cterm in
    let args = Array.of_list args in
    if equal s head then
      args
    else
      raise (WrongConstr (s, head))
end

(** Produces Mtac2 constr *)
module MtacNames = struct

  let mtac_module_name = "Mtac2.Mtac2"
  let mkConstr e sigma env = (sigma, Lazy.force (Constr.mkConstr (mtac_module_name ^ "." ^ e)))
  let mkBuilder e = ConstrBuilder.from_string (mtac_module_name ^ "." ^ e)
  let mkT_lazy = mkConstr "Mtac2"

  let isConstr e sigma env =
    let (_, c) = mkConstr e sigma env in
    eq_constr c

  let mkBase = mkConstr "base"
  let mkTele = mkConstr "tele"

  let isBase = isConstr "base"
  let isTele = isConstr "tele"

end

let constr_to_string t = Pp.string_of_ppcmds (Termops.print_constr t)

(**  *)
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

(** Manipulation of constr to reduce it with some strategies *)
module ReductionStrategy = struct

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
    let h, args = Term.decompose_app c in
    let h = Reductionops.whd_evar sigma h in
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
      Reductionops.whd_betadeltaiota env sigma c
    else if isRedOneStep sigma env strategy then
      one_step env sigma c
    else
      Exceptions.block Exceptions.unknown_reduction_strategy
end

module ExistentialSet = Evar.Set

(** type data : constr with the context *)
type data = Val of (Evd.evar_map * ExistentialSet.t * Term.constr)
	    | Err of (Evd.evar_map * ExistentialSet.t * Term.constr)

(**  *)
let (>>=) v g =
  match v with
    | Val v' -> g v'
    | _ -> v

let return s es t = Val (s, es, t)

let fail s es t = Err (s, es, t)

(** This function decomposes the tactic reducing it,
    check if the result is a constr, and get back the
    number associated to the tactic.
    Then according to the tactic
*)
let rec run' (env, renv, sigma, undo, metas as ctxt) t =
  let t = Reductionops.whd_betadeltaiota env sigma t in
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
      return sigma metas (* (nth 1) *)(ReductionStrategy.reduce sigma env (nth 1) (nth 2))
    | 2 -> (* bind *)
      run' ctxt (nth 2) >>= fun (sigma', metas, v) ->
      let t' = mkApp(nth 3, [|v|]) in
      run' (env, renv, sigma', undo, metas) t'
    | _ ->
      Exceptions.block "I have no idea what is this construct of T that you have here"

(**  *)
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
	  | Some v -> rem v metas)
	(Evd.evar_context ev_info) metas in
      match Evd.evar_body ev_info with
	| Evar_empty -> metas
	| Evar_defined b -> rem b metas
    ) fms metas
  in
  let metas = rem term metas in
  (* remove all the reminding metas *)
  ExistentialSet.fold (fun ev sigma -> Evd.remove sigma ev) metas sigma

(**  *)
let run (env, sigma) t  =
  match run' (env, env, sigma, [], ExistentialSet.empty) (Evarutil.nf_evar sigma t) with
    | Err i -> Err i
    | Val (sigma', metas, v) ->
      let sigma' = clean_unused_metas sigma' metas v in
      Val (sigma', ExistentialSet.empty, Evarutil.nf_evar sigma' v)

