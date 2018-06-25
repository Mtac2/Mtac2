(** This module defines the interpretation of MetaCoq constr
*)

open Ltac_plugin
open Declarations

open List

open Pp
open Environ
open Evd
open EConstr
open Termops
open Reductionops
open Names
open Util
open Evarconv

open Constrs

open CClosure

(* warning 40 is about picking a constructor name from a module that is not in scope *)
[@@@ocaml.warning "-40"]

let get_ts env = Conv_oracle.get_transp_state (Environ.oracle env)

(** returns the i-th position of constructor c (starting from 0) *)
let get_constructor_pos sigma c = let (_, pos), _ = destConstruct sigma c in pos-1

(** print informative exceptions *)
let debug_ex = ref false
(** traces execution *)
let trace = ref false

(** Some utilities for printing *)
let print (sigma: Evd.evar_map) env s =
  Feedback.msg_notice (app (str "[DEBUG] ")
                         (str (CoqString.from_coq (env, sigma) s)))

let print_constr (sigma: Evd.evar_map) env t =
  Feedback.msg_notice (app (str "[DEBUG] ") (Termops.print_constr_env env sigma t))

let constr_to_string (sigma: Evd.evar_map) env t =
  Pp.string_of_ppcmds (Termops.print_constr_env env sigma t)


(** Functions to convert between fconstr and econstr *)
let of_econstr e = CClosure.inject (EConstr.Unsafe.to_constr e)
let to_econstr f = EConstr.of_constr (CClosure.term_of_fconstr f)


open MtacNames


module RedList = GenericList (struct
    let nilname  = metaCoq_module_name ^ ".Reduction.rlnil"
    let consname = metaCoq_module_name ^ ".Reduction.rlcons"
    let typename = metaCoq_module_name ^ ".Reduction.rllist"
  end)


module Goal = struct

  let mkgoal = mkUConstr "Goals.goal"
  let mkGoal = mkUConstr "Goals.Goal"
  let mkAHyp = mkUConstr "Goals.AHyp"

  let mkSType = Constrs.mkConstr "Mtac2.Sorts.Sorts.SType"
  let mkSProp = Constrs.mkConstr "Mtac2.Sorts.Sorts.SProp"

  let mkTheGoal ty ev sigma env =
    let tt = Retyping.get_type_of env sigma ty in
    let tt = Reductionops.nf_all env sigma tt in
    if isSort sigma tt then
      let sort = ESorts.kind sigma (destSort sigma tt) in
      let ssort = Lazy.force (if Sorts.is_prop sort then mkSProp else mkSType) in
      let sigma, tg = mkGoal sigma env in
      sigma, mkApp (tg, [|ssort; ty;ev|])
    else
      failwith ("WAT? Not a sort?" ^ (constr_to_string sigma env tt))

  let mkAHypOrDef (name, odef, ty) body sigma env =
    (* we are going to wrap the body in a function, so we need to lift
       the indices. we also replace the name with index 1 *)
    let body = replace_term sigma (mkVar name) (mkRel 1) (Vars.lift 1 body) in
    let sigma, odef_coq = CoqOption.to_coq sigma env ty odef in
    let sigma, ahyp = mkAHyp sigma env in
    sigma, mkApp (ahyp, [|ty; odef_coq; mkLambda(Name name,ty,body)|])

  (* it assumes goal is of type goal *)
  let evar_of_goal sigma env =
    let rec eog goal =
      let (c, args) = decompose_appvect sigma goal in
      if isConstruct sigma c then
        match get_constructor_pos sigma c with
        | 0 -> (* AGoal *)
            let evar = whd_evar sigma args.(2) in
            if isEvar sigma evar then
              Some (fst (destEvar sigma evar))
            else (* it is defined *)
              None
        | 1 -> (* AHyp *)
            let func = args.(2) in
            if isLambda sigma func then
              let (_, _, body) = destLambda sigma func in
              eog body
            else
              None
        | 2 -> (* RemHyp *)
            eog args.(2)
        | _ -> failwith "Should not happen"
      else
        CErrors.user_err Pp.(str "Not a goal")
    in eog

  let goal_of_evar (env:env) sigma ev =
    let open Context.Named in
    let evinfo = Evd.find_undefined sigma ev in
    let evenv = EConstr.named_context_of_val (evar_hyps evinfo) in
    (* we remove the elements in the hypotheses that are shared with
       the current env (old to new). *)
    let newenv =
      let rec remove = function
        | (nd1 :: evenv) as l1, (nd2 :: env) ->
            if Declaration.equal (eq_constr sigma) nd1 nd2 then
              remove (evenv, env)
            else
              l1
        | l1, _ -> l1 in
      List.rev (remove (List.rev evenv, List.rev (named_context env))) in
    let ids = List.map (fun v -> EConstr.mkVar (Declaration.get_id v)) evenv in
    let evar = (ev, Array.of_list ids) in
    let sigma, tg = mkTheGoal (Evd.existential_type sigma evar) (EConstr.mkEvar evar) sigma env in
    fold_inside (fun (sigma,s) v -> mkAHypOrDef (Declaration.to_tuple v) s sigma env) newenv ~init:(sigma,tg)

end

module Exceptions = struct

  let debug_exception sigma env e t =
    if !debug_ex then print_constr sigma env (mkApp (e, [|t|]))

  let mkCannotRemoveVar sigma env x =
    let varname = CoqString.to_coq (constr_to_string sigma env x) in
    let sigma, exc = mkUConstr "Exceptions.CannotRemoveVar" sigma env in
    debug_exception sigma env exc x;
    sigma, mkApp(exc, [|varname|])

  let mkRefNotFound sigma env s =
    let msg = CoqString.to_coq s in
    let sigma, exc = (mkUConstr "Exceptions.RefNotFound" sigma env) in
    debug_exception sigma env exc msg;
    sigma, mkApp (exc, [|msg|])

  let mkDebugEx s sigma env t =
    let sigma, exc = mkUConstr ("Exceptions." ^ s) sigma env in
    debug_exception sigma env exc t;
    sigma, exc

  let mkWrongTerm = mkDebugEx "WrongTerm"

  let mkHypMissesDependency = mkDebugEx "HypMissesDependency"

  let mkTypeMissesDependency = mkDebugEx "TypeMissesDependency"

  let mkDuplicatedVariable = mkDebugEx "DuplicatedVariable"

  let mkNotAVar = mkDebugEx "NotAVar"

  let mkNotAForall = mkDebugEx "NotAForall"

  let mkNotAnApplication = mkDebugEx "NotAnApplication"

  let mkAbsDependencyError = mkDebugEx "AbsDependencyError"

  let mkExceptionNotGround = mkDebugEx "ExceptionNotGround"

  let mkStuckTerm = mkDebugEx "StuckTerm"

  let mkNotAList = mkDebugEx "NotAList"

  let mkNotAMatchExp = mkDebugEx "NotAMatchExp"

  let mkNotAnInductive = mkDebugEx "NotAnInductive"

  let mkVarAppearsInValue = mkDebugEx "VarAppearsInValue"

  let mkNotAReference sigma env ty t =
    let sigma, exc = (mkUConstr "Exceptions.NotAReference" sigma env) in
    let e = mkApp (exc, [|ty; t|]) in
    debug_exception sigma env exc t;
    sigma, e

  let mkAlreadyDeclared sigma env name =
    let sigma, exc = (mkUConstr "Exceptions.AlreadyDeclared" sigma env) in
    let e = mkApp (exc, [|name|]) in
    debug_exception sigma env exc name;
    sigma, e

  let mkTypeErrorUnboundVar = mkDebugEx "UnboundVar"

  let mkLtacError sigma env msg =
    let sigma, exc = mkUConstr "Exceptions.LtacError" sigma env in
    let coqmsg = CoqString.to_coq msg in
    let e = mkApp(exc, [|coqmsg|]) in
    debug_exception sigma env exc coqmsg;
    sigma, e

  let mkNameExists sigma env s =
    let sigma, exc = (mkUConstr "Exceptions.NameExistsInContext" sigma env) in
    let e = mkApp (exc, [|s|]) in
    debug_exception sigma env exc s;
    sigma, e

  let block msg = CErrors.user_err Pp.(str msg)
end

module E = Exceptions

module ReductionStrategy = struct
  open Reductionops
  open CClosure
  open CClosure.RedFlags
  open Context

  let isReduce sigma env c = isUConstr sigma env "Reduction.reduce" c

  let has_definition ts env sigma t =
    if isVar sigma t then
      let var = destVar sigma t in
      if not (is_transparent_variable ts var) then
        false
      else
        let n = Environ.lookup_named var env in
        Option.has_some (Named.Declaration.get_value n)
    else if isRel sigma t then
      let n = destRel sigma t in
      let n = Environ.lookup_rel n env in
      Option.has_some (Rel.Declaration.get_value n)
    else if isConst sigma t then
      let (c, _) = destConst sigma t in
      is_transparent_constant ts c && Environ.evaluable_constant c env
    else
      false

  let get_definition env sigma t : EConstr.t =
    if isVar sigma t then
      let var = destVar sigma t in
      let n = EConstr.lookup_named var env in
      match Named.Declaration.get_value n with
      | Some c -> c
      | _ -> CErrors.anomaly (Pp.str "get_definition for var didn't have definition!")
    else if isRel sigma t then
      let n = destRel sigma t in
      let d = Environ.lookup_rel n env in
      match Rel.Declaration.get_value d with
      | Some v -> (Vars.lift n) (of_constr v)
      | _ -> CErrors.anomaly (Pp.str "get_definition for rel didn't have definition!")
    else if isConst sigma t then
      let (c,ui) = destConst sigma t in
      let ui = EInstance.kind sigma ui in
      let d = Environ.constant_value_in env (c,ui) in
      of_constr d
    else
      CErrors.anomaly (Pp.str "get_definition didn't have definition!")

  let try_unfolding ts env sigma t =
    if has_definition ts env sigma t then
      get_definition env sigma t
    else
      t

  let one_step flags env sigma c =
    let ts = get_ts env in
    let h, args = decompose_app sigma c in
    let h = whd_evar sigma h in
    let r =
      match kind sigma h with
      | Lambda (_, _, trm) when args <> [] &&
                                red_set flags fBETA->
          (Vars.subst1 (List.hd args) trm, List.tl args)
      | LetIn (_, trm, _, body) when red_set flags fZETA ->
          (Vars.subst1 trm body, args)
      | Var id when red_set flags (fVAR id) ->
          (try_unfolding ts env sigma h, args)
      | Rel _ when red_set flags fDELTA ->
          (try_unfolding ts env sigma h, args)
      | Const (c, u) when red_set flags (fCONST c) ->
          (try_unfolding ts env sigma h, args)
      | _ -> h, args
    in applist r

  let redflags = [|fBETA;fDELTA;fMATCH;fFIX;fZETA|]
  let posDeltaC = Array.length redflags
  let posDeltaX = posDeltaC + 1
  let posDeltaOnly = posDeltaX + 1
  (* let posDeltaBut = posDeltaOnly + 1 *)

  let get_flags (env, sigma) flags =
    (* we assume flags have the right type and are in nf *)
    let flags = RedList.from_coq sigma env flags in
    List.fold_right (fun f reds->
      if isConstruct sigma f then
        let ci = get_constructor_pos sigma f in
        if ci < Array.length redflags then
          red_add reds redflags.(ci)
        else if ci = posDeltaC then
          red_add_transparent reds Names.cst_full_transparent_state
        else if ci = posDeltaX then
          red_add_transparent reds Names.var_full_transparent_state
        else
          failwith "Unknown flag"
      else if isApp sigma f then
        let c, args = destApp sigma f in
        if isConstruct sigma c && Array.length args = 1 then
          let reds, func =
            if get_constructor_pos sigma c = posDeltaOnly then
              red_add_transparent (red_add reds fDELTA) all_opaque,
              red_add
            else (* must be posDeltaBut *)
              red_add_transparent reds
                (Conv_oracle.get_transp_state (Environ.oracle env)),
              red_sub in
          let (sigma, ids) = RedList.from_coq_conv sigma env (fun sigma x -> sigma, get_elem sigma x) args.(0) in
          List.fold_right (fun e reds->
            if isVar sigma e then
              func reds (fVAR (destVar sigma e))
            else if isConst sigma e then
              func reds (fCONST (fst (destConst sigma e)))
            else
              failwith ("Unknown reference: " ^ constr_to_string sigma env e)) ids reds
        else
          failwith "Unknown flag"
      else
        failwith "Unknown flag"
    ) flags no_red


  let whdfun flags env sigma c =
    (* let open Machine in
     * let state = (c, Stack.empty) in
     * let (s, _) = whd_state_gen flags env sigma state in
     * Stack.zip sigma s *)
    let evars ev = safe_evar_value sigma ev in
    let infos = CClosure.create_clos_infos ~evars flags env in
    (CClosure.whd_val infos (CClosure.create_tab ()) c)

  let redfuns = [|
    (fun _ _ _ c -> c);
    (fun _ env sigma c -> Tacred.simpl env sigma (nf_evar sigma c));
    (fun fs env sigma ->one_step (get_flags (env, sigma) fs.(0)) env sigma);
    (fun fs env sigma c ->
       EConstr.of_constr (whdfun (get_flags (env, sigma) fs.(0)) env sigma (of_econstr c)));
    (fun fs env sigma->
       clos_norm_flags (get_flags (env, sigma) fs.(0)) env sigma);
    (fun _ -> Redexpr.cbv_vm) (* vm_compute *)
  |]

  let reduce sigma env strategy c =
    try
      (* note that [args] can be an empty array, or an array with one element: the flags *)
      let strategy, args = decompose_appvect sigma strategy in
      Some (redfuns.(get_constructor_pos sigma strategy) args env sigma c)
    with RedList.NotAList _ ->
      None

  (* let whd_betadeltaiota_nolet = whdfun CClosure.allnolet *)

  let whd_all_novars =
    let flags = red_add_transparent betaiota Names.cst_full_transparent_state in
    whdfun flags

  let whd_betadeltaiota = whdfun CClosure.all
end

module RE = ReductionStrategy

module UnificationStrategy = struct
  open Evarsolve

  let funs = [|
    (fun _-> Munify.unify_evar_conv);
    Munify.unify_match;
    Munify.unify_match_nored;
    (fun _ ts env sigma conv_pb t1 t2->
       try
         match evar_conv_x ts env sigma conv_pb t1 t2 with
         | Success sigma -> Success (solve_unif_constraints_with_heuristics env sigma)
         | e -> e
       with _ -> UnifFailure (sigma, Pretype_errors.ProblemBeyondCapabilities))
  |]

  let unicoq_pos = 0
  let evarconv_pos = Array.length funs -1

  (** unify oevars sigma env strategy conv_pb t1 t2 unifies t1 and t2
      according to universe restrictions conv_pb (CUMUL or CONV) and
      strategy (UniCoq,UniMatch,UniMatchNoRed,UniEvarconv). In the
      UniMatch and UniMatchNoRed cases, it only instantiates evars in
      the evars set, assuming oevars = Some evars. If oevars = None,
      then the whole set of evars is assumed.  The idea is to avoid
      pattern matching to instantiate external evars. It returns
      Success or UnifFailure and a bool stating if the strategy used
      was one of the Match. *)
  let unify oevars sigma env strategy conv_pb t1 t2 =
    let ts = get_ts env in
    let pos = get_constructor_pos sigma strategy in
    let evars =
      match oevars with
      | Some e -> e
      | _ -> Evar.Map.domain (Evd.undefined_map sigma) in
    (funs.(pos) evars ts env sigma conv_pb t1 t2,
     pos > unicoq_pos && pos < evarconv_pos)

end

(** Everything about name generation *)
module MNames = struct

  (* let mkTheName = Constr.mkConstr "Mtac2.M.TheName" *)
  (* let mkFreshFrom = Constr.mkConstr "Mtac2.M.FreshFrom" *)
  (* let mkGenerate = Constr.mkConstr "Mtac2.M.Generate" *)

  let get_name_base (env, sigma) (t: constr) : Names.Name.t option =
    (* If t is a defined variable it is reducing it *)
    let t = EConstr.of_constr (RE.whd_all_novars env sigma (of_econstr t)) in
    if isVar sigma t then Some (Name (destVar sigma t))
    else if isLambda sigma t then
      let (n, _, _) = destLambda sigma t in Some n
    else if isProd sigma t then
      let (n, _, _) = destProd sigma t in Some n
    else if isLetIn sigma t then
      let (n, _, _, _) = destLetIn sigma t in Some n
    else None

  let get_name (env, sigma as ctx) (t: constr) : constr option =
    let name = get_name_base ctx t in
    match name with
    | Some (Name i) -> Some (CoqString.to_coq (Names.Id.to_string i))
    | Some _ -> (* it is Anonymous. We generate a fresh name. *)
        let n = Namegen.next_name_away (Name (Names.Id.of_string "x")) (vars_of_env env) in
        Some (CoqString.to_coq (Names.Id.to_string n))
    | _ -> None

  let next_name_away s env = Namegen.next_name_away (Name s) (vars_of_env env)

  (* returns if the name generated is fresh or not *)
  let get_from_name (env, sigma as ctx) (t: constr) : (bool * string) option =
    let t = EConstr.of_constr (RE.whd_betadeltaiota env sigma (of_econstr t)) in
    let (h, args) = decompose_appvect sigma t in
    try
      match get_constructor_pos sigma h with
      | 0 -> (* TheName *)
          Some (false, CoqString.from_coq ctx args.(0))

      | 1 -> (* FreshFrom *)
          let name = get_name_base ctx args.(1) in
          let name =
            match name with
            | Some (Name i) -> Names.Id.to_string i
            | Some Anonymous -> "ann"
            | None -> "x"
          in
          let name = next_name_away (Names.Id.of_string name) env in
          Some (true, Names.Id.to_string name)

      | 2 -> (* FreshFromStr *)
          let name = CoqString.from_coq ctx args.(0) in
          let name = next_name_away (Names.Id.of_string name) env in
          Some (true, Names.Id.to_string name)

      | 3 -> (* Generate *)
          let name = next_name_away (Names.Id.of_string "ann") env in
          Some (true, Names.Id.to_string name)

      | _ ->
          None
    with Constr.DestKO ->
      None
end

type elem_stack = (evar_map * fconstr * stack)
type elem = (evar_map * constr)

type data_stack =
  | Val of elem_stack
  | Err of elem_stack

type data =
  | Val of elem
  | Err of elem

let return s t st : data_stack = Val (s, t, st)

let fail s t st : data_stack = Err (s, t, st)

let name_occurn_env env n =
  let open Context.Named.Declaration in
  let ids = Environ.fold_named_context_reverse
              (fun s n' -> Id.Set.add (get_id n') s)
              ~init:Id.Set.empty env in (* compute set of ids in env *)
  let ids = Id.Set.remove n ids in (* remove n *)
  let ids = Environ.really_needed env ids in (* and compute closure of ids *)
  Id.Set.mem n ids (* to finally check if n is in it *)

let dest_Case (env, sigma) t =
  let sigma, dyn = mkdyn sigma env in
  try
    let (info, return_type, discriminant, branches) = destCase sigma t in
    let sigma, branch_dyns = Array.fold_right (
      fun t (sigma,l) ->
        let dyn_type = Retyping.get_type_of env sigma t in
        let sigma, cdyn = mkDyn dyn_type t sigma env in
        CoqList.mkCons sigma env dyn cdyn l
    ) branches (CoqList.mkNil sigma env dyn) in
    let ind_type = Retyping.get_type_of env sigma discriminant in
    let return_type_type = Retyping.get_type_of env sigma return_type in
    let sigma, ret_dyn = mkDyn return_type_type return_type sigma env in
    Some (mkCase ind_type discriminant ret_dyn branch_dyns sigma env)
  with
  | Not_found ->
      Exceptions.block "Something specific went wrong. TODO: find out what!"
  | Constr.DestKO ->
      None
  | _ ->
      Exceptions.block "Something not so specific went wrong."

let make_Case (env, sigma) case =
  let (_, args) = decompose_appvect sigma case in
  let repr_ind = args.(0) in
  let repr_ind = RE.whd_betadeltaiota env sigma (of_econstr repr_ind) in
  let repr_val = args.(1) in
  let repr_return = get_elem sigma args.(2) in
  let sigma, repr_branches = CoqList.from_coq_conv sigma env (fun sigma x -> sigma, get_elem sigma x) args.(3) in
  let t_type, l = decompose_appvect sigma (EConstr.of_constr repr_ind) in
  if isInd sigma t_type then
    match kind sigma t_type with
    | Ind ((mind, ind_i), _) ->
        let case_info = Inductiveops.make_case_info env (mind, ind_i) LetPatternStyle in
        let match_term = EConstr.mkCase (case_info, repr_return, repr_val,
                                         (Array.of_list repr_branches)) in
        let match_type = Retyping.get_type_of env sigma match_term in
        mkDyn match_type match_term sigma env
    | _ -> assert false
  else
    Exceptions.block "case_type is not an inductive type"


let get_Constrs (env, sigma) t =
  (* let t = to_constr sigma t in *)
  let t_type, args = decompose_app sigma (EConstr.of_constr (RE.whd_betadeltaiota env sigma (of_econstr t))) in
  if isInd sigma t_type then
    let (mind, ind_i), _ = destInd sigma t_type in
    let mbody = Environ.lookup_mind mind env in
    let ind = Array.get (mbody.mind_packets) ind_i in
    let sigma, dyn = mkdyn sigma env in
    let args = CList.firstn mbody.mind_nparams_rec args in
    let sigma, l = Array.fold_right
                     (fun i (sigma, l) ->
                        let constr = Names.ith_constructor_of_inductive (mind, ind_i) i in
                        let coq_constr = applist (mkConstruct constr, args) in
                        let ty = Retyping.get_type_of env sigma coq_constr in
                        let sigma, dyn_constr = mkDyn ty coq_constr sigma env in
                        CoqList.mkCons sigma env dyn dyn_constr l
                     )
                     (* this is just a dirty hack to get the indices of constructors *)
                     (Array.mapi (fun i t -> i+1) ind.mind_consnames)
                     (CoqList.mkNil sigma env dyn)
    in
    let indty = applist (t_type, args) in
    let indtyty = Retyping.get_type_of env sigma indty in
    let sigma, indtydyn = mkDyn indtyty indty sigma env in
    let sigma, listty = CoqList.mkType sigma env dyn in
    let sigma, pair = CoqPair.mkPair sigma env dyn listty indtydyn l in
    Some (sigma, pair)
  else
    None

module Hypotheses = struct

  let ahyp_constr = mkUBuilder "Goals.ahyp"

  let mkAHyp sigma env ty n t =
    let sigma, t = match t with
      | None -> CoqOption.mkNone sigma env ty
      | Some t -> CoqOption.mkSome sigma env ty t
    in UConstrBuilder.build_app ahyp_constr sigma env [|ty; n; t|]

  let mkHypType = mkUConstr "Goals.Hyp"

  let cons_hyp ty n t renv sigma env =
    let (sigma, hyptype) = mkHypType sigma env in
    let sigma, hyp = mkAHyp sigma env ty n t in
    CoqList.mkCons sigma env hyptype hyp renv

  exception NotAVariable
  exception NotAHyp
  let from_coq (env, sigma as ctx) c =
    let fvar = fun c ->
      if isVar sigma c then c
      else raise NotAVariable
    in
    let fdecl = CoqOption.from_coq sigma env in
    let oargs = UConstrBuilder.from_coq ahyp_constr ctx c in
    match oargs with
    | Some args -> (fvar args.(1), fdecl args.(2), args.(0))
    | None -> raise NotAHyp

  let from_coq_list (env, sigma) t =
    (* safe to throw away sigma here as it doesn't change *)
    snd (CoqList.from_coq_conv sigma env (fun sigma x -> sigma, from_coq (env, sigma) x ) t)

end

(* It replaces each ii by ci in l = [(i1,c1) ... (in, cn)] in c.
   It throws Not_found if there is a variable not in l *)
let multi_subst sigma l c =
  let rec substrec depth c = match kind sigma c with
    | Rel k    ->
        if k<=depth then c
        else
          List.assoc (k - depth) l
    | _ -> map_with_binders sigma succ substrec depth c in
  substrec 0 c

let name_depends_on sigma deps ty ot =
  let open Id.Set in let open Termops in
  let vars = collect_vars sigma ty in
  let vars = if Option.has_some ot then
      union (collect_vars sigma (Option.get ot)) vars
    else vars in
  not (is_empty (inter vars deps))

(* given a named_context env and a variable x it returns all the
   (named) variables that depends transitively on x *)
let depends_on env sigma x =
  let open Id.Set in let open Context.Named in
  let deps = singleton x in
  fold_outside (fun v deps->
    let (n, ot, ty) = Declaration.to_tuple v in
    if name_depends_on sigma deps ty ot then
      Id.Set.add n deps
    else
      deps) env ~init:deps

let name_deps env x = depends_on (named_context env) x

let compute_deps env sigma x =
  if isVar sigma x then
    let name = destVar sigma x in
    name_deps env sigma name
  else
    failwith "check_dependencies should not be called with not a var or rel"

(* given a rel or var x and a term t and its type ty, it checks if t or ty does not depend on x *)
let check_abs_deps env sigma x t ty =
  let ndeps = compute_deps env sigma x in
  let open Id.Set in
  is_empty ndeps ||
  (* The term might depend on x, which by invariant we now is a
     variable (since ndeps is not empty) *)
  (subset (inter (collect_vars sigma t) ndeps) (singleton (destVar sigma x)) &&
   is_empty (inter (collect_vars sigma ty) ndeps))

(* check if x \not\in FV(t) union FV(env) *)
let check_dependencies env sigma x t =
  if isVar sigma x then
    let name = destVar sigma x in
    not (Termops.occur_var env sigma name t) && not (name_occurn_env env name)
  else
    failwith "check_dependencies should not be called with not a var or rel"


(** Abstract *)
type abs = AbsProd | AbsFun | AbsLet | AbsFix

(** checks if (option) definition od and type ty has named
    vars included in vars *)
let check_vars sigma od ty vars =
  Id.Set.subset (Termops.collect_vars sigma ty) vars &&
  if Option.has_some od then
    Id.Set.subset (Termops.collect_vars sigma (Option.get od)) vars
  else true

exception MissingDep

(* returns a substitution and an environment such that applying
   the substitution to a term makes the term well typed in the environment *)
let new_env (env, sigma) hyps =
  let _, _, subs, env =
    List.fold_right (fun (var, odef, ty) (idlist, idset, subs, env') ->
      (* the definition might refer to previously defined indices
         so we perform the substitution *)
      let odef =
        try Option.map (multi_subst sigma subs) odef
        with Not_found -> raise MissingDep
      in
      (* if the variable is named, its type can only refer to named variables.
         note that typing ensures the var has type ty, so its type must
         be defined in the named context *)
      if check_vars sigma odef ty idset then
        let id = destVar sigma var in
        (id::idlist, Id.Set.add id idset, subs, push_named (Context.Named.Declaration.of_tuple (id, odef, ty)) env')
      else
        raise MissingDep
    ) hyps ([], Id.Set.empty, [], empty_env)
  in subs, env

let make_evar sigma env ty =
  if isSort sigma ty && ty <> mkProp then
    let sigma, (evar, _) = Evarutil.new_type_evar env sigma Evd.UnivRigid in
    sigma, evar
  else
    let sigma, evar = Evarutil.new_evar env sigma ty in
    sigma, evar


(* return the reflected hash of a term *)
let hash env sigma c size =
  let size = CoqN.from_coq (env, sigma) size in
  let h = Constr.hash (Unsafe.to_constr c) in
  CoqN.to_coq (Pervasives.abs (h mod size))

(* reflects the hypotheses in [env] in a list of [ahyp] *)
let build_hypotheses sigma env =
  let open Context.Named.Declaration in
  let renv = List.map (fun v->let (n, t, ty) = to_tuple v in (mkVar n, t, ty))
               (named_context env) in
  (* the list is reversed: [H : x > 0, x : nat] *)
  let rec build renv =
    match renv with
    | [] -> let (sigma, ty) = Hypotheses.mkHypType sigma env in
        (CoqList.mkNil sigma env ty)
    | (n, t, ty) :: renv ->
        let (sigma, r) = build renv in
        Hypotheses.cons_hyp ty n t r sigma env
  in
  build renv

(* builds the context without x (which should be a variable) *)
let env_without sigma env renv x =
  let open Context.Named.Declaration in
  let name_env = named_context env in
  let env = Environ.reset_context env in
  let nx = destVar sigma x in
  let name_env = List.filter (fun decl -> get_id decl <> nx) name_env in
  let env = push_named_context name_env env in
  env, build_hypotheses sigma env (* TODO: we should do something smarter here, rebuilding everything is costly *)

let is_nu env sigma x nus =
  let open Context.Named.Declaration in
  let env = named_context env in
  let nx = destVar sigma x in
  let rec find env i =
    let decl = List.hd env in
    if get_id decl = nx then
      i
    else
      find (List.tl env) (i+1)
  in
  find env 0 < nus

(** declare a definition *)
exception UnsupportedDefinitionObjectKind
exception CanonicalStructureMayNotBeOpaque

let run_declare_def env sigma kind name opaque ty bod =
  let open Decl_kinds in
  (* copied from coq 8.6.1 Vernacentries *)
  let fix_exn = Future.fix_exn_of (Future.from_val bod) in
  let no_hook = Lemmas.mk_hook (fun _ _ -> ()) in
  let vernac_definition_hook p = function
    | Coercion -> Class.add_coercion_hook p
    | CanonicalStructure ->
        if opaque then raise CanonicalStructureMayNotBeOpaque else
          Lemmas.mk_hook (fun _ -> Recordops.declare_canonical_structure)
    | SubClass -> Class.add_subclass_hook p
    (* | Instance -> Lemmas.mk_hook (fun local gr -> *)
    (*   let local = match local with | Global -> false | Local -> true | _ -> raise DischargeLocality in *)
    (*   let () = Typeclasses.declare_instance None local gr *)
    (*   in () *)
    (* ) *)
    | Instance
    | IdentityCoercion | Scheme | StructureComponent | Fixpoint ->
        raise UnsupportedDefinitionObjectKind
    | _ ->
        no_hook
  in
  (* copied from coq 8.6.1 Decl_kinds *)
  let kinds = [|
    Definition
  ; Coercion
  ; SubClass
  ; CanonicalStructure
  ; Example
  ; Fixpoint
  ; CoFixpoint
  ; Scheme
  ; StructureComponent
  ; IdentityCoercion
  ; Instance
  ; Method|]
  in
  let ctx = Evd.universe_context_set sigma in
  let kind_pos = get_constructor_pos sigma kind in
  let kind = kinds.(kind_pos) in
  let name = CoqString.from_coq (env, sigma) name in
  let id = Names.Id.of_string name in
  let kn = Declare.declare_definition ~opaque:opaque ~kind:kind id ~types:ty (bod, Entries.Monomorphic_const_entry ctx) in
  let gr = Globnames.ConstRef kn in
  let () = Lemmas.call_hook fix_exn (vernac_definition_hook false kind) Global gr  in
  let c = (Universes.constr_of_global gr) in
  (* Feedback.msg_notice *)
  (*   (Termops.print_constr_env env c); *)
  (sigma, c)

(** declare implicits *)
let run_declare_implicits env sigma gr impls =
  (* we expect each item in the list to correspond to an optional element of an inductive type roughly like this:
     | Explicit
     | Implicit
     | MaximallyImplicit

     But we do not care much for the actual type so right now we just take the constructor_pos
  *)
  let impliciteness = [|
    (false, false, false)       (* Dummy value *)
  ; (false, true, true)   (* Implicit *)
  ; (true, true, true)    (* Maximal *)
  |]
  in
  let gr = Globnames.global_of_constr gr in
  let impls = CoqList.from_coq sigma env impls in
  let impls = List.rev impls in
  let idx = ref (List.length impls) in
  let impls = List.map
                (fun item ->
                   let kind_pos = get_constructor_pos sigma item in
                   let ret = (if kind_pos > 0 then
                                Some (Constrexpr.ExplByPos(!idx, None), impliciteness.(kind_pos))
                              else
                                None) in
                   (* let ret = match CoqOption.from_coq (env, sigma) item with *)
                   (*   | None -> None *)
                   (*   | Some item -> *)
                   (*       let kind_pos = get_constructor_pos item in *)
                   (*       Some (Constrexpr.ExplByPos(!idx, None), impliciteness.(kind_pos)) *)
                   (* in *)
                   idx := !idx - 1; ret
                ) impls in
  let impls = List.map_filter (fun x -> x) impls in
  (* since there is no way to declare something explicit, we clear implicits first *)
  let () = Impargs.declare_manual_implicits false gr [[]] in
  let () = Impargs.maybe_declare_manual_implicits false gr impls in
  (sigma, CoqUnit.mkTT)


let koft sigma t =
  let lf n = Lazy.force (MtacNames.mkConstr ("Tm_kind." ^ n)) in
  let open Constr in
  match kind t with
  | Var _ -> lf "tmVar"
  | Evar _ -> lf "tmEvar"
  | Sort _ -> lf "tmSort"
  | Const _ -> lf "tmConst"
  | Construct _ -> lf "tmConstruct"
  | Lambda _ -> lf "tmLambda"
  | Prod _ -> lf "tmProd"
  | LetIn _ -> lf "tmLetIn"
  | App _ -> lf "tmApp"
  | Cast _ -> lf "tmCast"
  | Ind _ -> lf "tmInd"
  | Case _ -> lf "tmCase"
  | Fix _ -> lf "tmFix"
  | CoFix _ -> lf "tmCoFix"
  | _ -> failwith "unsupported"

type ctxt = {env: Environ.env; renv: fconstr; sigma: Evd.evar_map; nus: int;
             stack: CClosure.stack;
            }

type vm = Code of fconstr | Ret of fconstr | Fail of fconstr
        | Bind of fconstr | Try of (Evd.evar_map * stack * fconstr)
        | Nu of (Names.Id.t * Environ.env * fconstr)
        (* env and renv prior to remove, and if a nu was removed *)
        | Rem of (Environ.env * fconstr * bool)

(* let vm_to_string env sigma = function *)
(*   | Code c -> "Code " ^ constr_to_string sigma env c *)
(*   | Bind c -> "Bind " ^ constr_to_string sigma env c *)
(*   | Try (_, c) -> "Try " ^ constr_to_string sigma env c *)
(*   | Ret c -> "Ret " ^ constr_to_string sigma env c *)
(*   | Fail c -> "Fail " ^ constr_to_string sigma env c *)
(*   | Nu _ -> "Nu" *)
(*   | Fix -> "Fix" *)
(*   | Rem _ -> "Rem" *)

let check_evars_exception old_sigma new_sigma env c =
  try
    let c = nf_evar old_sigma c in
    let (sigma, _) = Typing.type_of env new_sigma c in
    (sigma, c)
  with _ -> E.mkExceptionNotGround new_sigma env c

let timers = Hashtbl.create 128

let pop_args num stack =
  let rec pop_args num stack =
    if num > 0 then
      match stack with
      | Zapp args :: stack ->
          let n = Array.length args in
          if n < num then
            let (argss, stack) = pop_args (num - n) stack in
            args :: argss, stack
          else if n = num then
            [args], stack
          else
            let args, remainder = Array.chop num args in
            [args], Zapp remainder :: stack
      | _ -> failwith "no more arguments on stack"
    else
      ([Array.init 0 (fun x -> failwith "Impossible case")], stack)
  in
  let argss, stack = pop_args num stack in
  (Array.concat argss, stack)


let rec run' ctxt (vms : vm list) =
  let open MConstr in
  let sigma, env, stack = ctxt.sigma, ctxt.env, ctxt.stack in
  (* if !trace then begin
   *   print_string "<<< ";
   *   List.iter (fun vm->Printf.printf "%s :: " (vm_to_string env sigma vm)) vms;
   *   print_endline " >>>"
   * end; *)
  let vm = hd vms in
  let vms = tl vms in
  let ctxt_nu1 (_, env, renv) = {ctxt with env; renv; nus = ctxt.nus-1} in
  match vm, vms with
  | Ret c, [] -> return sigma c ctxt.stack
  | Ret c, (Bind b :: vms) -> (run'[@tailcall]) {ctxt with stack=Zapp [|c|]::stack} (Code b :: vms)
  | Ret c, (Try (_, _, b) :: vms) -> (run'[@tailcall]) ctxt (Ret c :: vms)
  | Ret c, Nu (name, _, _ as p) :: vms -> (* why the sigma'? *)
      if occur_var env sigma name (to_econstr c) then
        let (sigma, e) = E.mkVarAppearsInValue sigma env (mkVar name) in
        let ctxt = ctxt_nu1 p in
        (run'[@tailcall]) {ctxt with sigma} (Fail (of_econstr e) :: vms)
      else
        (run'[@tailcall]) (ctxt_nu1 p) (Ret c :: vms)
  | Ret c, Rem (env, renv, was_nu) :: vms -> (run'[@tailcall]) {ctxt with env; renv; nus = if was_nu then ctxt.nus+1 else ctxt.nus} (Ret c :: vms)

  | Fail c, [] -> fail sigma c ctxt.stack
  | Fail c, (Bind _ :: vms) -> (run'[@tailcall]) ctxt (Fail c :: vms)
  | Fail c, (Try (sigma, stack, b) :: vms) ->
      let sigma = Evd.set_universe_context sigma (Evd.evar_universe_context ctxt.sigma) in
      let (sigma, c) = check_evars_exception ctxt.sigma sigma env (to_econstr c) in
      (run'[@tailcall]) {ctxt with sigma; stack=Zapp [|of_econstr c|] :: stack} (Code b::vms)
  | Fail c, (Nu p :: vms) -> (run'[@tailcall]) (ctxt_nu1 p) (Fail c :: vms)
  | Fail c, Rem (env, renv, was_nu) :: vms -> (run'[@tailcall]) {ctxt with env; renv; nus = if was_nu then ctxt.nus+1 else ctxt.nus} (Ret c :: vms)

  | (Bind _ | Fail _ | Nu _ | Try _ | Rem _), _ -> failwith "ouch1"
  | Ret _, (Code _ :: _ | Ret _ :: _ | Fail _ :: _) -> failwith "ouch2"

  | Code t, _ ->
      begin
        let upd c = (Code c :: vms) in
        let return sigma c = (run'[@tailcall]) {ctxt with sigma} (Ret c :: vms) in
        let fail (sigma, c) = (run'[@tailcall]) {ctxt with sigma} (Fail c :: vms) in

        (* wrappers for return and fail to conveniently return/fail with EConstrs *)
        let ereturn s fc = return s (of_econstr fc) in
        let efail (sigma, fc) = fail (sigma, of_econstr fc) in

        (* let cont ctxt h args = (run'[@tailcall]) {ctxt with stack=Zapp args::stack} (Code h :: vms) in *)

        let evars ev = safe_evar_value sigma ev in
        let infos = CClosure.create ~share:false ~repr:(fun _ _ c -> inject c) CClosure.allnolet env evars in

        let reduced_term, stack = CClosure.whd_stack infos (CClosure.create_tab ()) t stack
        (* RE.whd_betadeltaiota_nolet env ctxt.fixpoints sigma t *)
        in

        (* filter out Zupdate nodes in stack because PMP said so :) *)
        let stack = List.filter (function | Zupdate _ -> false | _ -> true) stack in

        (* Feedback.msg_debug (Pp.int (List.length stack)); *)

        let ctxt = {ctxt with stack=stack} in

        (* let (h, args) = decompose_appvect sigma reduced_term in *)

        (* print_constr sigma env (to_econstr reduced_term); *)

        match fterm_of reduced_term with
        | FConstruct _ -> failwith ("Invariant invalidated: reduction reached the constructor of M.t.")
        | FLetIn (_,v,_,bd,e) ->
            let open ReductionStrategy in
            (* let (_, b, _, t) = destLetIn sigma h in *)
            let vc = to_econstr v in
            let (h, args') = decompose_appvect sigma vc in
            if isReduce sigma env h && Array.length args' = 3 then
              let red = Array.get args' 0 in
              let term = Array.get args' 2 in
              (* print_constr sigma env term; *)
              let ob = reduce sigma env red term in
              match ob with
              | Some b ->
                  (* print_constr sigma env b; *)
                  (* (run'[@tailcall]) ctxt (upd (mkApp (Vars.subst1 b t, args))) *)
                  (* (run'[@tailcall]) ctxt (upd (of_econstr (Vars.subst1 b (to_econstr t)))) *)
                  let e = (Esubst.subs_cons([|of_econstr b|],e)) in
                  (* print_constr sigma env (to_econstr (mk_red (FCLOS (bd, e)))); *)
                  (run'[@tailcall]) ctxt (upd (mk_red (FCLOS (bd, e))))

              | None ->
                  efail (E.mkNotAList sigma env (Array.get args' 0))
            else
              (* (run'[@tailcall]) ctxt (upd (mkApp (Vars.subst1 b t, args))) *)
              (* (run'[@tailcall]) ctxt (upd (of_econstr (Vars.subst1 (to_econstr b) (to_econstr t)))) *)
              let e = (Esubst.subs_cons([|v|],e)) in
              (run'[@tailcall]) ctxt (upd (mk_red (FCLOS (bd, e))))

        | FFlex (ConstKey (hc, _)) ->
            begin
              let h = EConstr.mkConst hc in
              (* print_constr sigma env h; *)
              match MConstr.mconstr_head_of h with
              | mh ->
                  let num_args =
                    (match mh with MHead mh ->
                       MConstr.num_args_of_mconstr mh)
                  in

                  let args, stack = pop_args num_args stack in

                  let mc =
                    (match mh with MHead mh ->
                       MConstr.mconstr_of (Array.get args) mh) in

                  let hf = reduced_term in

                  if !trace then print_constr sigma env (EConstr.of_constr (CClosure.term_of_fconstr (mk_red (FApp (reduced_term,args)))));

                  let ctxt = {ctxt with stack} in


                  (* (\* repetition :( *\) *)
                  (* let return sigma c = (run'[@tailcall]) {ctxt with sigma} (Ret c :: vms) in *)
                  (* let fail (sigma, c) = (run'[@tailcall]) {ctxt with sigma} (Fail c :: vms) in *)

                  (* (\* wrappers for return and fail to conveniently return/fail with EConstrs *\) *)
                  (* let ereturn s fc = return s (of_econstr fc) in *)
                  (* let efail (sigma, fc) = fail (sigma, of_econstr fc) in *)

                  (* Array.iter (fun x -> print_constr sigma ctxt.env (to_econstr x)) args; *)
                  begin
                    match mc with
                    | MConstr (Mret, (_, t)) -> return sigma t
                    | MConstr (Mbind, (_, _, t, f)) ->
                        (run'[@tailcall]) ctxt (Code t :: Bind f :: vms)
                    | MConstr (Mmtry', (_, t, f)) ->
                        (run'[@tailcall]) ctxt (Code t :: Try (sigma, stack, f) :: vms)
                    | MConstr (Mraise', (_, t)) -> fail (sigma, t)
                    | MConstr (Mfix1, ((a), b, f, (x))) ->
                        run_fix ctxt vms hf [|a|] b f [|x|]
                    | MConstr (Mfix2, ((a1, a2), b, f, (x1, x2))) ->
                        run_fix ctxt vms hf [|a1; a2|] b f [|x1; x2|]
                    | MConstr (Mfix3, ((a1, a2, a3), b, f, (x1, x2, x3))) ->
                        run_fix ctxt vms hf [|a1; a2; a3|] b f [|x1; x2; x3|]
                    | MConstr (Mfix4, ((a1, a2, a3, a4), b, f, (x1, x2, x3, x4))) ->
                        run_fix ctxt vms hf [|a1; a2; a3; a4|] b f [|x1; x2; x3; x4|]
                    | MConstr (Mfix5, ((a1, a2, a3, a4, a5), b, f, (x1, x2, x3, x4, x5))) ->
                        run_fix ctxt vms hf [|a1; a2; a3; a4; a5|] b f [|x1; x2; x3; x4; x5|]
                    | MConstr (Mis_var, (_, e)) ->
                        if isVar sigma (to_econstr e) then
                          ereturn sigma CoqBool.mkTrue
                        else
                          ereturn sigma CoqBool.mkFalse

                    | MConstr (Mnu, (a, _, s, ot, f)) ->
                        let a = to_econstr a in
                        let s = to_econstr s in
                        (* print_constr sigma env s; *)
                        begin
                          match MNames.get_from_name (env, sigma) s with
                          | Some (fresh, namestr) ->
                              let name = Names.Id.of_string namestr in
                              if (not fresh) && (Id.Set.mem name (vars_of_env env)) then
                                efail (Exceptions.mkNameExists sigma env s)
                              else
                                begin
                                  let ot = CoqOption.from_coq sigma env (to_econstr ot) in
                                  let env' = push_named (Context.Named.Declaration.of_tuple (name, ot, a)) env in
                                  let (sigma, renv') = Hypotheses.cons_hyp a (mkVar name) ot (to_econstr ctxt.renv) sigma env in
                                  (run'[@tailcall]) {env=env'; renv=of_econstr renv'; sigma; nus=(ctxt.nus+1); stack=Zapp [|of_econstr (mkVar name)|] :: stack}
                                    (Code f :: Nu (name, env, ctxt.renv) :: vms)
                                end
                          | None -> efail (Exceptions.mkWrongTerm sigma env s)
                        end

                    | MConstr (Mabs_fun, (a, p, x, y)) ->
                        abs vms AbsFun ctxt a p x y 0 mkProp

                    | MConstr (Mabs_let, (a, p, x, t, y)) ->
                        abs vms AbsLet ctxt a p x y 0 (to_econstr t)

                    | MConstr (Mabs_prod_type, (a, x, y)) ->
                        (* HACK: put mkProp as returning type *)
                        abs vms AbsProd ctxt a (of_econstr mkProp) x y 0 mkProp
                    | MConstr (Mabs_prod_prop, (a, x, y)) ->
                        (* HACK: put mkProp as returning type *)
                        abs vms AbsProd ctxt a (of_econstr mkProp) x y 0 mkProp

                    | MConstr (Mabs_fix, (a, f, t, n)) ->
                        let n = CoqN.from_coq (env, sigma) (to_econstr n) in
                        (* HACK: put mkProp as returning type *)
                        abs vms AbsFix ctxt a (of_econstr mkProp) f t n mkProp

                    | MConstr (Mget_binder_name, (_, t)) ->
                        let t = to_econstr t in
                        (* With the new reduction machine, there may still be casts left in t.
                           For now, we assume there is at most one
                        *)
                        let t = try let (c, _, _) =  destCast sigma t in c with Constr.DestKO -> t in
                        let s = MNames.get_name (env, sigma) t in
                        begin
                          match s with
                          | Some s -> return sigma (of_econstr s)
                          | None ->
                              efail (Exceptions.mkWrongTerm sigma env t)
                        end

                    | MConstr (Mremove, (_, _, x, t)) ->
                        let x = to_econstr x in
                        let t = to_econstr t in
                        if isVar sigma x then
                          if check_dependencies env sigma x t then
                            let isnu = is_nu env sigma x ctxt.nus in
                            let nus = if isnu then ctxt.nus-1 else ctxt.nus in
                            let env', (sigma, renv') = env_without sigma env ctxt.renv x in
                            (run'[@tailcall]) {ctxt with env=env'; renv=of_econstr renv'; sigma; nus} (Code (of_econstr t) :: Rem (env, ctxt.renv, isnu) :: vms)
                          else
                            efail (E.mkCannotRemoveVar sigma env x)
                        else
                          efail (E.mkNotAVar sigma env x)

                    | MConstr (Mgen_evar, (ty, hyp)) ->
                        let ty, hyp = to_econstr ty, to_econstr hyp in
                        cvar vms ctxt ty hyp

                    | MConstr (Mis_evar, (_, e)) ->
                        let e = whd_evar sigma (to_econstr e) in
                        if isEvar sigma e || (isApp sigma e && isEvar sigma (fst (destApp sigma e))) then
                          ereturn sigma CoqBool.mkTrue
                        else
                          ereturn sigma CoqBool.mkFalse

                    | MConstr (Mhash, (_, x1, x2)) ->
                        ereturn sigma (hash env sigma (to_econstr x1) (to_econstr x2))

                    | MConstr (Msolve_typeclasses, _) ->
                        let evd' = Typeclasses.resolve_typeclasses ~fail:false env sigma in
                        ereturn evd' CoqUnit.mkTT

                    | MConstr (Mprint, (s)) ->
                        print sigma env (to_econstr s);
                        ereturn sigma CoqUnit.mkTT

                    | MConstr (Mpretty_print, (_, t)) ->
                        let t = nf_evar sigma (to_econstr t) in
                        let s = constr_to_string sigma env t in
                        ereturn sigma (CoqString.to_coq s)

                    | MConstr (Mhyps, _) -> return sigma ctxt.renv

                    | MConstr (Mdestcase, (_, t)) ->
                        let t = to_econstr t in
                        begin
                          match dest_Case (env, sigma) t with
                          | Some (sigma', case) -> ereturn sigma' case
                          | _ -> efail (E.mkNotAMatchExp sigma env t)
                        end

                    | MConstr (Mconstrs, (_, t)) ->
                        let t = to_econstr t in
                        let oval = get_Constrs (env, sigma) t in
                        begin
                          match oval with
                          | Some (sigma', constrs) -> ereturn sigma' constrs
                          | None -> efail (E.mkNotAnInductive sigma env t)
                        end

                    | MConstr (Mmakecase, (case)) ->
                        begin
                          match make_Case (env, sigma) (to_econstr case) with
                          | (sigma', case) -> ereturn sigma' case
                          | exception CoqList.NotAList l ->
                              efail (E.mkNotAList sigma env l)
                        end

                    | MConstr (Munify, (a, x, y, uni)) ->
                        let a, x, y, uni = to_econstr a, to_econstr x, to_econstr y, to_econstr uni in
                        let sigma, feqT = CoqEq.mkType sigma env a x y in
                        begin
                          let r = UnificationStrategy.unify None sigma env uni Reduction.CONV x y in
                          match r with
                          | Evarsolve.Success sigma, _ ->
                              let sigma, feq = CoqEq.mkEqRefl sigma env a x in
                              let sigma, someFeq = CoqOption.mkSome sigma env feqT feq in
                              ereturn sigma someFeq
                          | _, _ ->
                              let sigma, none = CoqOption.mkNone sigma env feqT in
                              ereturn sigma none
                        end

                    | MConstr (Munify_univ, (x, y, uni)) ->
                        let x, y, uni = to_econstr x, to_econstr y, to_econstr uni in
                        let fT = mkProd(Name.Anonymous, x, y) in
                        begin
                          let r = UnificationStrategy.unify None sigma env uni Reduction.CUMUL x y in
                          match r with
                          | Evarsolve.Success sigma, _ ->
                              let id = mkLambda(Name.Anonymous,x,mkRel 1) in
                              let sigma, some = CoqOption.mkSome sigma env fT id in
                              ereturn sigma some
                          | _, _ ->
                              let sigma, none = CoqOption.mkNone sigma env fT in
                              ereturn sigma none
                        end

                    | MConstr (Mget_reference, s) ->
                        let s = CoqString.from_coq (env, sigma) (to_econstr s) in
                        let open Nametab in let open Libnames in
                        begin
                          match Evd.fresh_global env sigma (locate (qualid_of_string s)) with
                          | (sigma, v) ->
                              let ty = Retyping.get_type_of env sigma v in
                              let sigma, dyn = mkDyn ty v sigma env in
                              ereturn sigma dyn
                          | exception _ -> efail (Exceptions.mkRefNotFound sigma env s)
                        end

                    | MConstr (Mget_var, s) ->
                        let s = CoqString.from_coq (env, sigma) (to_econstr s) in
                        let open Context.Named in
                        begin
                          match lookup (Id.of_string s) (named_context env) with
                          | var ->
                              let sigma, dyn = mkDyn (Declaration.get_type var) (mkVar (Declaration.get_id var)) sigma env in
                              ereturn sigma dyn
                          | exception _ -> efail (Exceptions.mkRefNotFound sigma env s)
                        end

                    | MConstr (Mcall_ltac, (sort, concl, name, args)) ->
                        let open Tacinterp in
                        let open Tacexpr in
                        let open Misctypes in
                        let open Loc in
                        let open Names in
                        let concl, name, args = to_econstr concl, to_econstr name, to_econstr args in
                        let name, args = CoqString.from_coq (env, sigma) name, CoqList.from_coq sigma env args in
                        let args = List.map (CoqSig.from_coq (env, sigma)) args in
                        let tac_name = Tacenv.locate_tactic (Libnames.qualid_of_string name) in
                        let arg_name = "lx_" in
                        let args = List.mapi (fun i a->(Id.of_string (arg_name ^ string_of_int i), Value.of_constr a)) args in
                        let args_var = List.map (fun (n, _) -> Reference (ArgVar (CAst.make n))) args in
                        let to_call = TacArg (tag (TacCall (tag (ArgArg (tag tac_name), args_var)))) in
                        begin
                          try
                            let undef = Evar.Map.domain (Evd.undefined_map sigma) in
                            let args_map = List.fold_left (fun m (k, v)-> Id.Map.add k v m) Id.Map.empty args in
                            let ist = { (default_ist ()) with lfun = args_map } in
                            let (c, sigma) = Pfedit.refine_by_tactic env sigma concl (Tacinterp.eval_tactic_ist ist to_call) in
                            let new_undef = Evar.Set.diff (Evar.Map.domain (Evd.undefined_map sigma)) undef in
                            let new_undef = Evar.Set.elements new_undef in
                            let sigma, goal = Goal.mkgoal sigma env in
                            let sigma, listg = CoqList.mkType sigma env goal in
                            let sigma, goals = CoqList.pto_coq env goal (fun e sigma->Goal.goal_of_evar env sigma e) new_undef sigma in
                            let sigma, pair = CoqPair.mkPair sigma env concl listg (of_constr c) goals in
                            ereturn sigma pair
                          with CErrors.UserError(s,ppm) ->
                            let expl = string_of_ppcmds ppm in
                            let s = Option.default "" s in
                            efail (Exceptions.mkLtacError sigma env (s ^ ": " ^ expl))
                             | e ->
                                 efail (Exceptions.mkLtacError sigma env (Printexc.to_string  e))
                        end

                    | MConstr (Mlist_ltac, _) ->
                        let aux k _ = Feedback.msg_info (Pp.str (Names.KerName.to_string k)) in
                        KNmap.iter aux (Tacenv.ltac_entries ());
                        ereturn sigma CoqUnit.mkTT

                    | MConstr (Mread_line, _) ->
                        ereturn sigma (CoqString.to_coq (read_line ()))

                    | MConstr (Mdecompose, (_, t)) ->
                        let (h, args) = decompose_app sigma (to_econstr t) in
                        let sigma, dyn = mkdyn sigma env in
                        let sigma, listdyn = CoqList.mkType sigma env dyn in
                        let sigma, dh = mkDyn (Retyping.get_type_of env sigma h) h sigma env in
                        let sigma, args = CoqList.pto_coq env dyn (fun t sigma->mkDyn (Retyping.get_type_of env sigma t) t sigma env) args sigma in
                        let sigma, pair =CoqPair.mkPair sigma env dyn listdyn dh args in
                        ereturn sigma pair

                    | MConstr (Msolve_typeclass, (ty)) ->
                        let ty = to_econstr ty in
                        begin
                          match Typeclasses.resolve_one_typeclass ~unique:false env sigma  ty with
                          | (sigma, v) ->
                              let sigma, some = (CoqOption.mkSome sigma env ty v) in
                              ereturn sigma some
                          | exception Not_found ->
                              let sigma, none = (CoqOption.mkNone sigma env ty) in
                              ereturn sigma none
                        end

                    | MConstr (Mdeclare, (kind, name, opaque, ty, bod)) ->
                        let kind, name, opaque, ty, bod = to_econstr kind, to_econstr name, to_econstr opaque, to_econstr ty, to_econstr bod in
                        let ty = Unsafe.to_constr ty in
                        let bod = Unsafe.to_constr bod in
                        (match run_declare_def env sigma kind name (CoqBool.from_coq sigma opaque) ty bod with
                         | (sigma, ret) -> ereturn sigma (of_constr ret)
                         | exception CErrors.AlreadyDeclared _ ->
                             efail (E.mkAlreadyDeclared sigma env name)
                         | exception Type_errors.TypeError(env, Type_errors.UnboundVar v) ->
                             efail (E.mkTypeErrorUnboundVar sigma env (mkVar v))
                        )

                    | MConstr (Mdeclare_implicits, (t, reference, impls)) ->
                        let reference, impls = to_econstr reference, to_econstr impls in
                        let reference_t = EConstr.Unsafe.to_constr reference in
                        (match run_declare_implicits env sigma reference_t impls with
                         | (sigma, ret) -> ereturn sigma ret
                         | exception Not_found ->
                             efail (E.mkNotAReference sigma env (to_econstr t) reference)
                        )

                    | MConstr (Mos_cmd, (cmd)) ->
                        let cmd = CoqString.from_coq (env, sigma) (to_econstr cmd) in
                        let ret = Sys.command cmd in
                        ereturn sigma (CoqZ.to_coq ret)

                    | MConstr (Mget_debug_exceptions, _) ->
                        ereturn sigma (CoqBool.to_coq !debug_ex)
                    | MConstr (Mset_debug_exceptions, b) ->
                        debug_ex := CoqBool.from_coq sigma (to_econstr b);
                        ereturn sigma CoqUnit.mkTT

                    | MConstr (Mget_trace, _) ->
                        ereturn sigma (CoqBool.to_coq !trace)
                    | MConstr (Mset_trace, b) ->
                        trace := CoqBool.from_coq sigma (to_econstr b);
                        ereturn sigma CoqUnit.mkTT

                    | MConstr (Mdecompose_app', (_, _, _, uni, t, c, cont)) ->
                        (* : A B m uni a C cont  *)
                        let (t_head, t_args) = decompose_app sigma (to_econstr t) in
                        let (c_head, c_args) = decompose_app sigma (to_econstr c) in
                        if eq_constr_nounivs sigma t_head c_head then
                          let uni = to_econstr uni in
                          let rec traverse sigma t_args c_args =
                            match c_args with
                            | [] ->
                                (run'[@tailcall]) {ctxt with sigma = sigma; stack=Zapp (Array.of_list t_args) :: stack} (upd cont)
                            | c_h :: c_args ->
                                match t_args with
                                | t_h :: t_args ->
                                    let (unires, _) = UnificationStrategy.unify None sigma env uni Reduction.CONV (to_econstr t_h) c_h in
                                    begin
                                      match unires with
                                      | Success (sigma) -> traverse sigma t_args c_args
                                      | UnifFailure _ -> efail (E.mkWrongTerm sigma env c_head)
                                    end
                                | _ -> efail (E.mkWrongTerm sigma env c_head)
                          in
                          traverse sigma (List.map of_econstr t_args) c_args
                        else
                          efail (E.mkWrongTerm sigma env c_head)

                    | MConstr (Mdecompose_forallT, (_, _, t, cont)) ->
                        let t = to_econstr t in
                        begin
                          match EConstr.destProd sigma t with
                          | (_, a, b) ->
                              let (a, b) = (of_econstr a, of_econstr b) in
                              (run'[@tailcall]) {ctxt with sigma = sigma; stack=Zapp [|a; b|] :: stack} (upd cont)
                          | exception Constr.DestKO ->
                              efail (E.mkNotAForall sigma env t)
                        end

                    | MConstr (Mdecompose_forallP, (_, _, t, cont)) ->
                        let t = to_econstr t in
                        begin
                          match EConstr.destProd sigma t with
                          | (_, a, b) ->
                              let (a, b) = (of_econstr a, of_econstr b) in
                              (run'[@tailcall]) {ctxt with sigma = sigma; stack=Zapp [|a; b|] :: stack} (upd cont)
                          | exception Constr.DestKO ->
                              efail (E.mkNotAForall sigma env t)
                        end

                    | MConstr (Mdecompose_app'', (_, _, t, cont)) ->
                        let t = to_econstr t in
                        begin
                          match EConstr.destApp sigma t with
                          | (h, args) ->
                              let args, arg = Array.chop (Array.length args - 1) args in
                              let h = EConstr.mkApp (h, args) in
                              let arg = arg.(0) in
                              let h_type = Retyping.get_type_of env sigma h in
                              let arg_type = Retyping.get_type_of env sigma arg in
                              let (h_type, arg_type, h, arg) = (of_econstr h_type, of_econstr arg_type, of_econstr h, of_econstr arg) in
                              (run'[@tailcall]) {ctxt with sigma = sigma; stack=Zapp [|h_type; arg_type; h; arg|] :: stack} (upd cont)
                          | exception Constr.DestKO ->
                              efail (E.mkNotAnApplication sigma env t)
                        end

                    | MConstr (Mnew_timer, (_, t_arg)) ->
                        let t_arg = to_econstr t_arg in
                        let name, _ = destConst sigma t_arg in
                        let fname = Constant.canonical name in
                        let last = None in
                        let () = Hashtbl.add timers fname ((ref last, ref 0.0)) in
                        ereturn sigma CoqUnit.mkTT

                    | MConstr (Mstart_timer, (_, t_arg, reset)) ->
                        let reset = CoqBool.from_coq sigma (to_econstr reset) in
                        let t_arg = to_econstr t_arg in
                        let name, _ = destConst sigma t_arg in
                        let fname = Constant.canonical name in
                        begin
                          match Hashtbl.find timers fname with
                          | t ->
                              let () = fst t := Some (System.get_time ()) in
                              if reset then snd t := 0.0;
                              ereturn sigma CoqUnit.mkTT
                          | exception Not_found -> ereturn sigma CoqUnit.mkTT
                        end

                    | MConstr (Mstop_timer, (_, t_arg)) ->
                        let t_arg = to_econstr t_arg in
                        let name, _ = destConst sigma t_arg in
                        let fname = Constant.canonical name in
                        begin
                          match Hashtbl.find timers fname with
                          | t ->
                              let (last, total) = (! (fst t)), (! (snd t)) in
                              begin
                                match last with
                                | Some last ->
                                    let time = System.get_time () in
                                    snd t := total +. (System.time_difference last time)
                                | None -> snd t := -.infinity
                              end;
                              ereturn sigma CoqUnit.mkTT
                          | exception Not_found -> ereturn sigma CoqUnit.mkTT
                        end

                    | MConstr (Mreset_timer, (_, t_arg)) ->
                        let t_arg = to_econstr t_arg in
                        let name, _ = destConst sigma t_arg in
                        let fname = Constant.canonical name in
                        let t = Hashtbl.find timers fname in
                        let () = fst t := None in
                        let () = snd t := 0.0 in
                        ereturn sigma CoqUnit.mkTT

                    | MConstr (Mprint_timer, (_, t_arg)) ->
                        let t_arg = to_econstr t_arg in
                        let name, _ = destConst sigma t_arg in
                        let fname = Constant.canonical name in
                        let t = Hashtbl.find timers fname in
                        let total = !(snd t) in
                        let () = Feedback.msg_info (Pp.str (Printf.sprintf "%f" total)) in
                        ereturn sigma CoqUnit.mkTT

                    | MConstr (Mkind_of_term, (_, t)) ->
                        ereturn sigma (koft sigma (CClosure.term_of_fconstr t))
                  end
              | exception Not_found ->
                  efail (E.mkStuckTerm sigma env h)
            end
        | _ ->
            efail (E.mkStuckTerm sigma env (to_econstr reduced_term))
      end
(* h is the mfix operator, a is an array of types of the arguments, b is the
   return type of the fixpoint, f is the function
   and x its arguments. *)
and run_fix ctxt (vms: vm list) (h: fconstr) (a: fconstr array) (b: fconstr) (f: fconstr) (x: fconstr array) =
  (* (run'[@tailcall]) {ctxt with stack=Zapp (Array.append [|mk_red (FApp (h, Array.append a [|f|]))|] x)::ctxt.stack} (Code f :: vms) *)
  (* Feedback.msg_notice(Pp.str "run_fix"); *)
  (run'[@tailcall]) {ctxt with stack=Zapp (Array.append [|mk_red (FApp (h, Array.append a [|b;f|]))|] x)::ctxt.stack} (Code f :: vms)

(* abs case env a p x y n abstract variable x from term y according to the case.
   if variables depending on x appear in y or the type p, it fails. n is for fixpoint. *)
and abs vms case ctxt a p x y n t : data_stack =
  let sigma, env = ctxt.sigma, ctxt.env in
  let a, p, x, y = to_econstr a, to_econstr p, to_econstr x, to_econstr y in
  let a = nf_evar sigma a in
  let p = nf_evar sigma p in
  let x = nf_evar sigma x in
  let y = nf_evar sigma y in
  (* check if the type p does not depend of x, and that no variable
     created after x depends on it.  otherwise, we will have to
     substitute the context, which is impossible *)
  if isVar sigma x then
    if check_abs_deps env sigma x y p then
      let name = destVar sigma x in
      let y' = Vars.subst_vars [name] y in
      let t =
        match case with
        | AbsProd -> mkProd (Name name, a, y')
        | AbsFun -> mkLambda (Name name, a, y')
        | AbsLet -> mkLetIn (Name name, t, a, y')
        | AbsFix -> mkFix (([|n-1|], 0), ([|Name name|], [|a|], [|y'|]))
      in
      (run'[@tailcall]) ctxt (Ret (of_econstr t) :: vms)
    else
      let (sigma, e) = E.mkAbsDependencyError sigma env (mkApp(x,[|y;p|])) in
      (run'[@tailcall]) {ctxt with sigma} (Fail (of_econstr e) :: vms)
  else
    let (sigma, e) = E.mkNotAVar sigma env x in
    (run'[@tailcall]) {ctxt with sigma} (Fail (of_econstr e) :: vms)

and cvar vms ctxt ty ohyps =
  let env, sigma = ctxt.env, ctxt.sigma in
  let ohyps = CoqOption.from_coq sigma env ohyps in
  if Option.has_some ohyps then
    let chyps = Option.get ohyps in
    let ovars =
      try
        let hyps = Hypotheses.from_coq_list (env, sigma) chyps in
        Some (List.map (fun (v, _, _)->v) hyps, hyps)
      with Hypotheses.NotAVariable ->
        None
    in
    let fail (sigma, c) = (run'[@tailcall]) {ctxt with sigma} (Fail (of_econstr c) :: vms) in
    match ovars with
    | Some (vars, hyps) ->
        if List.distinct vars then
          let value =
            try
              let subs, env = new_env (env, sigma) hyps in
              let ty = multi_subst sigma subs ty in
              let sigma, evar = make_evar sigma env ty in
              let (e, _) = destEvar sigma evar in
              (* the evar created by make_evar has id in the substitution
                 but we need to remap it to the actual variables in hyps *)
              `OK (sigma, mkEvar (e, Array.of_list vars))
            with
            | MissingDep ->
                `MDep
            | Not_found ->
                `NFound
          in
          match value with
          | `OK (sigma, c) -> (run'[@tailcall]) {ctxt with sigma} (Ret (of_econstr c) :: vms)
          | `MDep -> fail (E.mkHypMissesDependency sigma env chyps)
          | `NFound -> fail (E.mkTypeMissesDependency sigma env chyps)
        else
          fail (E.mkDuplicatedVariable sigma env chyps)
    | None -> fail (E.mkNotAVar sigma env chyps)
  else
    let sigma, evar = make_evar sigma env ty in
    (run'[@tailcall]) {ctxt with sigma} (Ret (of_econstr evar) :: vms)

(* returns the enviornment and substitution without db rels *)
let db_to_named sigma env =
  let open Context in
  let env' = push_named_context (named_context env) (reset_context env) in
  let vars = Named.to_vars (named_context env) in
  let _, subs, env = CList.fold_right_i (fun n var (vars, subs, env') ->
    (* the definition might refer to previously defined indices
       so we perform the substitution *)
    let (name, odef, ty) = Rel.Declaration.to_tuple var in
    let odef = Option.map (multi_subst sigma subs) odef in
    let ty = multi_subst sigma subs ty in
    (* since the name can be Anonymous, we need to generate a name *)
    let id =
      match name with
      | Anonymous ->
          Id.of_string ("_MC" ^ string_of_int n)
      | Name n ->
          Namegen.next_name_away name vars in
    let nvar = Named.Declaration.of_tuple (id, odef, ty) in
    Id.Set.add id vars, (n, mkVar id) :: subs, push_named nvar env'
  ) 1 (rel_context env) (vars, [], env') in
  subs, env

(* It replaces each ci by ii in l = [(i1,c1) ... (in, cn)] in c. *)
let multi_subst_inv sigma l c =
  let l = List.map (fun (a, b) -> (b, a)) l in
  let rec substrec depth c =
    begin
      try let n = destVar sigma c in
        begin
          try mkRel (List.assoc (mkVar n) l + depth)
          with Not_found -> mkVar n
        end
      with Constr.DestKO ->
        map_with_binders sigma succ substrec depth c
    end
  in substrec 0 c


let run (env0, sigma) t : data =
  let subs, env = db_to_named sigma env0 in
  let t = multi_subst sigma subs t in
  let t = CClosure.inject (EConstr.Unsafe.to_constr t) in
  let (sigma, renv) = build_hypotheses sigma env in
  match run' {env; renv=of_econstr renv; sigma; nus=0; stack=CClosure.empty_stack} [Code t] with
  | Err (sigma', v, _) ->
      (* let v = Vars.replace_vars vsubs v in *)
      let v = multi_subst_inv sigma' subs (to_econstr v) in
      let sigma', v = check_evars_exception sigma' sigma' env0 v in
      Err (sigma', v)
  | Val (sigma', v, _) ->
      let v = multi_subst_inv sigma' subs (to_econstr v) in
      let sigma', _ = Typing.type_of env0 sigma' v in
      Val (sigma', v)

(** set the run function in unicoq *)
let _ = Munify.set_lift_constr (fun env sigma -> (mkUConstr "Lift.lift" sigma env))
let _ = Munify.set_run (fun env sigma t ->
  match run (env, sigma) t with
  | Err _ -> None
  | Val c -> Some c)
