(** This module defines the interpretation of MetaCoq constr
*)

open Ltac_plugin
open Declarations

open List
open String

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

open MtacNames


module RedList = GenericList (struct
    let nilname = metaCoq_module_name ^ ".rlnil"
    let consname = metaCoq_module_name ^ ".rlcons"
    let typename = metaCoq_module_name ^ ".rllist"
  end)


module Goal = struct

  let mkgoal = mkUConstr "goal"
  let mkGoal = mkUConstr "Goal"
  let mkAHyp = mkUConstr "AHyp"

  let mkSType = Constr.mkConstr "Mtac2.Sorts.Sorts.SType"
  let mkSProp = Constr.mkConstr "Mtac2.Sorts.Sorts.SProp"

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
    let evenv = named_context_of_val (evar_hyps evinfo) in
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
    let ids = List.map (fun v -> Term.mkVar (Declaration.get_id v)) evenv in
    let evar = (ev, Array.of_list ids) in
    let sigma, tg = mkTheGoal (of_constr @@ Evd.existential_type sigma evar) (of_constr @@ Term.mkEvar evar) sigma env in
    fold_inside (fun (sigma,s) v -> mkAHypOrDef (Declaration.to_tuple v) s sigma env) newenv ~init:(sigma,tg)

end


module Exceptions = struct

  let debug_exception sigma env e t =
    if !debug_ex then print_constr sigma env (mkApp (e, [|t|]))

  let mkCannotRemoveVar sigma env x =
    let varname = CoqString.to_coq (constr_to_string sigma env x) in
    let sigma, exc = mkUConstr "CannotRemoveVar" sigma env in
    debug_exception sigma env exc x;
    sigma, mkApp(exc, [|varname|])

  let mkRefNotFound sigma env s =
    let msg = CoqString.to_coq s in
    let sigma, exc = (mkUConstr "RefNotFound" sigma env) in
    debug_exception sigma env exc msg;
    sigma, mkApp (exc, [|msg|])

  let mkDebugEx s sigma env t =
    let sigma, exc = mkUConstr s sigma env in
    debug_exception sigma env exc t;
    sigma, exc

  let mkWrongTerm = mkDebugEx "WrongTerm"

  let mkHypMissesDependency = mkDebugEx "HypMissesDependency"

  let mkTypeMissesDependency = mkDebugEx "TypeMissesDependency"

  let mkDuplicatedVariable = mkDebugEx "DuplicatedVariable"

  let mkNotAVar = mkDebugEx "NotAVar"

  let mkAbsDependencyError = mkDebugEx "AbsDependencyError"

  let mkExceptionNotGround = mkDebugEx "ExceptionNotGround"

  let mkStuckTerm = mkDebugEx "StuckTerm"

  let mkNotAList = mkDebugEx "NotAList"

  let mkNotAMatchExp = mkDebugEx "NotAMatchExp"

  let mkVarAppearsInValue = mkDebugEx "VarAppearsInValue"

  let mkNotAReference sigma env ty t =
    let sigma, exc = (mkUConstr "NotAReference" sigma env) in
    let e = mkApp (exc, [|ty; t|]) in
    debug_exception sigma env exc t;
    sigma, e

  let mkAlreadyDeclared sigma env name =
    let sigma, exc = (mkUConstr "AlreadyDeclared" sigma env) in
    let e = mkApp (exc, [|name|]) in
    debug_exception sigma env exc name;
    sigma, e

  let mkTypeErrorUnboundVar = mkDebugEx "UnboundVar"

  let mkLtacError sigma env msg =
    let sigma, exc = mkUConstr "LtacError" sigma env in
    let coqmsg = CoqString.to_coq msg in
    let e = mkApp(exc, [|coqmsg|]) in
    debug_exception sigma env exc coqmsg;
    sigma, e

  let mkNameExists sigma env s =
    let sigma, exc = (mkUConstr "NameExistsInContext" sigma env) in
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

  let isReduce sigma env c = isUConstr sigma env "reduce" c

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
      let (d,_) = Environ.constant_value env (c,ui) in
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


  let whdfun flags env fixs sigma c =
    let open Machine in
    let state = (c, Stack.empty) in
    let (s, _) = whd_state_gen flags env fixs sigma state in
    Stack.zip sigma s

  let redfuns = [|
    (fun _ _ _ _ c -> c);
    (fun _ _ env sigma c -> Tacred.simpl env sigma (nf_evar sigma c));
    (fun fs _ env sigma ->one_step (get_flags (env, sigma) fs.(0)) env sigma);
    (fun fs fixs env sigma c ->
       whdfun (get_flags (env, sigma) fs.(0)) env fixs sigma c);
    (fun fs _ env sigma->
       clos_norm_flags (get_flags (env, sigma) fs.(0)) env sigma);
    (fun _ _ -> Redexpr.cbv_vm) (* vm_compute *)
  |]

  let reduce sigma fixs env strategy c =
    try
      (* note that [args] can be an empty array, or an array with one element: the flags *)
      let strategy, args = decompose_appvect sigma strategy in
      Some (redfuns.(get_constructor_pos sigma strategy) args fixs env sigma c)
    with RedList.NotAList _ ->
      None

  let whd_betadeltaiota_nolet = whdfun CClosure.allnolet

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
         | Success sigma -> Success (consider_remaining_unif_problems env sigma)
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

module ExistentialSet = Evar.Set

type elem = (evar_map * constr)

type data =
  | Val of elem
  | Err of elem

let return s t = Val (s, t)

let fail s t = Err (s, t)

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
  | Term.DestKO ->
      None
  | _ ->
      Exceptions.block "Something not so specific went wrong."

let make_Case (env, fixs, sigma) case =
  let (_, args) = decompose_appvect sigma case in
  let repr_ind = args.(0) in
  let repr_ind = RE.whd_betadeltaiota env fixs sigma repr_ind in
  let repr_val = args.(1) in
  let repr_return = get_elem sigma args.(2) in
  let sigma, repr_branches = CoqList.from_coq_conv sigma env (fun sigma x -> sigma, get_elem sigma x) args.(3) in
  let t_type, l = decompose_appvect sigma repr_ind in
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


let get_Constrs (env, fixs, sigma) t =
  (* let t = to_constr sigma t in *)
  let t_type, args = decompose_app sigma ((* of_constr @@ *) RE.whd_betadeltaiota env fixs sigma t) in
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
    (sigma, pair)
  else
    Exceptions.block "The argument of Mconstrs is not an inductive type"

module Hypotheses = struct

  let ahyp_constr = mkUBuilder "ahyp"

  let mkAHyp sigma env ty n t =
    let sigma, t = match t with
      | None -> CoqOption.mkNone sigma env ty
      | Some t -> CoqOption.mkSome sigma env ty t
    in UConstrBuilder.build_app ahyp_constr sigma env [|ty; n; t|]

  let mkHypType = mkUConstr "Hyp"

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
  let open Idset in let open Termops in
  let vars = collect_vars sigma ty in
  let vars = if Option.has_some ot then
      union (collect_vars sigma (Option.get ot)) vars
    else vars in
  not (is_empty (inter vars deps))

(* given a named_context env and a variable x it returns all the
   (named) variables that depends transitively on x *)
let depends_on env sigma x =
  let open Idset in let open Context.Named in
  let deps = singleton x in
  fold_outside (fun v deps->
    let (n, ot, ty) = Declaration.to_tuple v in
    if name_depends_on sigma deps ty ot then
      Idset.add n deps
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
  let open Idset in
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
  Idset.subset (Termops.collect_vars sigma ty) vars &&
  if Option.has_some od then
    Idset.subset (Termops.collect_vars sigma (Option.get od)) vars
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
        (id::idlist, Idset.add id idset, subs, push_named (Context.Named.Declaration.of_tuple (id, odef, ty)) env')
      else
        raise MissingDep
    ) hyps ([], Idset.empty, [], empty_env)
  in subs, env

let make_evar sigma env ty =
  if isSort sigma ty && ty <> mkProp then
    let sigma, (evar, _) = Evarutil.new_type_evar env sigma Evd.UnivRigid in
    sigma, evar
  else
    let sigma, evar = Evarutil.new_evar env sigma ty in
    sigma, evar

let get_name (env, fixs, sigma) (t: constr) : constr option =
  (* If t is a defined variable it is reducing it *)
  let t = RE.whd_all_novars env fixs sigma t in
  let name =
    if isVar sigma t then Some (Name (destVar sigma t))
    else if isLambda sigma t then
      let (n, _, _) = destLambda sigma t in Some n
    else if isProd sigma t then
      let (n, _, _) = destProd sigma t in Some n
    else if isLetIn sigma t then
      let (n, _, _, _) = destLetIn sigma t in Some n
    else None
  in
  match name with
  | Some (Name i) -> Some (CoqString.to_coq (Names.Id.to_string i))
  | Some _ -> (* it is Anonymous. We generate a fresh name. *)
      let n = Namegen.next_name_away (Name (Names.Id.of_string "x")) (ids_of_context env) in
      Some (CoqString.to_coq (Names.Id.to_string n))
  | _ -> None

(* return the reflected hash of a term *)
let hash env sigma c size =
  let size = CoqN.from_coq (env, sigma) size in
  let h = Term.hash_constr (to_constr sigma c) in
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
  let kn = Declare.declare_definition ~opaque:opaque ~kind:kind id ~types:ty (bod, ctx) in
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



type ctxt = {env: Environ.env; renv: constr; sigma: Evd.evar_map; nus: int;
             fixpoints: (EConstr.t, EConstr.t) Context.Named.pt;
            }

type vm = Code of constr | Ret of constr | Fail of constr
        | Bind of constr | Try of (Evd.evar_map * constr)
        | Nu of (Names.Id.t * Environ.env * constr)
        | Fix
        (* env and renv prior to remove, and if a nu was removed *)
        | Rem of (Environ.env * constr * bool)

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

let rec run' ctxt (vms : vm list) =
  let open MConstr in
  let sigma, env = ctxt.sigma, ctxt.env in
  (* if !trace then begin
   *   print_string "<<< ";
   *   List.iter (fun vm->Printf.printf "%s :: " (vm_to_string env sigma vm)) vms;
   *   print_endline " >>>"
   * end; *)
  let vm = hd vms in
  let vms = tl vms in
  let ctxt_nu1 (_, env, renv) = {ctxt with env; renv; nus = ctxt.nus-1} in
  let ctxt_fix () = {ctxt with fixpoints = List.tl ctxt.fixpoints} in
  match vm, vms with
  | Ret c, [] -> return sigma c
  | Ret c, (Bind b :: vms) -> (run'[@tailcall]) ctxt (Code (mkApp(b, [|c|])) :: vms)
  | Ret c, (Try (_, b) :: vms) -> (run'[@tailcall]) ctxt (Ret c :: vms)
  | Ret c, Nu (name, _, _ as p) :: vms -> (* why the sigma'? *)
      if occur_var env sigma name c then
        let (sigma, e) = E.mkVarAppearsInValue sigma env (mkVar name) in
        let ctxt = ctxt_nu1 p in
        (run'[@tailcall]) {ctxt with sigma} (Fail e :: vms)
      else
        (run'[@tailcall]) (ctxt_nu1 p) (Ret c :: vms)
  | Ret c, Fix :: vms -> (run'[@tailcall]) (ctxt_fix ()) (Ret c :: vms)
  | Ret c, Rem (env, renv, was_nu) :: vms -> (run'[@tailcall]) {ctxt with env; renv; nus = if was_nu then ctxt.nus+1 else ctxt.nus} (Ret c :: vms)

  | Fail c, [] -> fail sigma c
  | Fail c, (Bind _ :: vms) -> (run'[@tailcall]) ctxt (Fail c :: vms)
  | Fail c, (Try (sigma, b) :: vms) ->
      let sigma = Evd.set_universe_context sigma (Evd.evar_universe_context ctxt.sigma) in
      let (sigma, c) = check_evars_exception ctxt.sigma sigma env c in
      (run'[@tailcall]) {ctxt with sigma} (Code (mkApp(b, [|c|]))::vms)
  | Fail c, (Nu p :: vms) -> (run'[@tailcall]) (ctxt_nu1 p) (Fail c :: vms)
  | Fail c, Fix :: vms -> (run'[@tailcall]) (ctxt_fix ()) (Fail c :: vms)
  | Fail c, Rem (env, renv, was_nu) :: vms -> (run'[@tailcall]) {ctxt with env; renv; nus = if was_nu then ctxt.nus+1 else ctxt.nus} (Ret c :: vms)

  | (Bind _ | Fail _ | Nu _ | Try _ | Fix | Rem _), _ -> failwith "ouch1"
  | Ret _, (Code _ :: _ | Ret _ :: _ | Fail _ :: _) -> failwith "ouch2"

  | Code t, _ ->
      let upd c = (Code c :: vms) in
      let return sigma c = (run'[@tailcall]) {ctxt with sigma} (Ret c :: vms) in
      let fail (sigma, c) = (run'[@tailcall]) {ctxt with sigma} (Fail c :: vms) in
      let reduced_term = RE.whd_betadeltaiota_nolet env ctxt.fixpoints sigma t in
      let (h, args) = decompose_appvect sigma reduced_term in
      let nth = Array.get args in
      if isLetIn sigma h then
        let open ReductionStrategy in
        let (_, b, _, t) = destLetIn sigma h in
        let (h, args') = decompose_appvect sigma b in
        if isReduce sigma env h && Array.length args' = 3 then
          let ob = reduce sigma ctxt.fixpoints env (Array.get args' 0) (Array.get args' 2) in
          match ob with
          | Some b ->
              (run'[@tailcall]) ctxt (upd (mkApp (Vars.subst1 b t, args)))
          | None ->
              fail (E.mkNotAList sigma env (Array.get args' 0))
        else
          (run'[@tailcall]) ctxt (upd (mkApp (Vars.subst1 b t, args)))
      else
        begin
          if !trace then print_constr sigma env reduced_term;
          match h with
          | _ when isret h ->
              return sigma (nth 1)

          | _ when isbind h ->
              (run'[@tailcall]) ctxt (Code (nth 2) :: Bind (nth 3) :: vms)

          | _ when istry' h ->
              (run'[@tailcall]) ctxt (Code (nth 1) :: Try (sigma, nth 2) :: vms)

          | _ when israise h ->
              let term = nth 1 in
              fail (sigma, term)

          | _ when isfix1 h ->
              let a, b, f, x = nth 0, nth 1, nth 2, nth 3 in
              run_fix ctxt vms h [|a|] b f [|x|]

          | _ when isfix2 h ->
              let a1, a2, b, f, x1, x2 =
                nth 0, nth 1, nth 2, nth 3, nth 4, nth 5 in
              run_fix ctxt vms h [|a1; a2|] b f [|x1; x2|]

          | _ when isfix3 h ->
              let a1, a2, a3, b, f, x1, x2, x3 =
                nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7 in
              run_fix ctxt vms h [|a1; a2; a3|] b f [|x1; x2; x3|]

          | _ when isfix4 h ->
              let a1, a2, a3, a4, b, f, x1, x2, x3, x4 =
                nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7, nth 8, nth 9 in
              run_fix ctxt vms h [|a1; a2; a3; a4|] b f [|x1; x2; x3; x4|]

          | _ when isfix5 h ->
              let a1, a2, a3, a4, a5, b, f, x1, x2, x3, x4, x5 =
                nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7, nth 8, nth 9, nth 10, nth 11 in
              run_fix ctxt vms h [|a1; a2; a3; a4; a5|] b f [|x1; x2; x3; x4; x5|]

          | _ when isis_var h ->
              let e = nth 1 in
              if isVar sigma e then
                return sigma CoqBool.mkTrue
              else
                return sigma CoqBool.mkFalse

          | _ when isnu h ->
              let a, s, ot, f = nth 0, nth 2, nth 3, nth 4 in
              let namestr = CoqString.from_coq (env, sigma) s in
              let name = Names.Id.of_string namestr in
              if Id.Set.mem name (vars_of_env env) then
                fail (Exceptions.mkNameExists sigma env s)
              else
                begin
                  let fx = mkApp(f, [|mkVar name|]) in
                  let ot = CoqOption.from_coq sigma env ot in
                  let env' = push_named (Context.Named.Declaration.of_tuple (name, ot, a)) env in
                  let (sigma, renv') = Hypotheses.cons_hyp a (mkVar name) ot ctxt.renv sigma env in
                  (run'[@tailcall]) {ctxt with env=env'; renv=renv'; sigma; nus=(ctxt.nus+1)} (Code fx :: Nu (name, env, ctxt.renv) :: vms)
                end

          | _ when isabs_fun h ->
              let a, p, x, y = nth 0, nth 1, nth 2, nth 3 in
              abs vms AbsFun ctxt a p x y 0 mkProp

          | _ when isabs_let h ->
              let a, p, x, t, y = nth 0, nth 1, nth 2, nth 3, nth 4 in
              abs vms AbsLet ctxt a p x y 0 t

          | _ when isabs_prod_type h || isabs_prod_prop h ->
              let a, x, y = nth 0, nth 1, nth 2 in
              (* HACK: put mkProp as returning type *)
              abs vms AbsProd ctxt a mkProp x y 0 mkProp

          | _ when isabs_fix h ->
              let a, f, t, n = nth 0, nth 1, nth 2, nth 3 in
              let n = CoqN.from_coq (env, sigma) n in
              (* HACK: put mkProp as returning type *)
              abs vms AbsFix ctxt a mkProp f t n mkProp

          | _ when isget_binder_name h ->
              let t = nth 1 in
              let s = get_name (env, ctxt.fixpoints, sigma) t in
              begin
                match s with
                | Some s -> return sigma s
                | None ->
                    fail (Exceptions.mkWrongTerm sigma env t)
              end

          | _ when isremove h ->
              let x, t = nth 2, nth 3 in
              if isVar sigma x then
                if check_dependencies env sigma x t then
                  let isnu = is_nu env sigma x ctxt.nus in
                  let nus = if isnu then ctxt.nus-1 else ctxt.nus in
                  let env', (sigma, renv') = env_without sigma env ctxt.renv x in
                  (run'[@tailcall]) {ctxt with env=env'; renv=renv'; sigma; nus} (Code t :: Rem (env, ctxt.renv, isnu) :: vms)
                else
                  fail (E.mkCannotRemoveVar sigma env x)
              else
                fail (E.mkNotAVar sigma env x)

          | _ when isgen_evar h->
              let ty, hyp = nth 0, nth 1 in
              cvar vms ctxt ty hyp

          | _ when isis_evar h ->
              let e = whd_evar sigma (nth 1) in
              if isEvar sigma e || (isApp sigma e && isEvar sigma (fst (destApp sigma e))) then
                return sigma CoqBool.mkTrue
              else
                return sigma CoqBool.mkFalse

          | _ when ishash h ->
              return sigma (hash env sigma (nth 1) (nth 2))

          | _ when issolve_typeclasses h ->
              let evd' = Typeclasses.resolve_typeclasses ~fail:false env sigma in
              return evd' CoqUnit.mkTT

          | _ when isprint h ->
              let s = nth 0 in
              print sigma env s;
              return sigma CoqUnit.mkTT

          | _ when ispretty_print h ->
              let t = nth 1 in
              let t = nf_evar sigma t in
              let s = constr_to_string sigma env t in
              return sigma (CoqString.to_coq s)

          | _ when ishyps h ->
              return sigma ctxt.renv

          | _ when isdestcase h ->
              let t = nth 1 in
              begin
                match dest_Case (env, sigma) t with
                | Some (sigma', case) -> return sigma' case
                | _ -> fail (E.mkNotAMatchExp sigma env t)
              end

          | _ when isconstrs h ->
              let t = nth 1 in
              let (sigma', constrs) = get_Constrs (env, ctxt.fixpoints, sigma) t in
              return sigma' constrs

          | _ when ismakecase h ->
              let case = nth 0 in
              begin
                try
                  let (sigma', case) = make_Case (env, ctxt.fixpoints, sigma) case in
                  return sigma' case
                with CoqList.NotAList l ->
                  fail (E.mkNotAList sigma env l)
              end

          | _ when isunify h ->
              let a, x, y, uni = nth 0, nth 1, nth 2, nth 3 in
              let sigma, feqT = CoqEq.mkType sigma env a x y in
              begin
                let r = UnificationStrategy.unify None sigma env uni Reduction.CONV x y in
                match r with
                | Evarsolve.Success sigma, _ ->
                    let sigma, feq = CoqEq.mkEqRefl sigma env a x in
                    let sigma, someFeq = CoqOption.mkSome sigma env feqT feq in
                    return sigma someFeq
                | _, _ ->
                    let sigma, none = CoqOption.mkNone sigma env feqT in
                    return sigma none
              end

          | _ when isunify_univ h ->
              let x, y, uni = nth 0, nth 1, nth 2 in
              let fT = mkProd(Name.Anonymous, x, y) in
              begin
                let r = UnificationStrategy.unify None sigma env uni Reduction.CUMUL x y in
                match r with
                | Evarsolve.Success sigma, _ ->
                    let id = mkLambda(Name.Anonymous,x,mkRel 1) in
                    let sigma, some = CoqOption.mkSome sigma env fT id in
                    return sigma some
                | _, _ ->
                    let sigma, none = CoqOption.mkNone sigma env fT in
                    return sigma none
              end

          | _ when isget_reference h ->
              let s = CoqString.from_coq (env, sigma) (nth 0) in
              let open Nametab in let open Libnames in
              begin
                try
                  let sigma, v = Evd.fresh_global env sigma (locate (qualid_of_string s)) in
                  let ty = Retyping.get_type_of env sigma (of_constr v) in
                  let sigma, dyn = mkDyn ty (of_constr v) sigma env in
                  return sigma dyn
                with _ -> fail (Exceptions.mkRefNotFound sigma env s)
              end

          | _ when isget_var h ->
              let s = CoqString.from_coq (env, sigma) (nth 0) in
              let open Context.Named in
              begin
                try
                  let var = lookup (Id.of_string s) (named_context env) in
                  let sigma, dyn = mkDyn (Declaration.get_type var) (mkVar (Declaration.get_id var)) sigma env in
                  return sigma dyn
                with _ -> fail (Exceptions.mkRefNotFound sigma env s)
              end

          | _ when iscall_ltac h ->
              let open Tacinterp in
              let open Nametab in
              let open Tacexpr in
              let open Misctypes in
              let open Loc in
              let open Names in
              let sort, concl, name, args = nth 0, nth 1, nth 2, nth 3 in
              let name, args = CoqString.from_coq (env, sigma) name, CoqList.from_coq sigma env args in
              let args = List.map (CoqSig.from_coq (env, sigma)) args in
              let tac_name = locate_tactic (Libnames.qualid_of_string name) in
              let arg_name = "lx_" in
              let args = List.mapi (fun i a->(Id.of_string (arg_name ^ string_of_int i), Value.of_constr a)) args in
              let args_var = List.map (fun (n, _) -> Reference (ArgVar (tag n))) args in
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
                  let sigma, goals = CoqList.pto_coq env goal (fun e sigma->Goal.goal_of_evar env sigma e) new_undef sigma in
                  let sigma, pair = CoqPair.mkPair sigma env concl goal (of_constr c) goals in
                  return sigma pair
                with CErrors.UserError(s,ppm) ->
                  let expl = string_of_ppcmds ppm in
                  let s = Option.default "" s in
                  fail (Exceptions.mkLtacError sigma env (s ^ ": " ^ expl))
                   | e ->
                       fail (Exceptions.mkLtacError sigma env (Printexc.to_string  e))
              end

          | _ when islist_ltac h ->
              let aux k _ = Feedback.msg_info (Pp.str (Names.KerName.to_string k)) in
              KNmap.iter aux (Tacenv.ltac_entries ());
              return sigma CoqUnit.mkTT

          | _ when isread_line h ->
              return sigma (CoqString.to_coq (read_line ()))

          | _ when isdecompose h ->
              let (h, args) = decompose_app sigma (nth 1) in
              let sigma, dyn = mkdyn sigma env in
              let sigma, listdyn = CoqList.mkType sigma env dyn in
              let sigma, dh = mkDyn (Retyping.get_type_of env sigma h) h sigma env in
              let sigma, args = CoqList.pto_coq env dyn (fun t sigma->mkDyn (Retyping.get_type_of env sigma t) t sigma env) args sigma in
              let sigma, pair =CoqPair.mkPair sigma env dyn listdyn dh args in
              return sigma pair

          | _ when issolve_typeclass h ->
              let ty = nth 0 in
              begin
                try
                  let sigma, v = Typeclasses.resolve_one_typeclass ~unique:false env sigma  ty in
                  let sigma, some = (CoqOption.mkSome sigma env ty v) in
                  return sigma some
                with Not_found ->
                  let sigma, none = (CoqOption.mkNone sigma env ty) in
                  return sigma none
              end

          | _ when isdeclare h ->
              let kind, name, opaque, ty, bod = nth 0, nth 1, nth 2, nth 3, nth 4 in
              (try
                 let ty = to_constr sigma ty in
                 let bod = to_constr sigma bod in
                 let sigma, ret = run_declare_def env sigma kind name (CoqBool.from_coq sigma opaque) ty bod in
                 return sigma (of_constr ret)
               with
               | CErrors.AlreadyDeclared _ ->
                   fail (E.mkAlreadyDeclared sigma env name)
               | Type_errors.TypeError(env, Type_errors.UnboundVar v) ->
                   fail (E.mkTypeErrorUnboundVar sigma env (mkVar v))
              )

          | _ when isdeclare_implicits h ->
              let reference, impls = (*nth 0 is the type *) nth 1, nth 2 in
              (try
                 let reference = to_constr sigma reference in
                 let sigma, ret = run_declare_implicits env sigma reference impls in
                 return sigma ret
               with Not_found ->
                 fail (E.mkNotAReference sigma env (nth 0) reference)
              )

          | _ when isos_cmd h ->
              let cmd = CoqString.from_coq (env, sigma) (nth 0) in
              let ret = Sys.command cmd in
              return sigma (CoqZ.to_coq ret)

          | _ when isget_debug_ex h ->
              return sigma (CoqBool.to_coq !debug_ex)
          | _ when isset_debug_ex h ->
              debug_ex := CoqBool.from_coq sigma (nth 0);
              return sigma CoqUnit.mkTT

          | _ when isget_trace h ->
              return sigma (CoqBool.to_coq !trace)
          | _ when isset_trace h ->
              trace := CoqBool.from_coq sigma (nth 0);
              return sigma CoqUnit.mkTT

          | _ when isdecompose_app h ->
              let (t_head, t_args) = decompose_app sigma (nth 4) in
              let head = nth 6 in
              if eq_constr_nounivs sigma (t_head) head then
                let cont = nth 8 in
                let ptele = nth 3 in
                let rec traverse ptele t_args =
                  let ptele = ReductionStrategy.whd_betadeltaiota env ctxt.fixpoints sigma ptele in
                  match CoqPTele.from_coq sigma env ptele with
                  | None ->
                      let code = (applist (cont, t_args)) in
                      (run'[@tailcall]) ctxt (upd code)
                  | Some (x, ptele) ->
                      traverse ptele (tl t_args)
                in
                traverse ptele t_args
              else
                fail (E.mkWrongTerm sigma env head)

          | _ when isnew_timer h ->
              let t_arg = nth 1 in
              let name, _ = destConst sigma t_arg in
              let fname = Names.canonical_con name in
              let last = None in
              let () = Hashtbl.add timers fname ((ref last, ref 0.0)) in
              return sigma CoqUnit.mkTT

          | _ when isstart_timer h ->
              let reset = CoqBool.from_coq sigma (nth 2) in
              let t_arg = nth 1 in
              let name, _ = destConst sigma t_arg in
              let fname = Names.canonical_con name in
              begin
                try
                  let t = Hashtbl.find timers fname in
                  let () = fst t := Some (System.get_time ()) in
                  if reset then snd t := 0.0;
                  return sigma CoqUnit.mkTT
                with | Not_found -> return sigma CoqUnit.mkTT
              end

          | _ when isstop_timer h ->
              let t_arg = nth 1 in
              let name, _ = destConst sigma t_arg in
              let fname = Names.canonical_con name in
              begin
                try
                  let t = Hashtbl.find timers fname in
                  let (last, total) = (! (fst t)), (! (snd t)) in
                  begin
                    match last with
                    | Some last ->
                        let time = System.get_time () in
                        snd t := total +. (System.time_difference last time)
                    | None -> snd t := -.infinity
                  end;
                  return sigma CoqUnit.mkTT
                with | Not_found -> return sigma CoqUnit.mkTT
              end

          | _ when isreset_timer h ->
              let t_arg = nth 1 in
              let name, _ = destConst sigma t_arg in
              let fname = Names.canonical_con name in
              let t = Hashtbl.find timers fname in
              let () = fst t := None in
              let () = snd t := 0.0 in
              return sigma CoqUnit.mkTT

          | _ when isprint_timer h ->
              let t_arg = nth 1 in
              let name, _ = destConst sigma t_arg in
              let fname = Names.canonical_con name in
              let t = Hashtbl.find timers fname in
              let total = !(snd t) in
              let () = Feedback.msg_info (Pp.str (Printf.sprintf "%f" total)) in
              return sigma CoqUnit.mkTT


          | _ ->
              fail (E.mkStuckTerm sigma env h)
        end

(* h is the mfix operator, a is an array of types of the arguments, b is the
   return type of the fixpoint, f is the function
   and x its arguments. *)
and run_fix ctxt (vms: vm list) (h: constr) (a: constr array) (b: constr) (f: constr) (x: constr array) =
  let sigma, env = ctxt.sigma, ctxt.env in
  let name =
    if isVar sigma f then Some (Name (destVar sigma f))
    else if isLambda sigma f then
      let (n, _, _) = destLambda sigma f in Some n
    else if isProd sigma f then
      let (n, _, _) = destProd sigma f in Some n
    else if isLetIn sigma f then
      let (n, _, _, _) = destLetIn sigma f in Some n
    else None
  in
  let name = match name with | Some (Name i) -> Names.Id.to_string i | Some _ -> "anon" | None -> "impossible" in
  let n = Namegen.next_name_away (Name (Names.Id.of_string (concat "mtac_fix_" [name]))) (List.append (ids_of_context env) (ids_of_named_context ctxt.fixpoints)) in
  let fixvar = EConstr.mkVar n in
  let fixf = mkApp(f, [|fixvar|]) in
  (* HACK: we put Prop as the type of fixf in the context, simply because we
     don't care. If it turns out to be problematic, we have to construct its
     type. *)
  let fixpoints = Context.Named.Declaration.of_tuple (n, Some (fixf), EConstr.mkProp) :: ctxt.fixpoints in
  let c = mkApp (f, Array.append [| fixvar |] x) in
  (run'[@tailcall]) {ctxt with sigma=sigma; env=env; fixpoints=fixpoints} (Code c :: Fix :: vms)

(* abs case env a p x y n abstract variable x from term y according to the case.
   if variables depending on x appear in y or the type p, it fails. n is for fixpoint. *)
and abs vms case ctxt a p x y n t : data =
  let sigma, env = ctxt.sigma, ctxt.env in
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
      (run'[@tailcall]) ctxt (Ret t :: vms)
    else
      let (sigma, e) = E.mkAbsDependencyError sigma env (mkApp(x,[|y;p|])) in
      (run'[@tailcall]) {ctxt with sigma} (Fail e :: vms)
  else
    let (sigma, e) = E.mkNotAVar sigma env x in
    (run'[@tailcall]) {ctxt with sigma} (Fail e :: vms)

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
    let fail (sigma, c) = (run'[@tailcall]) {ctxt with sigma} (Fail c :: vms) in
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
          | `OK (sigma, c) -> (run'[@tailcall]) {ctxt with sigma} (Ret c :: vms)
          | `MDep -> fail (E.mkHypMissesDependency sigma env chyps)
          | `NFound -> fail (E.mkTypeMissesDependency sigma env chyps)
        else
          fail (E.mkDuplicatedVariable sigma env chyps)
    | None -> fail (E.mkNotAVar sigma env chyps)
  else
    let sigma, evar = make_evar sigma env ty in
    (run'[@tailcall]) {ctxt with sigma} (Ret evar :: vms)

(* returns the enviornment and substitution without db rels *)
let db_to_named sigma env =
  let open Context in
  let env' = push_named_context (named_context env) (reset_context env) in
  let vars = Id.Set.elements (Named.to_vars (named_context env)) in
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
    id::vars, (n, mkVar id) :: subs, push_named nvar env'
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
      with | Term.DestKO ->
        map_with_binders sigma succ substrec depth c
    end
  in substrec 0 c


let run (env0, sigma) t =
  let subs, env = db_to_named sigma env0 in
  let t = multi_subst sigma subs t in
  let (sigma, renv) = build_hypotheses sigma env in
  match run' {env; renv; sigma; nus=0; fixpoints=[]} [Code t] with
  | Err (sigma', v) ->
      (* let v = Vars.replace_vars vsubs v in *)
      let v = multi_subst_inv sigma' subs v in
      let sigma', v = check_evars_exception sigma' sigma' env0 v in
      Err (sigma', v)
  | Val (sigma', v) ->
      let v = multi_subst_inv sigma' subs v in
      let sigma', _ = Typing.type_of env0 sigma' v in
      Val (sigma', v)

(** set the run function in unicoq *)
let _ = Munify.set_lift_constr (fun env sigma -> (mkUConstr "lift" sigma env))
let _ = Munify.set_run (fun env sigma t ->
  match run (env, sigma) t with
  | Err _ -> None
  | Val c -> Some c)
