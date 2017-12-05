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
open CClosure
open Util
open Evarconv
open Libnames

open Constrs

module Stack = Reductionops.Stack

let reduce_value = Tacred.compute

let get_ts env = Conv_oracle.get_transp_state (Environ.oracle env)

(** returns the i-th position of constructor c (starting from 0) *)
let get_constructor_pos c = let (_, pos), _ = destConstruct c in pos-1

module MetaCoqNames = struct
  let metaCoq_module_name = "Mtac2.Base"
  let mkConstr e = Constr.mkConstr (metaCoq_module_name ^ "." ^ e)
  let mkBuilder e = ConstrBuilder.from_string (metaCoq_module_name ^ "." ^ e)
  let mkT_lazy = mkConstr "M.t"
  let mkUConstr e = Constr.mkUConstr (metaCoq_module_name ^ "." ^ e)

  let isConstr e =
    let c = Lazy.force (mkConstr e) in
    eq_constr c

  let mkCase ind v ret branch sigma env =
    let sigma, c = mkUConstr "mkCase" sigma env in
    sigma, mkApp(c, [|ind;v;ret;branch|])

  let mkelem d sigma env =
    let sigma, c = mkUConstr "elem" sigma env in
    sigma, mkApp(c, [|d|])

  let mkdyn = mkUConstr "dyn"

  let mkDyn ty el sigma env =
    let sigma, c = mkUConstr "Dyn" sigma env in
    sigma, mkApp(c, [|ty;el|])

  (* dyn is expected to be Dyn ty el *)
  let get_elem dyn = (snd (destApp dyn)).(1)
end

open MetaCoqNames

module RedList = GenericList (struct
    let nilname = metaCoq_module_name ^ ".rlnil"
    let consname = metaCoq_module_name ^ ".rlcons"
    let typename = metaCoq_module_name ^ ".rllist"
  end)


module Goal = struct

  let mkgoal = mkUConstr "goal"
  let mkGoal = mkUConstr "Goal"
  let mkAHyp = mkUConstr "AHyp"

  let mkTheGoal ty ev sigma env =
    let sigma, tg = mkGoal sigma env in
    sigma, mkApp (tg, [|ty;ev|])

  let mkAHypOrDef (name, odef, ty) body sigma env =
    (* we are going to wrap the body in a function, so we need to lift
       the indices. we also replace the name with index 1 *)
    let body = replace_term (mkVar name) (mkRel 1) (Vars.lift 1 body) in
    let odef_coq = CoqOption.to_coq ty odef in
    let sigma, ahyp = mkAHyp sigma env in
    sigma, mkApp (ahyp, [|ty; odef_coq; mkLambda(Name name,ty,body)|])

  (* it assumes goal is of type goal *)
  let evar_of_goal sigma env =
    let rec eog goal =
      let (c, args) = decompose_appvect goal in
      if isConstruct c then
        match get_constructor_pos c with
        | 0 -> (* AGoal *)
            let evar = whd_evar sigma args.(1) in
            if isEvar evar then
              Some (fst (destEvar evar))
            else (* it is defined *)
              None
        | 1 -> (* AHyp *)
            let func = args.(2) in
            if isLambda func then
              let (_, _, body) = destLambda func in
              eog body
            else
              None
        | 2 -> (* RemHyp *)
            eog args.(2)
        | _ -> failwith "Should not happen"
      else
        CErrors.error "Not a goal"
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
            let nd2 = Declaration.map_type (Reductionops.nf_evar sigma) nd2 in
            if Declaration.equal nd1 nd2 then
              remove (evenv, env)
            else
              l1
        | l1, _ -> l1 in
      List.rev (remove (List.rev evenv, List.rev (named_context env))) in
    let ids = List.map (fun v -> mkVar (Declaration.get_id v)) evenv in
    let evar = (ev, Array.of_list ids) in
    let sigma, tg = mkTheGoal (Evd.existential_type sigma evar) (mkEvar evar) sigma env in
    fold_inside (fun (sigma,s) v -> mkAHypOrDef (Declaration.to_tuple v) s sigma env) newenv ~init:(sigma,tg)

end

let constr_to_string t = string_of_ppcmds (Termops.print_constr t)
let constr_to_string_env env t = string_of_ppcmds (Termops.print_constr_env env t)

module Exceptions = struct

  let mkCannotRemoveVar env x =
    let varname = CoqString.to_coq (constr_to_string_env env x) in
    mkApp(Lazy.force (mkConstr "CannotRemoveVar"), [|varname|])

  let mkRefNotFound s =
    let msg = CoqString.to_coq s in
    mkApp (Lazy.force (mkConstr "RefNotFound"), [|msg|])

  let mkTermNotGround () = Lazy.force (mkConstr "TermNotGround")
  let mkWrongTerm () = Lazy.force (mkConstr "WrongTerm")
  let mkHypMissesDependency () = Lazy.force (mkConstr "HypMissesDependency")
  let mkTypeMissesDependency () = Lazy.force (mkConstr "TypeMissesDependency")
  let mkAbsDependencyError () = Lazy.force (mkConstr "AbsDependencyError")
  let mkExceptionNotGround () = Lazy.force (mkConstr "ExceptionNotGround")
  let mkDuplicatedVariable () = Lazy.force (mkConstr "DuplicatedVariable")
  let mkNotAVar () = Lazy.force (mkConstr "NotAVar")
  let mkStuckTerm () = Lazy.force (mkConstr "StuckTerm")
  let mkNotAList () = Lazy.force (mkConstr "NotAList")
  let mkNotAMatchExp () = Lazy.force (mkConstr "NotAMatchExp")
  let mkVarAppearsInValue () = Lazy.force (mkConstr "VarAppearsInValue")
  let mkNotAReference ty t =
    mkApp (Lazy.force (mkConstr "NotAReference"), [|ty; t|])
  let mkAlreadyDeclared  name =
    mkApp (Lazy.force (mkConstr "AlreadyDeclared"), [|name|])
  let mkTypeErrorUnboundVar () = Lazy.force (mkConstr "UnboundVar")

  let mkLtacError msg =
    let e = mkConstr "LtacError" in
    let coqmsg = CoqString.to_coq msg in
    mkApp(Lazy.force e, [|coqmsg|])

  (* HACK: we put Prop as the type of the raise. We can put an evar, but
     what's the point anyway? *)
  let mkRaise e =
    let c = Lazy.force (mkConstr "raise") in
    let a = Lazy.force (mkConstr e) in
    mkApp(c, [|mkProp; a|])

  let mkNameExists s = mkApp (Lazy.force (mkConstr "NameExistsInContext"), [|s|])

  let block = CErrors.error
end

module E = Exceptions

module ReductionStrategy = struct
  open MetaCoqNames
  open Reductionops
  open CClosure
  open CClosure.RedFlags
  open Context

  let isReduce c = isConstr "reduce" c

  let has_definition ts env t =
    if isVar t then
      let var = destVar t in
      if not (is_transparent_variable ts var) then
        false
      else
        let n = Environ.lookup_named var env in
        Option.has_some (Named.Declaration.get_value n)
    else if isRel t then
      let n = destRel t in
      let n = Environ.lookup_rel n env in
      Option.has_some (Rel.Declaration.get_value n)
    else if isConst t then
      let (c, _) = destConst t in
      is_transparent_constant ts c && Environ.evaluable_constant c env
    else
      false

  let get_definition env t =
    if isVar t then
      let var = destVar t in
      let n = Environ.lookup_named var env in
      match Named.Declaration.get_value n with
      | Some c -> c
      | _ -> CErrors.anomaly (Pp.str "get_definition for var didn't have definition!")
    else if isRel t then
      let n = destRel t in
      let d = Environ.lookup_rel n env in
      match Rel.Declaration.get_value d with
      | Some v -> (Vars.lift n) v
      | _ -> CErrors.anomaly (Pp.str "get_definition for rel didn't have definition!")
    else if isConst t then
      let c = destConst t in
      let (d,_) = Environ.constant_value env c in
      d
    else
      CErrors.anomaly (Pp.str "get_definition didn't have definition!")

  let try_unfolding ts env t =
    if has_definition ts env t then
      get_definition env t
    else
      t

  let one_step env sigma c =
    let ts = get_ts env in
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

  let redflags = [|fBETA;fDELTA;fMATCH;fFIX;fZETA|]
  let posDeltaC = Array.length redflags
  let posDeltaX = posDeltaC + 1
  let posDeltaOnly = posDeltaX + 1
  let posDeltaBut = posDeltaOnly + 1

  let get_flags (env, _ as ctx) flags =
    (* we assume flags have the right type and are in nf *)
    let flags = RedList.from_coq ctx flags in
    List.fold_right (fun f reds->
      if isConstruct f then
        let ci = get_constructor_pos f in
        if ci < Array.length redflags then
          red_add reds redflags.(ci)
        else if ci = posDeltaC then
          red_add_transparent reds Names.cst_full_transparent_state
        else if ci = posDeltaX then
          red_add_transparent reds Names.var_full_transparent_state
        else
          failwith "Unknown flag"
      else if isApp f then
        let c, args = destApp f in
        if isConstruct c && Array.length args = 1 then
          let reds, func =
            if get_constructor_pos c = posDeltaOnly then
              red_add_transparent (red_add reds fDELTA) all_opaque,
              red_add
            else (* must be posDeltaBut *)
              red_add_transparent reds
                (Conv_oracle.get_transp_state (Environ.oracle env)),
              red_sub in
          let ids = RedList.from_coq_conv ctx get_elem args.(0) in
          List.fold_right (fun e reds->
            if isVar e then
              func reds (fVAR (destVar e))
            else if isConst e then
              func reds (fCONST (fst (destConst e)))
            else
              failwith "Unknown reference") ids reds
        else
          failwith "Unknown flag"
      else
        failwith "Unknown flag"
    ) flags no_red

  let redfuns = [|
    (fun _ _ _ c -> c);
    (fun _ env sigma c -> Tacred.simpl env sigma (nf_evar sigma c));
    (fun _ ->one_step);
    (fun fs env sigma c->
       let evars ev = safe_evar_value sigma ev in
       whd_val
         (create_clos_infos ~evars (get_flags (env, sigma) fs.(0)) env)
         (inject c));
    (fun fs env sigma->
       clos_norm_flags (get_flags (env, sigma) fs.(0)) env sigma);
    (fun _ -> Redexpr.cbv_vm) (* vm_compute *)
  |]

  let reduce sigma env strategy c =
    let strategy, args = decompose_appvect strategy in
    redfuns.(get_constructor_pos strategy) args env sigma c

  let whdfun flags env sigma c =
    let evars = safe_evar_value sigma in
    whd_val
      (create_clos_infos ~evars flags env)
      (inject c)

  let whd_betadeltaiota_nolet = whdfun CClosure.allnolet

  let whd_betadeltaiota = whdfun CClosure.all

  let whd_betadelta = whdfun (red_add beta fDELTA)

  let whd_betaiotazeta = whdfun betaiotazeta

  let whd_betaiota = whdfun betaiota

end

module RE = ReductionStrategy

module UnificationStrategy = struct
  open Evarsolve

  let find_pbs sigma evars =
    let (_, pbs) = extract_all_conv_pbs sigma in
    List.filter (fun (_,_,c1,c2) ->
      List.exists (fun e ->
        Termops.occur_term e c1 || Termops.occur_term e c2) evars) pbs

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
    let pos = get_constructor_pos strategy in
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

let (>>=) v g =
  match v with
  | Val v' -> g v'
  | _ -> v

let return s t = Val (s, t)

let fail s t = Err (s, t)

let print env sigma s =
  Feedback.msg_notice (app (str "[DEBUG] ")
                         (str (CoqString.from_coq (env, sigma) s)))

let mysubstn t n c =
  let rec substrec in_arr depth c = match kind_of_term c with
    | Rel k    ->
        if k<=depth then c
        else if k = depth+n then
          Vars.lift depth t
        else mkRel (k+1)
    | _ -> map_constr_with_binders succ (substrec in_arr) depth c in
  substrec false 0 c

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
    let t = RE.whd_betadelta env sigma t in
    let (info, return_type, discriminant, branches) = Term.destCase t in
    let sigma, branch_dyns = Array.fold_right (
      fun t (sigma,l) ->
        let dyn_type = Retyping.get_type_of env sigma t in
        let sigma, cdyn = mkDyn dyn_type t sigma env in
        sigma, CoqList.mkCons dyn cdyn l
    ) branches (sigma, CoqList.mkNil dyn) in
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

let make_Case (env, sigma) case =
  let open Lazy in
  let open Term in
  let (_, args) = decompose_appvect case in
  let repr_ind = args.(0) in
  let repr_val = args.(1) in
  let repr_return = get_elem args.(2) in
  let repr_branches = CoqList.from_coq_conv (env, sigma) get_elem args.(3) in
  let t_type, l = decompose_appvect repr_ind in
  if isInd t_type then
    match kind_of_term t_type with
    | Ind ((mind, ind_i), _) ->
        let case_info = Inductiveops.make_case_info env (mind, ind_i) LetPatternStyle in
        let match_term = mkCase (case_info, repr_return, repr_val,
                                 (Array.of_list repr_branches)) in
        let match_type = Retyping.get_type_of env sigma match_term in
        mkDyn match_type match_term sigma env
    | _ -> assert false
  else
    Exceptions.block "case_type is not an inductive type"


let get_Constrs (env, sigma) t =
  let t_type, args = Term.decompose_app (RE.whd_betadeltaiota env sigma t) in
  if Term.isInd t_type then
    let (mind, ind_i), _ = destInd t_type in
    let mbody = Environ.lookup_mind mind env in
    let ind = Array.get (mbody.mind_packets) ind_i in
    let sigma, dyn = mkdyn sigma env in
    let args = CList.firstn mbody.mind_nparams_rec args in
    let sigma, l = Array.fold_right
                     (fun i (sigma, l) ->
                        let constr = Names.ith_constructor_of_inductive (mind, ind_i) i in
                        let coq_constr = Term.applist (Term.mkConstruct constr, args) in
                        let ty = Retyping.get_type_of env sigma coq_constr in
                        let sigma, dyn_constr = mkDyn ty coq_constr sigma env in
                        sigma, CoqList.mkCons dyn dyn_constr l
                     )
                     (* this is just a dirty hack to get the indices of constructors *)
                     (Array.mapi (fun i t -> i+1) ind.mind_consnames)
                     (sigma, CoqList.mkNil dyn)
    in
    let indty = Term.applist (t_type, args) in
    let indtyty = Retyping.get_type_of env sigma indty in
    let sigma, indtydyn = mkDyn indtyty indty sigma env in
    let pair = CoqPair.mkPair dyn (CoqList.mkType dyn) indtydyn l in
    (sigma, pair)
  else
    Exceptions.block "The argument of Mconstrs is not an inductive type"

module Hypotheses = struct

  let ahyp_constr = mkBuilder "ahyp"

  let mkAHyp ty n t =
    let t = match t with
      | None -> CoqOption.mkNone ty
      | Some t -> CoqOption.mkSome ty t
    in ConstrBuilder.build_app ahyp_constr [|ty; n; t|]

  let mkHypType = mkConstr "Hyp"

  let cons_hyp ty n t renv sigma env =
    let hyptype = Lazy.force mkHypType in
    let hyp = mkAHyp ty n t in
    (sigma, CoqList.mkCons hyptype hyp renv)

  exception NotAVariable
  exception NotAHyp
  let from_coq (env, sigma as ctx) c =
    let fvar = fun c ->
      if Term.isVar c then c
      else raise NotAVariable
    in
    let fdecl = CoqOption.from_coq ctx in
    let oargs = ConstrBuilder.from_coq ahyp_constr ctx c in
    match oargs with
    | Some args -> (fvar args.(1), fdecl args.(2), args.(0))
    | None -> raise NotAHyp

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

let name_depends_on deps ty ot =
  let open Idset in let open Termops in
  let vars = collect_vars ty in
  let vars = if Option.has_some ot then
      union (collect_vars (Option.get ot)) vars
    else vars in
  not (is_empty (inter vars deps))

(* given a named_context env and a variable x it returns all the
   (named) variables that depends transitively on x *)
let depends_on env x =
  let open Idset in let open Context.Named in
  let deps = singleton x in
  fold_outside (fun v deps->
    let (n, ot, ty) = Declaration.to_tuple v in
    if name_depends_on deps ty ot then
      Idset.add n deps
    else
      deps) env ~init:deps

let name_deps env x = depends_on (named_context env) x

let compute_deps env x =
  if isVar x then
    let name = destVar x in
    name_deps env name
  else
    failwith "check_dependencies should not be called with not a var or rel"

(* given a rel or var x and a term t and its type ty, it checks if t or ty does not depend on x *)
let check_abs_deps env x t ty =
  let ndeps = compute_deps env x in
  let open Idset in
  is_empty ndeps ||
  (* The term might depend on x, which by invariant we now is a
     variable (since ndeps is not empty) *)
  (subset (inter (collect_vars t) ndeps) (singleton (destVar x)) &&
   is_empty (inter (collect_vars ty) ndeps))

(* check if x \not\in FV(t) union FV(env) *)
let check_dependencies env x t =
  if isVar x then
    let name = destVar x in
    not (Termops.occur_var env name t) && not (name_occurn_env env name)
  else
    failwith "check_dependencies should not be called with not a var or rel"


(** Abstract *)
type abs = AbsProd | AbsFun | AbsLet | AbsFix

let rec n_prods env sigma ty = function
  | 0 -> true
  | n ->
      let ty = RE.whd_betadeltaiota env sigma ty in
      if isProd ty then
        let _, _, b = destProd ty in
        n_prods env sigma b (n-1)
      else
        false

(** checks if (option) definition od and type ty has named
    vars included in vars *)
let check_vars od ty vars =
  Idset.subset (Termops.collect_vars ty) vars &&
  if Option.has_some od then
    Idset.subset (Termops.collect_vars (Option.get od)) vars
  else true

exception MissingDep

(* returns a substitution and an environment such that applying
   the substitution to a term makes the term well typed in the environment *)
let new_env (env, sigma) hyps =
  let _, _, subs, env =
    List.fold_right (fun (var, odef, ty) (idlist, idset, subs, env') ->
      (* remove false dependencies from type and definition *)
      let ty = Reductionops.nf_evar sigma ty in
      let odef = Option.map (Reductionops.nf_evar sigma) odef in
      (* the definition might refer to previously defined indices
         so we perform the substitution *)
      let odef =
        try Option.map (multi_subst subs) odef
        with Not_found -> raise MissingDep
      in
      (* if the variable is named, its type can only refer to named variables.
         note that typing ensures the var has type ty, so its type must
         be defined in the named context *)
      if check_vars odef ty idset then
        let id = destVar var in
        (id::idlist, Idset.add id idset, subs, push_named (Context.Named.Declaration.of_tuple (id, odef, ty)) env')
      else
        raise MissingDep
    ) hyps ([], Idset.empty, [], empty_env)
  in subs, env

let make_evar sigma env ty =
  let open Sigma in
  let sigma = Unsafe.of_evar_map sigma in
  if Term.isSort ty && ty <> mkProp then
    let Sigma ((evar, _), sigma, _) = Evarutil.new_type_evar env sigma Evd.UnivRigid in
    to_evar_map sigma, evar
  else
    let Sigma (evar, sigma, _) = Evarutil.new_evar env sigma ty in
    to_evar_map sigma, evar

let rec get_name (env, sigma) (t: constr) : constr option =
  (* If t is a defined variable it is reducing it *)
  (*  let t = whd_betadeltaiota_nolet env sigma t in *)
  let name =
    if isVar t then Some (Name (destVar t))
    else if isLambda t then
      let (n, _, _) = destLambda t in Some n
    else if isProd t then
      let (n, _, _) = destProd t in Some n
    else if isLetIn t then
      let (n, _, _, _) = destLetIn t in Some n
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
  let h = Term.hash_constr c in
  CoqN.to_coq (Pervasives.abs (h mod size))

(* reflects the hypotheses in [env] in a list of [ahyp] *)
let build_hypotheses sigma env =
  let open Context.Named.Declaration in
  let renv = List.map (fun v->let (n, t, ty) = to_tuple v in (mkVar n, t, ty))
               (named_context env) in
  (* the list is reversed: [H : x > 0, x : nat] *)
  let rec build renv =
    match renv with
    | [] -> let ty = Lazy.force Hypotheses.mkHypType in
        (sigma, CoqList.mkNil ty)
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
  let nx = destVar x in
  let name_env = List.filter (fun decl -> get_id decl <> nx) name_env in
  let env = push_named_context name_env env in
  env, build_hypotheses sigma env (* TODO: we should do something smarter here, rebuilding everything is costly *)

let is_nu env x nus =
  let open Context.Named.Declaration in
  let env = named_context env in
  let nx = destVar x in
  let rec find env i =
    let decl = List.hd env in
    if get_id decl = nx then
      i
    else
      find (List.tl env) (i+1)
  in
  find env 0 < nus

(** declare a definition *)
exception DischargeLocality

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
  let kind_pos = get_constructor_pos kind in
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
  let impls = CoqList.from_coq (env, sigma) impls in
  let impls = List.rev impls in
  let idx = ref (List.length impls) in
  let impls = List.map
                (fun item ->
                   let kind_pos = get_constructor_pos item in
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



type ctxt = {env: Environ.env; renv: constr; sigma: Evd.evar_map; nus: int; hook: constr option;
             fixpoints: Environ.env;
            }

(* the intention of this function was to add the fixpoint context to the
   normal context for retyping. but it seems unnecessary *)
let get_type_of ctxt t =
  (* let env = push_named_context (named_context ctxt.fixpoints) ctxt.env in *)
  Retyping.get_type_of ctxt.env ctxt.sigma t

type vm = Code of constr | Ret of constr | Fail of constr
        | Bind of constr | Try of (Evd.evar_map * constr)
        | Nu of (Evd.evar_map * Names.Id.t)

(* let rec constr_of = function *)
(*   | Code c -> c *)
(*   | Bind (a, _) -> constr_of a *)
(*   | Try (a, _) -> constr_of a *)
(*   | Nu (a, _, _) -> constr_of a *)

(* let rec update_constr c = function *)
(*   | Code _ -> Code c *)
(*   | Bind (a, b) -> Bind (update_constr c a, b) *)
(*   | Try (a, b) -> Try (update_constr c a, b) *)
(*   | Nu (a, s, n) -> Nu (update_constr c a, s, n) *)

let vm_to_string = function
  | Code c -> "Code " ^ constr_to_string c
  | Bind c -> "Bind " ^ constr_to_string c
  | Try (_, c) -> "Try " ^ constr_to_string c
  | Ret c -> "Ret " ^ constr_to_string c
  | Fail c -> "Fail " ^ constr_to_string c
  | Nu _ -> "Nu"

let rec run' ctxt (vms: vm list) =
  (* List.iter (fun vm->Printf.printf "<<< %s :: " (vm_to_string vm)) vms; print_endline ">>>"; *)
  let sigma, env = ctxt.sigma, ctxt.env in
  let vm = hd vms in
  let vms = tl vms in
  match vm, vms with
  | Ret c, [] -> return sigma c
  | Ret c, (Bind b :: vms) -> run' ctxt (Code (mkApp(b, [|c|])) :: vms)
  | Ret c, (Try (_, b) :: vms) -> run' ctxt (Ret c :: vms)
  | Ret c, Nu (sigma', name) :: vms -> (* why the sigma'? *)
      if occur_var env name c then
        run' {ctxt with sigma= sigma'} (Fail (E.mkVarAppearsInValue ()) :: vms)
      else
        run' ctxt (Ret c :: vms)
  | Fail c, [] -> fail sigma c
  | Fail c, (Bind _ :: vms) -> run' ctxt (Fail c :: vms)
  | Fail c, (Try (sigma, b) :: vms) -> run' {ctxt with sigma} (Code (mkApp(b, [|c|]))::vms)
  | Fail c, (Nu _ :: vms) -> run' ctxt (Fail c :: vms)
  | (Bind _ | Fail _ | Nu _ | Try _), _ -> failwith "ouch1"
  | Ret _, (Code _ :: _ | Ret _ :: _ | Fail _ :: _) -> failwith "ouch2"
  | Code t, _ ->
      (* ( match ctxt.hook with *)
      (*   | Some f -> *)
      (*       let t = RE.whd_betaiota env sigma t in *)
      (*       let ty = get_type_of ctxt t in *)
      (*       run' {ctxt with hook = None} (Term.mkApp (f, [|ty; t|])) *)
      (*   | None -> return sigma t *)
      (* ) >>= fun (sigma, t) -> *)
      let upd c = (Code c :: vms) in
      let return sigma c = run' {ctxt with sigma} (Ret c :: vms) in
      let fail sigma c = run' {ctxt with sigma} (Fail c :: vms) in
      let (h, args) = Term.decompose_appvect (RE.whd_betadeltaiota_nolet env sigma t) in
      let nth = Array.get args in
      if Term.isLetIn h then
        let open ReductionStrategy in
        let (_, b, _, t) = Term.destLetIn h in
        let (h, args') = Term.decompose_appvect b in
        if isReduce h && Array.length args' = 3 then
          try
            let b = reduce sigma env (Array.get args' 0) (Array.get args' 2) in
            run' ctxt (upd (Term.mkApp (Vars.subst1 b t, args)))
          with RedList.NotAList l ->
            fail sigma (E.mkNotAList ())
        else
          run' ctxt (upd (Term.mkApp (Vars.subst1 b t, args)))
      else
        let constr c =
          if Term.isConstruct c then
            let ((m, ix), _) = Term.destConstruct c in
            if Names.eq_ind m (fst (Term.destInd (Lazy.force mkT_lazy))) then
              ix
            else -1
          else -1
        in
        match constr h with
        | -1 ->
            begin
              try
                (* search for the variable in the fixpoint context *)
                let n = Term.destVar h in
                match Environ.named_body n ctxt.fixpoints with
                | Some fixbody ->
                    let t = (Term.appvect (fixbody,args)) in
                    run' ctxt (upd t)
                | None -> fail sigma (E.mkStuckTerm ())
              with | Term.DestKO ->
                fail sigma (E.mkStuckTerm ())
            end

        | 1 -> (* ret *)
            return sigma (nth 1)

        | 2 -> (* bind *)
            run' ctxt (Code (nth 2) :: Bind (nth 3) :: vms)

        | 3 -> (* try *)
            run' ctxt (Code (nth 1) :: Try (sigma, nth 2) :: vms)

        | 4 -> (* raise *)
            (* we make sure the exception is a closed term: it does not depend on evars or nus *)
            let term = nf_evar sigma (nth 1) in
            let vars = collect_vars term in
            let nuvars = Context.Named.to_vars (CList.firstn ctxt.nus (named_context env)) in
            let intersect = Id.Set.inter vars nuvars in
            let closed = Id.Set.is_empty intersect && Evar.Set.is_empty (Evarutil.undefined_evars_of_term sigma term) in
            if closed then
              fail sigma term
            else
              fail sigma (E.mkExceptionNotGround ())

        | 5 -> (* fix1 *)
            let a, b, s, i, f, x = nth 0, nth 1, nth 2, nth 3, nth 4, nth 5 in
            run_fix ctxt vms h [|a|] b s i f [|x|]

        | 6 -> (* fix 2 *)
            let a1, a2, b, s, i, f, x1, x2 =
              nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7 in
            run_fix ctxt vms h [|a1; a2|] b s i f [|x1; x2|]

        | 7 -> (* fix 3 *)
            let a1, a2, a3, b, s, i, f, x1, x2, x3 =
              nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7, nth 8, nth 9 in
            run_fix ctxt vms h [|a1; a2; a3|] b s i f [|x1; x2; x3|]

        | 8 -> (* fix 4 *)
            let a1, a2, a3, a4, b, s, i, f, x1, x2, x3, x4 =
              nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7, nth 8, nth 9, nth 10, nth 11 in
            run_fix ctxt vms h [|a1; a2; a3; a4|] b s i f [|x1; x2; x3; x4|]

        | 9 -> (* fix 5 *)
            let a1, a2, a3, a4, a5, b, s, i, f, x1, x2, x3, x4, x5 =
              nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7, nth 8, nth 9, nth 10, nth 11, nth 12, nth 13 in
            run_fix ctxt vms h [|a1; a2; a3; a4; a5|] b s i f [|x1; x2; x3; x4; x5|]

        | 10 -> (* is_var *)
            let e = nth 1 in
            if isVar e then
              return sigma CoqBool.mkTrue
            else
              return sigma CoqBool.mkFalse

        | 11 -> (* nu *)
            let a, s, ot, f = nth 0, nth 2, nth 3, nth 4 in
            let namestr = CoqString.from_coq (env, sigma) s in
            let name = Names.Id.of_string namestr in
            if Id.Set.mem name (vars_of_env env) then
              fail sigma (Exceptions.mkNameExists s)
            else begin
              let fx = Term.mkApp(f, [|Term.mkVar name|]) in
              let ot = CoqOption.from_coq (env, sigma) ot in
              let env = push_named (Context.Named.Declaration.of_tuple (name, ot, a)) env in
              let (sigma, renv) = Hypotheses.cons_hyp a (Term.mkVar name) ot ctxt.renv sigma env in
              run' {ctxt with env; renv; sigma; nus=(ctxt.nus+1)} (Code fx :: Nu (sigma, name) :: vms)
            end

        | 12 -> (* abs *)
            let a, p, x, y = nth 0, nth 1, nth 2, nth 3 in
            abs vms AbsFun ctxt a p x y 0 mkProp

        | 13 -> (* abs_let *)
            let a, p, x, t, y = nth 0, nth 1, nth 2, nth 3, nth 4 in
            abs vms AbsLet ctxt a p x y 0 t

        | 14 -> (* abs_prod *)
            let a, x, y = nth 0, nth 1, nth 2 in
            (* HACK: put mkProp as returning type *)
            abs vms AbsProd ctxt a mkProp x y 0 mkProp

        | 15 -> (* abs_fix *)
            let a, f, t, n = nth 0, nth 1, nth 2, nth 3 in
            let n = CoqN.from_coq (env, sigma) n in
            (* HACK: put mkProp as returning type *)
            abs vms AbsFix ctxt a mkProp f t n mkProp

        | 16 -> (* get_binder_name *)
            let t = nth 1 in
            let s = get_name (env, sigma) t in
            begin
              match s with
              | Some s -> return sigma s
              | None -> fail sigma (Exceptions.mkWrongTerm ())
            end

        | 17 -> (* remove *)
            let x, t = nth 2, nth 3 in
            if isVar x then
              if check_dependencies env x t then
                let nus = if is_nu env x ctxt.nus then ctxt.nus-1 else ctxt.nus in
                let env, (sigma, renv) = env_without sigma env ctxt.renv x in
                run' {ctxt with env; renv; sigma; nus} (upd t)
              else
                fail sigma (E.mkCannotRemoveVar env x)
            else
              fail sigma (E.mkNotAVar ())

        | 18 -> (* evar *)
            let ty, hyp = nth 0, nth 1 in
            cvar vms ctxt ty hyp

        | 19 -> (* is_evar *)
            let e = whd_evar sigma (nth 1) in
            if isEvar e || (isApp e && isEvar (fst (destApp e))) then
              return sigma CoqBool.mkTrue
            else
              return sigma CoqBool.mkFalse

        | 20 -> (* hash *)
            return sigma (hash env sigma (nth 1) (nth 2))

        | 21 -> (* solve_typeclasses *)
            let evd' = Typeclasses.resolve_typeclasses ~fail:false env sigma in
            return evd' CoqUnit.mkTT

        | 22 -> (* print *)
            let s = nth 0 in
            print env sigma s;
            return sigma CoqUnit.mkTT

        | 23 -> (* pretty_print *)
            let t = nth 1 in
            let t = nf_evar sigma t in
            let s = string_of_ppcmds (Termops.print_constr_env env t) in
            return sigma (CoqString.to_coq s)

        | 24 -> (* hypotheses *)
            return sigma ctxt.renv

        | 25 -> (* dest case *)
            let t = nth 1 in
            begin
              match dest_Case (env, sigma) t with
              | Some (sigma', case) -> return sigma' case
              | _ -> fail sigma (E.mkNotAMatchExp ())
            end

        | 26 -> (* get constrs *)
            let t = nth 1 in
            let (sigma', constrs) = get_Constrs (env, sigma) t in
            return sigma' constrs

        | 27 -> (* make case *)
            let case = nth 0 in
            begin
              try
                let (sigma', case) = make_Case (env, sigma) case in
                return sigma' case
              with CoqList.NotAList l ->
                fail sigma (E.mkNotAList ())
            end

        | 28 -> (* munify *)
            let a, x, y, uni = nth 0, nth 1, nth 2, nth 3 in
            let feqT = CoqEq.mkType a x y in
            begin
              let r = UnificationStrategy.unify None sigma env uni Reduction.CONV x y in
              match r with
              | Evarsolve.Success sigma, _ ->
                  let feq = CoqEq.mkEqRefl a x in
                  let someFeq = CoqOption.mkSome feqT feq in
                  return sigma someFeq
              | _, _ ->
                  let none = CoqOption.mkNone feqT in
                  return sigma none
            end

        | 29 -> (* munify_univ *)
            let x, y, uni = nth 0, nth 1, nth 2 in
            let fT = mkProd(Name.Anonymous, x, y) in
            begin
              let r = UnificationStrategy.unify None sigma env uni Reduction.CUMUL x y in
              match r with
              | Evarsolve.Success sigma, _ ->
                  let id = mkLambda(Name.Anonymous,x,mkRel 1) in
                  return sigma (CoqOption.mkSome fT id)
              | _, _ ->
                  return sigma (CoqOption.mkNone fT)
            end

        | 30 -> (* get_reference *)
            let s = CoqString.from_coq (env, sigma) (nth 0) in
            let open Nametab in let open Libnames in
            begin
              try
                let sigma, v = Evd.fresh_global env sigma (locate (qualid_of_string s)) in
                let ty = Retyping.get_type_of env sigma v in
                let sigma, dyn = mkDyn ty v sigma env in
                return sigma dyn
              with _ -> fail sigma (Exceptions.mkRefNotFound s)
            end

        | 31 -> (* get_var *)
            let s = CoqString.from_coq (env, sigma) (nth 0) in
            let open Context.Named in
            begin
              try
                let var = lookup (Id.of_string s) (named_context env) in
                let sigma, dyn = mkDyn (Declaration.get_type var) (mkVar (Declaration.get_id var)) sigma env in
                return sigma dyn
              with _ -> fail sigma (Exceptions.mkRefNotFound s)
            end

        | 32 -> (* call_ltac *)
            let concl, name, args = nth 0, nth 1, nth 2 in
            let args = nf_evar sigma args in
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
                let undef = Evar.Map.domain (Evd.undefined_map sigma) in
                let (c, sigma) = Pfedit.refine_by_tactic env sigma concl (Tacinterp.eval_tactic tac) in
                let new_undef = Evar.Set.diff (Evar.Map.domain (Evd.undefined_map sigma)) undef in
                let new_undef = Evar.Set.elements new_undef in
                let sigma, goal = Goal.mkgoal sigma env in
                let sigma, goals = CoqList.pto_coq goal (fun e sigma->Goal.goal_of_evar env sigma e) new_undef sigma in
                return sigma (CoqPair.mkPair concl goal c goals)
              with CErrors.UserError(s,ppm) ->
                let expl = string_of_ppcmds ppm in
                fail sigma (Exceptions.mkLtacError (s ^ ": " ^ expl))
                 | e ->
                     fail sigma (Exceptions.mkLtacError (Printexc.to_string e))
            end
        (* Tac (sigma, Tacinterp.eval_tactic tac, fun v -> Val v) *)

        | 33 -> (* list_ltac *)
            let aux k _ = Feedback.msg_info (Pp.str (Names.KerName.to_string k)) in
            KNmap.iter aux (Tacenv.ltac_entries ());
            return sigma CoqUnit.mkTT

        | 34 -> (* read_line *)
            return sigma (CoqString.to_coq (read_line ()))

        | 35 -> (* break *)
            run' {ctxt with hook=Some (nth 2)} (upd (nth 4))(*  >>= fun (sigma, _) -> *)
        (* return sigma CoqUnit.mkTT *)

        | 36 -> (* decompose *)
            let (h, args) = decompose_app (nth 1) in
            let sigma, dyn = mkdyn sigma env in
            let listdyn = CoqList.mkType dyn in
            let sigma, dh = mkDyn (get_type_of ctxt h) h sigma env in
            let sigma, args = CoqList.pto_coq dyn (fun t sigma->mkDyn (get_type_of ctxt t) t sigma env) args sigma in
            return sigma (CoqPair.mkPair dyn listdyn dh args)

        | 37 -> (* solve_typeclass *)
            let ty = nth 0 in
            begin
              try
                let sigma, v = Typeclasses.resolve_one_typeclass ~unique:false env sigma  ty in
                return sigma (CoqOption.mkSome ty v)
              with Not_found ->
                return sigma (CoqOption.mkNone ty)
            end

        | 38 -> (* declare definition *)
            let kind, name, opaque, ty, bod = nth 0, nth 1, nth 2, nth 3, nth 4 in
            (try
               let sigma, ret = run_declare_def env sigma kind name (CoqBool.from_coq opaque) ty bod in
               return sigma ret
             with
             | CErrors.AlreadyDeclared _ ->
                 fail sigma (E.mkAlreadyDeclared name)
             | Type_errors.TypeError(env, Type_errors.UnboundVar _) ->
                 fail sigma (E.mkTypeErrorUnboundVar ())
            )

        | 39 -> (* declare implicit arguments *)
            let reference, impls = (*nth 0 is the type *) nth 1, nth 2 in
            (try
               let sigma, ret = run_declare_implicits env sigma reference impls in
               return sigma ret
             with Not_found ->
               fail sigma (E.mkNotAReference (nth 0) reference)
            )

        | 40 -> (* os_cmd *)
            let cmd = CoqString.from_coq (env, sigma) (nth 0) in
            let ret = Sys.command cmd in
            return sigma (CoqZ.to_coq ret)

        | _ ->
            Exceptions.block "I have no idea what is this construct of T that you have here"

(* h is the mfix operator, a is an array of types of the arguments, b is the
   return type of the fixpoint, s is the type to embed M in itself (used only to
   make universes happy), i is the identity to embed S in M, f is the function
   and x its arguments. *)
and run_fix ctxt (vms: vm list) (h: constr) (a: constr array) (b: constr) (s: constr) (i: constr) (f: constr) (x: constr array) =
  (* let fixbody = mkApp(h, Array.append a [|b;s;i|]) in *)
  (* run' ctxt c *)
  let sigma, env = ctxt.sigma, ctxt.env in
  (* let fix_type = Retyping.get_type_of env sigma fixbody in *)
  let name =
    if isVar f then Some (Name (destVar f))
    else if isLambda f then
      let (n, _, _) = destLambda f in Some n
    else if isProd f then
      let (n, _, _) = destProd f in Some n
    else if isLetIn f then
      let (n, _, _, _) = destLetIn f in Some n
    else None
  in
  let name = match name with | Some (Name i) -> Names.Id.to_string i | Some _ -> "anon" | None -> "impossible" in

  let n = Namegen.next_name_away (Name (Names.Id.of_string (concat "mtac_fix_" [name]))) (ids_of_context env) in
  (* let env = push_named (Context.Named.Declaration.of_tuple (n, None, fix_type)) env in *)
  let fixvar = Term.mkVar n in
  let fixf = mkApp(f, [|fixvar|]) in
  (* HACK: we put Prop as the type of fixf in the context, simply because we
     don't care. If it turns out to be problematic, we have to construct its
     type. *)
  let fixpoints = push_named (Context.Named.Declaration.of_tuple (n, Some (fixf), Term.mkProp)) ctxt.fixpoints in
  let c = mkApp (f, Array.append [| fixvar |] x) in
  run' {ctxt with sigma=sigma; env=env; fixpoints=fixpoints} (Code c :: vms)
(* run' ctxt c *)

and
  (* abs case env a p x y n abstract variable x from term y according to the case.
     if variables depending on x appear in y or the type p, it fails. n is for fixpoint. *)
  abs vms case ctxt a p x y n t : data =
  let sigma = ctxt.sigma in
  let a = nf_evar sigma a in
  let p = nf_evar sigma p in
  let x = nf_evar sigma x in
  let y = nf_evar sigma y in
  (* check if the type p does not depend of x, and that no variable
     created after x depends on it.  otherwise, we will have to
     substitute the context, which is impossible *)
  if isVar x then
    if check_abs_deps ctxt.env x y p then
      let name = destVar x in
      let y' = Vars.subst_vars [name] y in
      let t =
        match case with
        | AbsProd -> Term.mkProd (Name name, a, y')
        | AbsFun -> Term.mkLambda (Name name, a, y')
        | AbsLet -> Term.mkLetIn (Name name, t, a, y')
        | AbsFix -> Term.mkFix (([|n-1|], 0), ([|Name name|], [|a|], [|y'|]))
      in
      run' ctxt (Ret t :: vms)
    else
      run' ctxt (Fail (E.mkAbsDependencyError ()) :: vms)
  else
    run' ctxt (Fail (E.mkNotAVar ()) :: vms)

and cvar vms ctxt ty ohyps =
  let env, sigma = ctxt.env, ctxt.sigma in
  let ohyps = CoqOption.from_coq (env, sigma) ohyps in
  if Option.has_some ohyps then
    try
      let hyps = Hypotheses.from_coq_list (env, sigma) (Option.get ohyps) in
      let vars = List.map (fun (v, _, _)->v) hyps in
      if List.distinct vars then
        try
          let subs, env = new_env (env, sigma) hyps in
          let ty = multi_subst subs ty in
          let sigma, evar = make_evar sigma env ty in
          let (e, _) = destEvar evar in
          (* the evar created by make_evar has id in the substitution
             but we need to remap it to the actual variables in hyps *)
          run' {ctxt with sigma} (Ret (mkEvar (e, Array.of_list vars)) :: vms)
        with
        | MissingDep ->
            run' ctxt (Fail (E.mkHypMissesDependency ()) :: vms)
        | Not_found ->
            run' ctxt (Fail (E.mkTypeMissesDependency ()) :: vms)
      else
        run' ctxt (Fail (E.mkDuplicatedVariable ()) :: vms)
    with Hypotheses.NotAVariable ->
      run' ctxt (Fail (E.mkNotAVar ()) :: vms)
  else
    let sigma, evar = make_evar sigma env ty in
    run' {ctxt with sigma} (Ret evar :: vms)



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
      let metas = List.fold_right (fun var metas ->
        let (_, body, ty) = Context.Named.Declaration.to_tuple var in
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

(* returns the enviornment and substitution without db rels *)
let db_to_named env =
  let open Context in
  let env' = push_named_context (named_context env) (reset_context env) in
  let vars = Id.Set.elements (Named.to_vars (named_context env)) in
  let _, subs, env = CList.fold_right_i (fun n var (vars, subs, env') ->
    (* the definition might refer to previously defined indices
       so we perform the substitution *)
    let (name, odef, ty) = Rel.Declaration.to_tuple var in
    let odef = Option.map (multi_subst subs) odef in
    let ty = multi_subst subs ty in
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
let multi_subst_inv l c =
  let l = List.map (fun (a, b) -> (b, a)) l in
  let rec substrec depth c = match kind_of_term c with
    | Var n ->
        begin
          try mkRel (List.assoc (mkVar n) l + depth)
          with Not_found -> mkVar n
        end
    | _ -> map_constr_with_binders succ substrec depth c in
  substrec 0 c

let run (env, sigma) t =
  let subs, env = db_to_named env in
  let t = multi_subst subs (nf_evar sigma t) in
  let (sigma, renv) = build_hypotheses sigma env in
  match run' {env; renv; sigma; nus=0;hook=None; fixpoints=Environ.empty_env} (Code t :: []) with
  | Err (sigma', v) ->
      Err (sigma', multi_subst_inv subs (nf_evar sigma' v))
  | Val (sigma', v) ->
      Val (sigma', multi_subst_inv subs (nf_evar sigma' v))

(** set the run function in unicoq *)
let _ = Munify.set_lift_constr (MetaCoqNames.mkConstr "lift")
let _ = Munify.set_run (fun env sigma t ->
  match run (env, sigma) t with
  | Err _ -> None
  | Val c -> Some c)
