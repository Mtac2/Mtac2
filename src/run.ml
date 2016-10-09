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

let get_ts env = Conv_oracle.get_transp_state (Environ.oracle env)

(** returns the i-th position of constructor c (starting from 0) *)
let get_constructor_pos c = let (_, pos), _ = destConstruct c in pos-1

module MetaCoqNames = struct
  let metaCoq_module_name = "MetaCoq.Mtac"
  let mkConstr e = Constr.mkConstr (metaCoq_module_name ^ "." ^ e)
  let mkBuilder e = ConstrBuilder.from_string (metaCoq_module_name ^ "." ^ e)
  let mkT_lazy = mkConstr "Mtac"
  let mkUConstr e = (Constr.mkUConstr (metaCoq_module_name ^ "." ^ e))

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

end

open MetaCoqNames

module Goal = struct

  let goal = mkUConstr "goal"

  let mkTheGoal ty ev sigma env =
    let sigma, tg = mkUConstr "Goal" sigma env in
    sigma, mkApp (tg, [|ty;ev|])

  let mkAHypOrDef ty name odef body sigma env =
    (* we are going to wrap the body in a function, so we need to lift
       the indices. we also replace the name with index 1 *)
    let body = replace_term (mkVar name) (mkRel 1) (Vars.lift 1 body) in
    let odef_coq = CoqOption.to_coq ty odef in
    let sigma, ahyp = mkUConstr "AHyp" sigma env in
    sigma, mkApp (ahyp, [|ty; odef_coq; mkLambda(Name name,ty,body)|])

  let goal_of_evar (env:env) sigma ev =
    let evinfo = Evd.find_undefined sigma ev in
    let evenv = named_context_of_val (evar_hyps evinfo) in
    (* we remove the elements in the hypotheses that are shared with
       the current env (old to new). *)
    let newenv =
      let rec remove = function
        | (nd1 :: evenv) as l1, (nd2 :: env) ->
            if Context.eq_named_declaration nd1 nd2 then
              remove (evenv, env)
            else
              l1
        | l1, _ -> l1 in
      List.rev (remove (List.rev evenv, List.rev (named_context env))) in
    let ids = Context.fold_named_context (fun (n,_,_) s -> mkVar n :: s) evenv ~init:[] in
    let evar = (ev, Array.of_list ids) in
    let sigma, tg = mkTheGoal (Evd.existential_type sigma evar) (mkEvar evar) sigma env in
    Context.fold_named_context_reverse (fun (sigma,s) (n,odef,ty) -> mkAHypOrDef ty n odef s sigma env) newenv ~init:(sigma,tg)

end

let constr_to_string t = string_of_ppcmds (Termops.print_constr t)
let constr_to_string_env env t = string_of_ppcmds (Termops.print_constr_env env t)

module Exceptions = struct

  let mkFailure s =
    let msg = CoqString.to_coq s in
    mkApp (Lazy.force (mkConstr "Failure"), [|msg|])

  let mkCannotRemoveVar env x =
    let varname = CoqString.to_coq (constr_to_string_env env x) in
    mkApp(Lazy.force (mkConstr "CannotRemoveVar"), [|varname|])

  let mkTermNotGround = mkConstr "TermNotGround"
  let mkWrongTerm = mkConstr "WrongTerm"
  let mkHypMissesDependency = mkConstr "HypMissesDependency"
  let mkTypeMissesDependency = mkConstr "TypeMissesDependency"
  let mkLtacError (s, ppm) =
    let e = mkConstr "LtacError" in
    let expl = string_of_ppcmds ppm in
    let coqexp = CoqString.to_coq (s ^ ": " ^ expl) in
    mkApp(Lazy.force e, [|coqexp|])

  (* HACK: we put Prop as the type of the raise. We can put an evar, but
     what's the point anyway? *)
  let mkRaise e =
    let c = Lazy.force (mkConstr "raise") in
    let a = Lazy.force (mkConstr e) in
    mkApp(c, [|mkProp; a|])

  let mkNameExists s = mkApp (Lazy.force (mkConstr "NameExistsInContext"), [|s|])

  let mkExceptionNotGround env term =
    let e = mkConstr "ExceptionNotGround" in
    let s = string_of_ppcmds (Termops.print_constr_env env term) in
    let coqexp = CoqString.to_coq s in
    mkApp(Lazy.force e, [|coqexp|])

  let error_stuck t = "Cannot reduce term, perhaps an opaque definition? " ^ constr_to_string t
  let error_param env n t = "Parameter " ^ n ^ " appears in value " ^ constr_to_string_env env t
  let error_abs env x = "Cannot abstract non variable " ^ (constr_to_string_env env x)
  let error_abs_env env x t ty = "Cannot abstract "  ^ (constr_to_string_env env x) ^ " from " ^ (constr_to_string_env env t) ^ " of type " ^ (constr_to_string_env env ty)
  let error_abs_let = "Trying to let-abstract a variable without definition"
  let error_abs_let_noconv env t t' = "Definition " ^ (constr_to_string_env env t) ^ " must be convertible to " ^ (constr_to_string_env env t')
  let error_abs_fix env ty n = "The type of the fixpoint " ^ (constr_to_string_env env ty) ^ " must have " ^ (string_of_int n) ^ " products"
  let remove_var env x = "Term must be a variable " ^ constr_to_string_env env x
  let unknown_reduction_strategy = "Unknown reduction strategy"

  let block = Errors.error
end

module E = Exceptions

module ReductionStrategy = struct
  open MetaCoqNames
  open Reductionops
  open Closure
  open Closure.RedFlags

  let isReduce c = isConstr "reduce" c

  let has_definition ts env t =
    if isVar t then
      let var = destVar t in
      if not (is_transparent_variable ts var) then
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
      is_transparent_constant ts c && Environ.evaluable_constant c env
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

  let redflags = [|fBETA;fDELTA;fIOTA;fZETA|]

  let get_flags ctx flags =
    (* HACK for unfolding only constants we need to add it afterwards*)
    let deltac = ref false in
    let deltax = ref false in
    (* we assume flags have the right type and are in nf *)
    let flags = CoqList.from_coq_conv ctx (fun f->
      let ci = get_constructor_pos f in
      if ci < Array.length redflags then
        redflags.(ci)
      else begin
        if ci = Array.length redflags then
          deltac := true
        else
          deltax := true;
        raise CoqList.Skip
      end
    ) flags in
    let reds = mkflags flags in
    let reds =
      if !deltac then
        red_add_transparent reds Names.cst_full_transparent_state
      else
        reds
    in
    if !deltax then
      red_add_transparent reds Names.var_full_transparent_state
    else
      reds

  let redfuns = [|
    (fun _ _ _ c -> c);
    (fun _ -> Tacred.simpl);
    (fun _ ->one_step);
    (fun fs env sigma c->
       let evars ev = safe_evar_value sigma ev in
       whd_val
         (create_clos_infos ~evars (get_flags (env, sigma) fs.(0)) env)
         (inject c));
    (fun fs env sigma c->
       let evars ev = safe_evar_value sigma ev in
       norm_val
         (create_clos_infos ~evars (get_flags (env, sigma) fs.(0)) env)
         (inject c))
  |]

  let reduce sigma env strategy c =
    let strategy, args = decompose_appvect strategy in
    redfuns.(get_constructor_pos strategy) args env sigma c

end

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

let print env sigma s = Printf.printf "[DEBUG] %s\n"
                          (CoqString.from_coq (env, sigma) s)

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


let dest_Case (env, sigma) t =
  let sigma, dyn = mkdyn sigma env in
  try
    let t = whd_betadelta env sigma t in
    let (info, return_type, discriminant, branches) = Term.destCase t in
    let sigma, branch_dyns = Array.fold_right (
      fun t (sigma,l) ->
        let dyn_type = Retyping.get_type_of env sigma t in
        let sigma, cdyn = mkDyn dyn_type t sigma env in
        sigma, CoqList.makeCons dyn cdyn l
    ) branches (sigma, CoqList.makeNil dyn) in
    let ind_type = Retyping.get_type_of env sigma discriminant in
    let return_type_type = Retyping.get_type_of env sigma return_type in
    let sigma, ret_dyn = mkDyn return_type_type return_type sigma env in
    mkCase ind_type discriminant ret_dyn branch_dyns sigma env
  with
  | Not_found ->
      Exceptions.block "Something specific went wrong. TODO: find out what!"
  | Term.DestKO ->
      Exceptions.block "This is not a case construct."
  | _ ->
      Exceptions.block "Something not so specific went wrong."

let make_Case (env, sigma) case =
  let open Lazy in
  let open Term in
  let sigma, case_ind = mkUConstr "case_ind" sigma env in
  let sigma, case_val = mkUConstr "case_val" sigma env in
  let sigma, case_return = mkUConstr "case_return" sigma env in
  let sigma, case_branches = mkUConstr "case_branches" sigma env in
  let repr_ind = mkApp(case_ind, [|case|]) in
  let repr_val = mkApp(case_val, [|case|]) in
  let repr_val_red = whd_betadeltaiota env sigma repr_val in
  let repr_return = mkApp(case_return, [|case|]) in
  let sigma, repr_return_unpack = mkelem repr_return sigma env in
  let repr_return_red = whd_betadeltaiota env sigma repr_return_unpack in
  let repr_branches = mkApp(case_branches, [|case|]) in
  let repr_branches_list = CoqList.from_coq (env, sigma) repr_branches in
  let rsigma = ref sigma in
  let repr_branches_dyns =
    List.map (fun t ->
      let sigma, c = mkelem t !rsigma env in
      rsigma := sigma;
      c) repr_branches_list in
  let sigma = !rsigma in
  let repr_branches_red =
    List.map (fun t -> whd_betadeltaiota env sigma t) repr_branches_dyns in
  let t_type, l = decompose_app (whd_betadeltaiota env sigma repr_ind) in
  if isInd t_type then
    match kind_of_term t_type with
    | Ind ((mind, ind_i), _) ->
        let case_info = Inductiveops.make_case_info env (mind, ind_i) LetPatternStyle in
        let match_term = mkCase (case_info, repr_return_red, repr_val_red,
                                 Array.of_list (repr_branches_red)) in
        let match_type = Retyping.get_type_of env sigma match_term in
        mkDyn match_type match_term sigma env
    | _ -> assert false
  else
    Exceptions.block "case_type is not an inductive type"


let get_Constrs (env, sigma) t =
  let t_type, args = Term.decompose_app (whd_betadeltaiota env sigma t) in
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
                        sigma, CoqList.makeCons dyn dyn_constr l
                     )
                     (* this is just a dirty hack to get the indices of constructors *)
                     (Array.mapi (fun i t -> i+1) ind.mind_consnames)
                     (sigma, CoqList.makeNil dyn)
    in
    let indty = Term.applist (t_type, args) in
    let indtyty = Retyping.get_type_of env sigma indty in
    let sigma, indtydyn = mkDyn indtyty indty sigma env in
    let pair = CoqPair.mkPair dyn (CoqList.makeType dyn) indtydyn l in
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
    (sigma, CoqList.makeCons hyptype hyp renv)

  exception NotAVariable
  let from_coq (env, sigma as ctx) c =
    let fvar = fun c ->
      if Term.isVar c || isRel c then c
      else raise NotAVariable
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

let name_depends_on deps ty ot =
  let open Idset in let open Termops in
  let vars = collect_vars ty in
  let vars = if Option.has_some ot then
      union (collect_vars (Option.get ot)) vars
    else vars in
  not (is_empty (inter vars deps))

let index_depends_on deps ty ot =
  let open Int.Set in let open Termops in
  let rels = free_rels ty in
  let rels = if Option.has_some ot then
      union (free_rels (Option.get ot)) rels
    else rels in
  not (is_empty (inter rels deps))

let int_set_map f =
  let open Int.Set in
  fold (fun e ->add (f e)) empty

(* given a named_context env and a variable x it returns all the
   (named) variables that depends transitively on x *)
let depends_on env x =
  let open Idset in
  let deps = singleton x in
  Context.fold_named_context (fun (n, ot, ty) deps->
    if name_depends_on deps ty ot then
      add n deps
    else
      deps) env ~init:deps

let name_deps env x =
  let rel_env = rel_context env in
  let deps = depends_on (named_context env) x in
  let ixdeps = Context.fold_rel_context (fun (_, ot, ty) ixdeps ->
    (* we have to return the set increased by 1 to make sure all the
       indices are right when we return it *)
    let ixdeps' = int_set_map (fun n->n+1) ixdeps in
    if name_depends_on deps ty ot || index_depends_on ixdeps ty ot then
      Int.Set.add 1 ixdeps'
    else
      ixdeps') ~init:(Int.Set.empty) rel_env in
  (deps, ixdeps)

let index_deps env ix =
  let env = pop_rel_context ix env in
  let rel_env = rel_context env in
  Context.fold_rel_context (fun (_, ot, ty) ixdeps ->
    (* we have to return the set increased by 1 to make sure all the
       indices are right when we return it *)
    let ixdeps' = int_set_map (fun n->n+1) ixdeps in
    if index_depends_on ixdeps ty ot then
      Int.Set.add 1 ixdeps'
    else
      ixdeps') ~init:(Int.Set.singleton 1) rel_env

let compute_deps env x =
  if isRel x then
    let rel = destRel x in
    (Idset.empty, index_deps env rel)
  else if isVar x then
    let name = destVar x in
    name_deps env name
  else
    failwith "check_dependencies should not be called with not a var or rel"

(* given a rel or var x and a term t and its type ty, it checks if t or ty does not depend on x *)
let check_abs_deps env x t ty =
  let (ndeps, ixdeps) = compute_deps env x in
  let b = let open Idset in
    is_empty ndeps ||
    (* The term might depend on x, which by invariant we now is a
       variable (since ndeps is not empty) *)
    (subset (inter (collect_vars t) ndeps) (singleton (destVar x)) &&
     is_empty (inter (collect_vars ty) ndeps)) in
  let open Int.Set in
  let base_set = if isRel x then singleton (destRel x) else empty in
  b && subset (inter (free_rels t) ixdeps) base_set &&
  is_empty (inter (free_rels ty) ixdeps)

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

let rec n_prods env sigma ty = function
  | 0 -> true
  | n ->
      let ty = whd_betadeltaiota env sigma ty in
      if isProd ty then
        let _, _, b = destProd ty in
        n_prods env sigma b (n-1)
      else
        false

(* abs case env a p x y n abstract variable x from term y according to the case.
   if variables depending on x appear in y or the type p, it fails. n is for fixpoint. *)
let abs case (env, sigma) a p x y n t : data =
  (* check if the type p does not depend of x, and that no variable
     created after x depends on it.  otherwise, we will have to
     substitute the context, which is impossible *)
  if isRel x || isVar x then
    if check_abs_deps env x y p then
      if isRel x then
        let rel = destRel x in
        let (name, _, _) = lookup_rel rel env in
        let y' = mysubstn (mkRel 1) rel y in
        let t =
          match case with
          | AbsProd -> Term.mkProd (name, a, y')
          | AbsFun -> Term.mkLambda (name, a, y')
          | AbsLet -> Term.mkLetIn (name, t, a, y')
          | AbsFix ->
              if n_prods env sigma a n then
                Term.mkFix (([|n-1|], 0), ([|name|], [|a|], [|y'|]))
              else
                E.mkFailure (E.error_abs_fix env a n)
        in
        return sigma t
      else
        let name = destVar x in
        let y' = Vars.subst_vars [name] y in
        let t =
          match case with
          | AbsProd -> Term.mkProd (Name name, a, y')
          | AbsFun -> Term.mkLambda (Name name, a, y')
          | AbsLet -> Term.mkLetIn (Name name, t, a, y')
          | AbsFix -> Term.mkFix (([|n-1|], 0), ([|Name name|], [|a|], [|y'|]))
        in
        return sigma t
    else
      fail sigma (E.mkFailure (Exceptions.error_abs_env env x t p))
  else
    fail sigma (E.mkFailure (Exceptions.error_abs env x))

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
      if isRel var then
        let n = destRel var in
        let name, _, _ = List.nth (rel_context env) (n-1) in
        (* since the name can be Anonymous, we need to generate a name *)
        let id = Namegen.next_name_away name idlist in
        (* if the variable is an index, its type might
           refer to other indices, so we need to substitute *)
        let ty =
          try multi_subst subs ty
          with Not_found -> raise MissingDep
        in
        let b = check_vars odef ty idset in
        if b then
          (id::idlist, Idset.add id idset, (n, mkVar id) :: subs, push_named (id, odef, ty) env')
        else
          raise MissingDep
      else
        (* if the variable is named, its type can only refer to named variables.
           note that typing ensures the var has type ty, so its type must
           be defined in the named context *)
        let id = destVar var in
        if check_vars odef ty idset then
          (id::idlist, Idset.add id idset, subs, push_named (id, odef, ty) env')
        else
          raise MissingDep
    ) hyps ([], Idset.empty, [], empty_env)
  in subs, env

let make_evar sigma env ty =
  if Term.isSort ty && ty <> mkProp then
    let (sigma, (evar, _)) = Evarutil.new_type_evar env sigma Evd.UnivRigid in
    sigma, evar
  else
    Evarutil.new_evar env sigma ty

let cvar (env, sigma as ctx) ty ohyps =
  let ohyps = CoqOption.from_coq (env, sigma) ohyps in
  if Option.has_some ohyps then
    try
      let hyps = Hypotheses.from_coq_list (env, sigma) (Option.get ohyps) in
      let vars = List.map (fun (v, _, _)->v) hyps in
      if List.distinct vars then
        try
          let subs, env = new_env ctx hyps in
          let ty = multi_subst subs ty in
          let sigma, evar = make_evar sigma env ty in
          let (e, _) = destEvar evar in
          (* the evar created by make_evar has id in the substitution
             but we need to remap it to the actual variables in hyps *)
          return sigma (mkEvar (e, Array.of_list vars))
        with
        | MissingDep ->
            fail sigma (Lazy.force E.mkHypMissesDependency)
        | Not_found ->
            fail sigma (Lazy.force E.mkTypeMissesDependency)
      else
        fail sigma (E.mkFailure "Duplicated variable in hypotheses")
    with Hypotheses.NotAVariable ->
      fail sigma (E.mkFailure "All hypothesis should be variables")
  else
    let sigma, evar = make_evar sigma env ty in
    return sigma evar


let rec get_name (env, sigma) (t: constr) : constr option =
  (* If t is a defined variable it is reducing it *)
  (*  let t = whd_betadeltaiota_nolet env sigma t in *)
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
    else None
  in
  match name with
  | Some (Name i) -> Some (CoqString.to_coq (Names.Id.to_string i))
  | Some _ -> (* it is Anonymous. We generate a fresh name. *)
      let n = Namegen.next_name_away (Name (Names.Id.of_string "x")) (ids_of_context env) in
      Some (CoqString.to_coq (Names.Id.to_string n))
  | _ -> None

(* return the reflected hash of a term *)
let hash (env, _, sigma, nus) c size =
  let size = CoqN.from_coq (env, sigma) size in
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

let rec run' (env, renv, sigma, nus as ctxt) t =
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
        if Names.eq_ind m (fst (Term.destInd (Lazy.force mkT_lazy))) then
          ix
        else -1
      else -1
    in
    match constr h with
    | -1 -> fail sigma (E.mkFailure (E.error_stuck h))
    | 1 -> (* ret *)
        return sigma (nth 1)

    | 2 -> (* bind *)
        run' ctxt (nth 2) >>= fun (sigma', v) ->
        let t' = mkApp(nth 3, [|v|]) in
        run' (env, renv, sigma', nus) t'

    | 3 -> (* try *)
        begin
          match run' ctxt (nth 1) with
          | Val (sigma, v) -> return sigma v
          | Err (_, c) ->
              let t' = mkApp(nth 2, [|c|]) in
              run' (env, renv, sigma, nus) t'
        end

    | 4 -> (* raise *)
        (* we make sure the exception is a closed term: it does not depend on evars or nus *)
        let term = nf_evar sigma (nth 1) in
        let rels = free_rels term in
        let closed = Int.Set.is_empty rels || Int.Set.max_elt rels > nus in
        let closed = closed && Evar.Set.is_empty (Evarutil.undefined_evars_of_term sigma term) in
        if closed then
          fail sigma term
        else
          fail sigma (Exceptions.mkExceptionNotGround env term)

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
        let e = nth 1 in
        if isRel e || isVar e then
          return sigma CoqBool.mkTrue
        else
          return sigma CoqBool.mkFalse

    | 11 -> (* nu *)
        let a, s, ot, f = nth 0, nth 2, nth 3, nth 4 in
        let name = CoqString.from_coq (env, sigma) s in
        let name = Names.Id.of_string name in
        if Id.Set.mem name (vars_of_env env) then
          fail sigma (Exceptions.mkNameExists s)
        else begin
          let x, fx = Names.Name name, Term.mkApp(Vars.lift 1 f, [|Term.mkRel 1|]) in
          let ot = CoqOption.from_coq (env, sigma) ot in
          let env = push_rel (x, ot, a) env in
          (* after extending the context we need to lift the variables
             in the reified context, together with the definition and
             type that we are going to append to it. *)
          let renv = Vars.lift 1 renv in
          let a = Vars.lift 1 a in
          let ot = Option.map (Vars.lift 1) ot in
          let (sigma', renv) = Hypotheses.cons_hyp a (mkRel 1) ot renv sigma env in
          match run' (env, renv, sigma', (nus+1)) fx with
          | Val (sigma', e) ->
              if Int.Set.mem 1 (free_rels e) then
                fail sigma (E.mkFailure (E.error_param env (Names.Id.to_string name) e))
              else
                return sigma' (pop e)
          | Err (sigma, e) ->
              fail sigma (pop e)
        end

    | 12 -> (* abs *)
        let a, p, x, y = nth 0, nth 1, nth 2, nth 3 in
        abs AbsFun (env, sigma) a p x y 0 mkProp

    | 13 -> (* abs_let *)
        let a, p, x, t, y = nth 0, nth 1, nth 2, nth 3, nth 4 in
        abs AbsLet (env, sigma) a p x y 0 t

    | 14 -> (* abs_prod *)
        let a, x, y = nth 0, nth 1, nth 2 in
        (* HACK: put mkProp as returning type *)
        abs AbsProd (env, sigma) a mkProp x y 0 mkProp

    | 15 -> (* abs_fix *)
        let a, f, t, n = nth 0, nth 1, nth 2, nth 3 in
        let n = CoqN.from_coq (env, sigma) n in
        (* HACK: put mkProp as returning type *)
        abs AbsFix (env, sigma) a mkProp f t n mkProp

    | 16 -> (* get_binder_name *)
        let t = nth 1 in
        let s = get_name (env, sigma) t in
        begin
          match s with
          | Some s -> return sigma s
          | None -> fail sigma (Lazy.force Exceptions.mkWrongTerm)
        end

    | 17 -> (* remove *)
        let x, t = nth 2, nth 3 in
        if isVar x || isRel x then
          if check_dependencies env x t then
            (* if it's a rel we need to update the indices in t, since there is one element less in the context *)
            let t = if isRel x then Vars.liftn (-1) (destRel x) t else t in
            let env, (sigma, renv) = env_without sigma env renv x in
            (* Note that if the recursive call raises an exception,
               the exception can't contain nus, so there is no need
               to lift the indices *)
            run' (env, renv, sigma, nus) t >>= fun (sigma, v)->
            return sigma (if isRel x then Vars.liftn (+1) (destRel x) v else v)
          else
            fail sigma (E.mkCannotRemoveVar env x)
        else
          fail sigma (E.mkFailure (E.remove_var env x))

    | 18 -> (* evar *)
        let ty, hyp = nth 0, nth 1 in
        cvar (env, sigma) ty hyp

    | 19 -> (* is_evar *)
        let e = whd_evar sigma (nth 1) in
        if isEvar e || (isApp e && isEvar (fst (destApp e))) then
          return sigma CoqBool.mkTrue
        else
          return sigma CoqBool.mkFalse

    | 20 -> (* hash *)
        return sigma (hash ctxt (nth 1) (nth 2))

    | 21 -> (* solve_typeclasses *)
        let evd' = Typeclasses.resolve_typeclasses ~fail:false env sigma in
        return evd' (Lazy.force CoqUnit.mkTT)

    | 22 -> (* print *)
        let s = nth 0 in
        print env sigma s;
        return sigma (Lazy.force CoqUnit.mkTT)

    | 23 -> (* pretty_print *)
        let t = nth 1 in
        let t = nf_evar sigma t in
        let s = string_of_ppcmds (Termops.print_constr_env env t) in
        return sigma (CoqString.to_coq s)

    | 24 -> (* hypotheses *)
        return sigma renv

    | 25 -> (* dest case *)
        let t = nth 1 in
        let (sigma', case) = dest_Case (env, sigma) t in
        return sigma' case

    | 26 -> (* get constrs *)
        let t = nth 1 in
        let (sigma', constrs) = get_Constrs (env, sigma) t in
        return sigma' constrs

    | 27 -> (* make case *)
        let case = nth 0 in
        let (sigma', case) = make_Case (env, sigma) case in
        return sigma' case

    | 28 -> (* munify *)
        let a, x, y, uni = nth 0, nth 1, nth 2, nth 3 in
        let feqT = CoqEq.mkAppEq a x y in
        begin
          let r = UnificationStrategy.unify None sigma env uni Reduction.CONV x y in
          match r with
          | Evarsolve.Success sigma, _ ->
              let feq = CoqEq.mkAppEqRefl a x in
              let someFeq = CoqOption.mkSome feqT feq in
              return sigma someFeq
          | _, _ ->
              let none = CoqOption.mkNone feqT in
              return sigma none
        end

    | 29 -> (* munify_cumul *)
        let x, y, uni = nth 2, nth 3, nth 4 in
        begin
          let r = UnificationStrategy.unify None sigma env uni Reduction.CUMUL x y in
          match r with
          | Evarsolve.Success sigma, _ ->
              return sigma CoqBool.mkTrue
          | _, _ ->
              return sigma CoqBool.mkFalse
        end

    | 30 -> (* call_ltac *)
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
            let undef = Evar.Map.domain (Evd.undefined_map sigma) in
            let (c, sigma) = Pfedit.refine_by_tactic env sigma concl (Tacinterp.eval_tactic tac) in
            let new_undef = Evar.Set.diff (Evar.Map.domain (Evd.undefined_map sigma)) undef in
            let new_undef = Evar.Set.elements new_undef in
            let sigma, goal = Goal.goal sigma env in
            let sigma, goals = CoqList.pto_coq goal (fun e sigma->Goal.goal_of_evar env sigma e) new_undef sigma in
            return sigma (CoqPair.mkPair concl goal c goals)
          with Errors.UserError(s,ppm) ->
            fail sigma (Exceptions.mkLtacError (s, ppm))
        end
    (* Tac (sigma, Tacinterp.eval_tactic tac, fun v -> Val v) *)

    | 31 -> (* list_ltac *)
        let aux k _ = Pp.msg_info (Pp.str (Names.KerName.to_string k)) in
        KNmap.iter aux (Tacenv.ltac_entries ());
        return sigma (Lazy.force CoqUnit.mkTT)

    | _ ->
        Exceptions.block "I have no idea what is this construct of T that you have here"


and run_fix (env, renv, sigma, _ as ctxt) h a b s i f x =
  let fixf = mkApp(h, Array.append a [|b;s;i;f|]) in
  let c = mkApp (f, Array.append [| fixf|] x) in
  run' ctxt c

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
  let (sigma, renv) = build_hypotheses sigma env in
  match run' (env, renv, sigma, 0) (nf_evar sigma t) with
  | Err (sigma', v) ->
      Err (sigma', nf_evar sigma' v)
  | Val (sigma', v) ->
      Val (sigma', nf_evar sigma' v)
