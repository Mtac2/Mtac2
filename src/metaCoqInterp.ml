open Constrs
open Ltac_pretype

type mrun_arg_type =
  | PolyProgram of (Univ.AbstractContext.t * EConstr.types)
  | MonoProgram of (EConstr.types)
  | GTactic

type mrun_arg =
  | StaticallyChecked of (mrun_arg_type * Names.GlobRef.t)
  | DynamicallyChecked of (Ltac_pretype.closed_glob_constr)

let ifTactic env sigma ty c =
  let (sigma, gtactic) = MCTactics.mkGTactic env sigma in
  let unitType = CoqUnit.mkType in
  let gtactic = EConstr.mkApp(gtactic, [|Lazy.force unitType|]) in
  let open Evarsolve in
  let res = Unicoq.Munify.unify_evar_conv TransparentState.full env sigma Conversion.CONV gtactic ty in
  match res with
  | Success sigma -> (true, sigma)
  | _ -> (false, sigma)


let glob_mtac_type ist r =
  let open Declarations in
  try
    let c =
      match
        (Smartlocate.locate_global_with_alias r) (* Maybe put loc back in for error reporting *)
      with
      | Names.GlobRef.ConstRef c -> c
      | _ -> CErrors.user_err (Pp.str "mrun_static only accepts constants. It does *not* accept variables, inductives, or constructors. ")
    in
    (* Typecheck here. Unification? probably *)
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let body = Global.lookup_constant c in
    let ty = body.const_type in
    let sigma, ty, ret = match body.const_universes with
      | Declarations.Monomorphic ->
          sigma, ty, (fun ty -> MonoProgram ty) (* constraints already registered *)
      | Declarations.Polymorphic au ->
          (* need to instantiate and register the abstract universes a *)
          let inst, ctx = UnivGen.fresh_instance_from au None in
          (* TODO: find out why UnivFlexible needs a bool & select correct bool. *)
          let sigma = Evd.merge_context_set ?sideff:(Some false) (Evd.UnivFlexible true) sigma ctx in
          sigma, Vars.subst_instance_constr inst ty, (fun ty -> PolyProgram (au, ty))
    in
    let ty = EConstr.of_constr ty in
    let (h, args) = Reductionops.whd_all_stack env sigma ty in
    let sigma, metaCoqType = MtacNames.mkT_lazy sigma env in
    if EConstr.eq_constr_nounivs sigma metaCoqType h && List.length args = 1 then
      (ret (List.hd args), (Names.GlobRef.ConstRef c))
    else
      let b, sigma = ifTactic env sigma ty (body.const_body) in
      if b then
        (GTactic, Names.GlobRef.ConstRef c)
      else
        CErrors.user_err (Pp.str "Not a Mtactic")
  with Not_found as exn ->
    let _, info = Exninfo.capture exn in
    Nametab.error_global_not_found ~info r


module MetaCoqRun = struct
  (** This module run the interpretation of a constr
  *)

  let uncaught ?loc env sigma e tr =
    let open Pp in
    let err =
      str "Uncaught Mtac exception:\n"
      ++ str "  " ++ hov 2 (Printer.pr_econstr_env env sigma e)
      ++ str "\n" ++ str "Mtac backtrace (last function first):\n"
      ++ Run.pr_backtrace tr
      ++ str "End of backtrace\n"
      ++ str "(Backtraces are only recorded with [Set_Debug_Exceptions].)\n"
    in
    CErrors.user_err ?loc err

  let ifM env sigma concl ty c =
    let sigma, metaCoqType = MtacNames.mkT_lazy sigma env in
    let (h, args) = Reductionops.whd_all_stack env sigma ty in
    if EConstr.eq_constr_nounivs sigma metaCoqType h && List.length args = 1 then
      try
        let sigma = Evarconv.unify_leq_delay env sigma (List.hd args) concl in
        (true, sigma)
      with Evarconv.UnableToUnify(_,_) -> CErrors.user_err (Pp.str "Different types")
    else
      (false, sigma)

  (** Given a type concl and a term c, it checks that c has type:
      - [M concl]: then it returns [c]
      - [tactic]: then it returns [c (Goal concl evar)] *)
  let pretypeT env sigma concl evar c =
    (* let sigma, ty = Typing.type_of ~refresh:true env sigma c in *)
    let ty = Retyping.get_type_of env sigma c in
    let b, sigma = ifM env sigma concl ty c in
    if b then
      (false, sigma, ty, c)
    else
      let b, sigma = ifTactic env sigma ty c in
      if b then
        (true, sigma, ty, c)
      else
        CErrors.user_err (Pp.str "Not a Mtactic")

  let run ?loc env sigma concl evar istactic (oty) t =
    (* [run] is also the entry point for code that doesn't go through
       [pretypeT] so we have to do the application to the current goal
       for tactics in here instead of [pretypeT].
    *)
    let sigma, t = if istactic then
        let sigma, goal = Run.Goal.mkTheGoal concl evar sigma env in
        let t = EConstr.mkApp(t, [|goal|]) in
        let sigma, _ = Typing.type_of env sigma t in
        (sigma, t)
      else sigma, t
    in
    let sigma, ty =
      match oty with
      | Some ty -> sigma, ty
      | None -> Typing.type_of env sigma t
    in
    match Run.run (env, sigma) ty t with
    | Run.Val (sigma, v) ->
        let open Proofview in let open Proofview.Notations in
        Unsafe.tclEVARSADVANCE sigma >>= fun _->
        if not istactic then
          Refine.refine ~typecheck:false begin fun evd -> evd, v end
        else
          begin
            try
              let goals = CoqList.from_coq sigma env v in
              let goals = List.map (fun x -> snd (CoqPair.from_coq (env, sigma) x)) goals in
              let goals = List.map (Run.Goal.evar_of_goal sigma env) goals in
              let goals = List.filter Option.has_some goals in
              let goals = List.map (fun e->Proofview_monad.with_empty_state (Option.get e)) goals in
              Unsafe.tclSETGOALS goals
            with CoqList.NotAList e ->
              let open Pp in
              CErrors.user_err (str "The list of goals is not normalized: " ++ (Printer.pr_econstr_env env sigma e))
          end
    | Run.Err ((sigma, e), tr) ->
        uncaught ?loc env sigma e tr

  let evar_of_goal gl =
    let evk = Proofview.Goal.goal gl in
    let EvarInfo info = Evd.find (Proofview.Goal.sigma gl) evk in
    let ids = Evd.evar_identity_subst info in
    EConstr.Unsafe.to_constr @@ EConstr.mkEvar (evk, ids)

  (** Get back the context given a goal, interp the constr_expr to obtain a constr
      Then run the interpretation fo the constr, and returns the tactic value,
      according to the value of the data returned by [run].
  *)
  let run_tac t =
    let open Proofview.Goal in
    enter begin fun gl ->
      let loc = Constrexpr_ops.constr_loc t in
      let env = env gl in
      let concl = concl gl in
      let sigma = sigma gl in
      let evar = EConstr.of_constr (evar_of_goal gl) in
      let (sigma, t) = Constrintern.interp_open_constr env sigma t in
      let (istactic, sigma, ty, t) = pretypeT env sigma concl evar t in
      (* We could be smarter here with the optional type argument to [run] but I cannot get it to work. *)
      run ?loc env sigma concl evar istactic (None) t
    end


  let understand env sigma {closure=closure;term=term} =
    let open Glob_ops in
    let open Pretyping in
    let flags = all_no_fail_flags in
    let lvar = { empty_lvar with
                 ltac_constrs = closure.typed;
                 ltac_uconstrs = closure.untyped;
                 ltac_idents = closure.idents;
               } in
    understand_ltac flags env sigma lvar WithoutTypeConstraint term

  let run_tac_constr t =
    let open Proofview.Goal in
    enter begin fun gl ->
      let env = env gl in
      let concl = concl gl in
      let sigma = sigma gl in
      let evar = EConstr.of_constr (evar_of_goal gl) in
      let ((istactic, sigma, ty, t), loc) = match t with
        | StaticallyChecked (MonoProgram ty, Names.GlobRef.ConstRef c) ->
            begin
              try
                let sigma = Evarconv.unify_leq_delay env sigma concl ty in
                (* monomorphic, so empty universe instance *)
                ((false, sigma, ty, EConstr.mkConstU (c, EConstr.EInstance.empty)), None)
              with Evarconv.UnableToUnify(_,_) -> CErrors.user_err (Pp.str "Different types")
            end
        | StaticallyChecked (PolyProgram (au, ty), Names.GlobRef.ConstRef  c) ->
            begin
              try
                let inst, ctx = UnivGen.fresh_instance_from au None in
                (* TODO: find out why UnivFlexible needs a bool & select correct bool. *)
                let sigma = Evd.merge_context_set ?sideff:(Some false) (Evd.UnivFlexible true) sigma ctx in
                let sigma = Evarconv.unify_leq_delay env sigma concl ty in
                ((false, sigma, ty, EConstr.mkConstU (c, EConstr.EInstance.make inst)), None)
              with Evarconv.UnableToUnify(_,_) -> CErrors.user_err (Pp.str "Different types")
            end
        | StaticallyChecked (GTactic, gr) ->
            let sigma, t = EConstr.fresh_global env sigma gr in
            let ty = Retyping.get_type_of env sigma t in
            ((true, sigma, ty, t), None)
        | DynamicallyChecked t ->
            let {term=term} = t in
            let loc = Glob_ops.loc_of_glob_constr term in
            let sigma, t = understand env sigma t in
            pretypeT env sigma concl evar t, loc
        | _ -> assert false
      in
      run ?loc env sigma concl evar istactic None t
    end

  let run_mtac_do env sigma t =
    let loc = Constrexpr_ops.constr_loc t in
    let sigma, t = Constrintern.interp_open_constr env sigma t in
    let sigma, ty = Typing.type_of env sigma t in
    let sigma, (concl, sort) = Evarutil.new_type_evar env sigma Evd.univ_flexible in
    let isM, sigma = ifM env sigma concl ty t in
    if isM then
      match Run.run (env, sigma) ty t with
      | Run.Val _ -> ()
      | Run.Err ((_, e), tr) ->
          uncaught ?loc env sigma e tr
    else
      CErrors.user_err (Pp.str "Mtac Do expects a term of type [M _].")

end

(**
   This module manages the interpretation of the MetaCoq tactics
   and the vernac MProof command.
*)

(** Interpreter of the MProof vernac command :
    - Get back and focus on the current proof
    - Set the proof mode to "MProof" mode.
    - Print subgoals *)
let interp_mproof_command () = ()

(** Interpreter of a mtactic *)
let interp_instr = function
  | MetaCoqInstr.MetaCoq_constr c -> MetaCoqRun.run_tac c

let exec ~pstate f =
  fst @@ Declare.Proof.by (f ()) pstate

(** Interpreter of a constr :
    - Interpretes the constr
    - Unfocus on the current proof *)
let interp_proof_constr ~pstate instr =
  exec ~pstate (fun () -> interp_instr instr)
