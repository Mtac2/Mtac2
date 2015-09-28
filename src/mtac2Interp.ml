module Mtac2Run = struct
  (** This module run the interpretation of a constr
  *)

  open Proofview.Notations

  (**  *)
  let pretypeT env sigma t c =
    let (_, e) = Run.MtacNames.mkT_lazy sigma env in
    let ty = Retyping.get_type_of env sigma c in
    let (h, args) = Reductionops.whd_betadeltaiota_stack env sigma ty in
    if Term.eq_constr_nounivs e h && List.length args = 1 then
      let sigma = Evarconv.the_conv_x_leq env t (List.hd args) sigma in
      (sigma, c)
    else
      Errors.error "Not a Mtactic"

  (** Get back the context given a goal, interp the constr_expr to obtain a constr
      Then run the interpretation fo the constr, and returns the tactic value,
      according to the value of the data returned by [run].
  *)
  let run_tac t =
    Proofview.Goal.nf_enter begin fun gl ->
      let sigma = Proofview.Goal.sigma gl in
      let env = Proofview.Goal.env gl in
      let concl = Proofview.Goal.concl gl in
      let sigma,c = Constrintern.interp_open_constr env sigma t in
      let (sigma, t) = pretypeT env sigma concl c in
      let r = Run.run (env, sigma) c in
      match r with
      | Run.Val (sigma', _, v) ->
          (Proofview.Unsafe.tclEVARS sigma')
          <*> (Proofview.Refine.refine ~unsafe:false (fun s -> (s, v)))
      | Run.Err (_, _, e) ->
          Errors.error ("Uncaught exception: " ^ Pp.string_of_ppcmds (Termops.print_constr e))
    end
end
module Mtac2ProofInfos = struct
  (**
     This module concerns the state of the proof tree
  *)

  (**  *)
  type split_tree=
    | Skip_patt of Names.Id.Set.t * split_tree
    | Split_patt of Names.Id.Set.t * Names.inductive * (bool array * (Names.Id.Set.t * split_tree) option) array
    | Close_patt of split_tree
    | End_patt of (Names.Id.t * (int * int))

  (**  *)
  type elim_kind =
    | EK_dep of split_tree
    | EK_nodep
    | EK_unknown

  type recpath = int option*Declarations.wf_paths

  type per_info =
    {per_casee:Term.constr;
     per_ctype:Term.types;
     per_ind:Names.inductive;
     per_pred:Term.constr;
     per_args:Term.constr list;
     per_params:Term.constr list;
     per_nparams:int;
     per_wf:recpath}

  type elim_type =
    | ET_Case_analysis
    | ET_Induction

  type stack_info =
    | Per of elim_type * per_info * elim_kind * Names.Id.t list
    | Suppose_case
    | Claim
    | Focus_claim

  type pm_info =
    { pm_stack : stack_info list}

  (** Create a new field in datatype used to store additional information in evar maps*)
  let info = Evd.Store.field ()

  (** Get back the infos of a given goal *)
  let get_info sigma gl=
    match Evd.Store.get (Goal.V82.extra sigma gl) info with
    | None -> invalid_arg "get_info"
    | Some pm -> pm

  let get_stack pts =
    let { Evd.it = goals; sigma } = Proof.V82.subgoals pts in
    let info = get_info sigma (List.hd goals) in
    info.pm_stack

  let proof_focus = Proof.new_focus_kind ()
  let proof_cond = Proof.no_cond proof_focus

  (** focus on the proof *)
  let focus p =
    let inf = get_stack p in
    Printf.printf "____focus\n%!";
    Proof_global.simple_with_current_proof
      (fun _ -> Proof.focus proof_cond inf 1)

  (** unfocus *)
  let maximal_unfocus () =
    Proof_global.simple_with_current_proof
      (fun _ -> Proof.maximal_unfocus proof_focus)
end

(**
   This module manages the interpretation of the mtac2 tactics
   and the vernac MProof command.
*)

(** Get the infos of a goal *)
let get_its_info gls = Mtac2ProofInfos.get_info gls.Evd.sigma gls.Evd.it

(**  *)
let tcl_change_info_gen info_gen =
  (fun gls ->
     let it = Evd.sig_it gls in
     let concl = Tacmach.pf_concl gls in
     let hyps = Goal.V82.hyps (Tacmach.project gls) it in
     let extra = Goal.V82.extra (Tacmach.project gls) it in
     let (gl, ev, sigma) =
       Goal.V82.mk_goal (Tacmach.project gls) hyps concl (info_gen extra)
     in
     let sigma = Goal.V82.partial_solution sigma it ev in
     {Evd.it = [gl]; sigma}
  )

(** Updates the info of the evar maps *)
let tcl_change_info info gls =
  let info_gen s = Evd.Store.set s Mtac2ProofInfos.info info in
  tcl_change_info_gen info_gen gls

(** Initializes the evar map and returns the updates evar map given the goal *)
let start_proof_tac gls=
  let info={Mtac2ProofInfos.pm_stack=[]} in
  tcl_change_info info gls

(** Applies start_proof_tac to the 1st subgoal of the current
    focused proof in order to updates the evar map and focus on
    the current proof *)
let go_to_proof_mode () =
  ignore (Pfedit.by (Proofview.V82.tactic start_proof_tac));
  let p = Proof_global.give_me_the_proof () in
  Mtac2ProofInfos.focus p


(** Interpreter of the MProof vernac command :
    - Get back and focus on the current proof
    - Set the proof mode to "MProof" mode.
    - Print subgoals *)
let interp_mproof_command () =
  let pf = Proof_global.give_me_the_proof () in
  if Proof.is_done pf then
    Errors.error "Nothing left to prove here."
  else
    begin
      go_to_proof_mode ();
      Proof_global.set_proof_mode "MProof";
      Vernacentries.print_subgoals ();
    end

(** Interpreter of a mtactic *)
let interp_instr = function
  | Mtac2Instr.Mtac2_constr c -> Mtac2Run.run_tac c

(** Interpreter of a constr :
    - Interpretes the constr
    - Unfocus on the current proof
    - Print subgoals *)
let interp_proof_constr instr =
  ignore (Pfedit.by (interp_instr instr));
  Mtac2ProofInfos.maximal_unfocus ();
  Vernacentries.print_subgoals ()
