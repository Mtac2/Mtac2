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
     let (gl,ev,sigma) = Goal.V82.mk_goal (Tacmach.project gls) hyps concl (info_gen extra) in
     let sigma = Goal.V82.partial_solution sigma it ev in
     {Evd.it = [gl] ; sigma= sigma; } )

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
      go_to_proof_mode () ;
      Proof_global.set_proof_mode "MProof" ;
      Vernacentries.print_subgoals ()
    end

(** Interpreter of a mtactic *)
let interp_instr instr =
  match instr with
  | Mtac2Instr.Mtac2_constr c -> Mtac2Run.run_tac c

(** Interpreter of a constr :
    - Interpretes the constr
    - Unfocus on the current proof
    - Print subgoals *)
let interp_proof_constr instr =
  begin
    ignore (Pfedit.by  (interp_instr instr));
    Mtac2ProofInfos.maximal_unfocus ();
    Vernacentries.print_subgoals ()
  end
