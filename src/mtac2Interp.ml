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

  let proof_focus = Proof.new_focus_kind ()
  let proof_cond = Proof.no_cond proof_focus

  (** focus on the proof *)
  let focus () =
    Proof_global.simple_with_current_proof
      (fun _ -> Proof.focus proof_cond () 1)

  (** unfocus *)
  let maximal_unfocus () =
    let aux _ proof =
      let proof = Proof.unshelve proof in
      Proof.maximal_unfocus proof_focus proof
    in
    Proof_global.simple_with_current_proof aux
end

(**
   This module manages the interpretation of the mtac2 tactics
   and the vernac MProof command.
*)

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
      Mtac2ProofInfos.focus ();
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
