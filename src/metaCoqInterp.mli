module MetaCoqRun : sig
  val run_tac_constr : Constr.t -> unit Proofview.tactic
end

val interp_proof_constr : MetaCoqInstr.mproof_instr -> unit
val interp_mproof_command : unit -> unit
