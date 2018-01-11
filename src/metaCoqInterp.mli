module MetaCoqRun : sig
  val run_tac_constr : Glob_term.closed_glob_constr -> unit Proofview.tactic

  val run_cmd : Constrexpr.constr_expr -> unit
end

val interp_proof_constr : MetaCoqInstr.mproof_instr -> unit
val interp_mproof_command : unit -> unit
val end_proof : unit -> unit
