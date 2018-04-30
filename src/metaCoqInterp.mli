type mrun_arg_type =
  | Program of (EConstr.types)
  | GTactic

type mrun_arg =
  | StaticallyChecked of (mrun_arg_type * Globnames.global_reference)
  | DynamicallyChecked of (Glob_term.closed_glob_constr)

module MetaCoqRun : sig
  val run_tac_constr : mrun_arg -> unit Proofview.tactic

  val run_cmd : Constrexpr.constr_expr -> unit
end

val ifTactic : Environ.env -> Evd.evar_map -> EConstr.types -> 'a -> bool * Evd.evar_map

val interp_proof_constr : MetaCoqInstr.mproof_instr -> unit
val interp_mproof_command : unit -> unit
val end_proof : unit -> unit
