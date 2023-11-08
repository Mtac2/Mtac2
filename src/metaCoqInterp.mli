(* open Ltac_pretype

   module MetaCoqRun : sig val run_tac_constr : closed_glob_constr -> unit
   Proofview.tactic *)
type mrun_arg_type =
  | PolyProgram of (UVars.AbstractContext.t * EConstr.types)
  | MonoProgram of (EConstr.types)
  | GTactic

type mrun_arg =
  | StaticallyChecked of (mrun_arg_type * Names.GlobRef.t)
  | DynamicallyChecked of (Ltac_pretype.closed_glob_constr)

module MetaCoqRun : sig
  val run_tac_constr : mrun_arg -> unit Proofview.tactic

  val run_mtac_do :
    Environ.env -> Evd.evar_map -> Constrexpr.constr_expr -> unit
end

val glob_mtac_type : 'a -> Libnames.qualid -> mrun_arg_type * Names.GlobRef.t

val interp_proof_constr
  :  pstate:Declare.Proof.t
  -> MetaCoqInstr.mproof_instr
  -> Declare.Proof.t

val interp_mproof_command : unit -> unit
