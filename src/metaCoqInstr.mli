(** This module defines the abstract syntax tree for MetaCoq instructions. *)

(** MetaCoq uses the syntax of Coq to represent programs. *)
type mproof_instr =
  | MetaCoq_constr of Constrexpr.constr_expr
