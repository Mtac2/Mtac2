(** This module defines the abstract syntax tree for Mtac2 instructions. *)

(** Mtac2 uses the syntax of Coq to represent programs. *)
type mproof_instr =
  | Mtac2_constr of Constrexpr.constr_expr
