Require Import Mtac2.Base.
Import M.
Import M.notations.

(* dumb test *)
Mtac Do (ret tt).

(* Test without parentheses. *)
Mtac Do ret tt.

Mtac Do (print_term tt).

(* open terms are OK *)
Mtac Do (ret _).
Fail Mtac Do _. (* Stuck term *)
Set Printing Universes.
Mtac Do New Exception Pum.
Check Pum.

Fail Mtac Do (raise Pum).

Mtac Do Check (_ + _).