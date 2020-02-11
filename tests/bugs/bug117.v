From Mtac2 Require Import Mtac2.

Definition to_any (g: goal gs_open) : goal gs_any :=
  match g with
  | Metavar _ s e => Metavar' _ _ s e
  end.

(* besides duplicating the same goal (which is not incorrect, just stupid)
   this tactic is not normalizing the list. *)
Definition wrong_tactic : tactic := \tactic g =>
  M.ret ([m: (m: tt, to_any g)]+m+[m: (m: tt, to_any g)]).

Goal True.
MProof.
  Fail wrong_tactic. (* it should fail nicely (without anomaly) *)
Abort.