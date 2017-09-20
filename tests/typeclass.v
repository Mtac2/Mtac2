From Mtac2 Require Import Mtac2.

Class Test := { val : nat }.

Instance Zero : Test := {| val := 0 |}.

Import M.notations.

Definition zero := ltac: (mrun (M.solve_typeclass Test >>= fun x=>M.ret (@val x))).

Goal zero = 0.
MProof.
  T.reflexivity.
Qed.
