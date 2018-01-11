From Mtac2 Require Import Mtac2.

Class Test := { val : nat }.

Instance Zero : Test := {| val := 0 |}.

Import M.notations.

Definition CouldntFindTC : Exception. exact exception. Qed.

Definition fail_solve_tc A :=
  M.solve_typeclass A >>= fun x=>
  match x with
  | mSome v => M.ret v
  | mNone => M.raise CouldntFindTC
  end.

Definition zero := ltac:(mrun (fail_solve_tc Test >>= fun x=>M.ret (@val x))).

Goal zero = 0.
MProof.
  T.reflexivity.
Qed.

Class TestFail := { valF : nat }.

Definition fail_but_caught := ltac: (mrun (
  mtry fail_solve_tc TestFail;; M.ret 1
  with CouldntFindTC => M.ret 0 end)).

Goal fail_but_caught = 0.
MProof.
  T.reflexivity.
Qed.
