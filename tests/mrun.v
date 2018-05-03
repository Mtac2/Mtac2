From Mtac2 Require Import Mtac2.

Example trivial : True.
Proof.
  mrun (M.ret I).
Qed.

Example exact : True.
Proof.
  mrun (T.exact I).
Qed.

Example destruct : nat -> True.
Proof.
  mrun (T.destructn 0).
  - mrun (T.exact I).
  - mrun (T.introsn 1;; T.exact I).
Qed.

Example destruct2 : nat -> True.
Proof.
  mrun (T.destructn 0); [mrun (T.exact I) | mrun (T.introsn 1;; T.exact I)].
Qed.

Definition MTrue := M.ret I.
Ltac mrun_static_tac1 := mrun_static MTrue.

Example mrun_static_ex1 : True.
Proof.
  mrun_static_tac1.
Qed.

Definition TTrue := T.exact I.

Ltac mrun_static_tac2 := mrun_static TTrue.

Example mrun_static_ex2 : True.
Proof.
  mrun_static_tac2.
Qed.

Fail Ltac mrun_static_tac3 := mrun_static I.

Definition Munit := M.ret tt.
Ltac mrun_static_tac4 := mrun_static Munit.

Example mrun_static_ex4 : True.
Proof.
  Fail mrun_static_tac4.
Abort.