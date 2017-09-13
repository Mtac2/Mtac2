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
