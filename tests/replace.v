Require Import Mtac2.Mtac2.

Goal (if true then True else False) -> True.
MProof.
  intros H.
  M.replace H meq_refl (M.ret H).
  Show Proof.
Qed.
