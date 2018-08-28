Require Import Mtac2.Mtac2.

Goal 4 = 3 -> 3 = 2 -> 2 = 1 -> 1 = 4.
MProof.
  intros H1 H2 H3.
  rewrite H1.
  rewrite -> H2.
  rewrite <- H3.
  rewrite H3, H3.
  T.reflexivity.
Qed.

Goal 4 = 3 -> 3 = 2 -> 2 = 1 -> 1 = 4.
MProof.
  intros H1 H2 H3.
  rewrite H1, H2, H3.
  rewrite <- H3, H2, H1.
  rewrite -> H1, H2, H3.
  T.reflexivity.
Qed.

Goal 4 = 3 -> 3 = 2 -> 2 = 1 -> 1 = 4.
MProof.
  intros H1 H2 H3.
  rewrite_in -> H3; H1.
  rewrite_in <- H1; H3, H2.
  rewrite_in H3; H1, H2.
  rewrite H3, H2.
  T.reflexivity.
Qed.
