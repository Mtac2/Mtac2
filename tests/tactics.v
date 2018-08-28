Require Import Mtac2.Mtac2.

Goal 2+3 = 4 -> 2+2 = 3 -> 5 = 3.
MProof.
  intros H1 H2.
  T.simpl_in_all.
  rewrite H1, H2.
  T.reflexivity.
Qed.

Goal 2+3 = 4 -> 2+2 = 3 -> 5 = 3.
MProof.
  intros H1 H2.
  T.simpl_in H1 &> T.simpl_in H2. (* FIXME concatenation of simpl_in doesn't work *)
  Fail rewrite H1, H2.
  Fail T.reflexivity.
Abort.

Goal True.
MProof.
  T.cut True.
  - T.apply id.
  - T.exact I.
Qed.