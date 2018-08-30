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
  T.simpl_in H1 &> T.simpl_in H2. (* #101 concatenation of simpl_in doesn't work *)
  rewrite H1, H2.
  T.reflexivity.
Qed.

Goal True.
MProof.
  T.cut True.
  - T.apply id.
  - T.exact I.
Qed.

Inductive test_i :=
| Zero : nat -> test_i
| One : test_i -> test_i
| Two : test_i -> test_i -> test_i.

Goal forall g:test_i, g = g.
MProof.
  (* #97 intros wasn't creating evars for each type *)
  T.destructn 0 &> intros n &> T.reflexivity.
Qed.
