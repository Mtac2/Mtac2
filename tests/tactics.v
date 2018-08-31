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

Require Import Mtac2.tactics.IntroPatt.
Example ex_act_on (x y z : nat) (H: x = y) : y = x.
MProof.
  act_on x T.destruct [i: ~~ | \x'] &>
    (`A B <- M.evar nat; T.select (A = B) >>= fun x=>rewrite x) &>
    T.reflexivity.
Qed.

Example ex_act_on2 (x y z : test_i) (H: x = y) : y = x.
MProof.
  act_on x T.destruct [i: ?? | ?? | \a ??] &>
    (`A B <- M.evar test_i; T.select (A = B) >>= fun x=>rewrite x) &>
    T.reflexivity.
Qed.

Example ex_specialize: (forall x, x >= 0) -> forall y, y >= 0.
MProof.
  intros f x.
  T.specialize f x.
  T.assumption.
Qed.
