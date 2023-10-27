From Mtac2 Require Import Mtac2 CompoundTactics.

Import T.
Import T.notations.
Import CT.
Import CT.notations.
Example exabs (x : nat) : x = 1 -> 1 = x.
MProof.
intro H.
simple_rewrite H.
reflexivity.
Qed.

Example exabs2 (x : nat) : S x = 1 -> 1 = S x.
MProof.
intro H.
simple_rewrite H.
reflexivity.
Qed.

Require Import Strings.String.
Example exabs2' (x : nat) : S x = 1 -> 1 = S x.
MProof.
intro H.
variabilize (S x) as t.
assert (B:t = S x).
reflexivity.
Abort.

Require Import Arith.

Example exif (x : nat) : if Nat.eqb (S x) 1 then x = 0 : Type else True.
MProof.
variabilize (Nat.eqb (S x) (S 0)) as t.
assert (B:t = Nat.eqb (S x) 1).
reflexivity.
Abort.

Definition sillyfun (n : nat) : bool :=
  if Nat.eqb n 3 then false
  else if Nat.eqb n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  (sillyfun n = false) : Type.
MProof.
  intros n. unfold sillyfun.
  variabilize (Nat.eqb n 3) as t3.
  destruct t3.
  simpl. reflexivity.
  simpl.
  variabilize (Nat.eqb _ _) as t5.
  destruct t5 &> reflexivity.
Qed.



Definition sillyfun1 (n : nat) : bool :=
  if Nat.eqb n 3 then true
  else if Nat.eqb n 5 then true
  else false.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Theorem sillyfun1_odd : forall (n : nat),
     (sillyfun1 n = true ->
     oddb n = true) : Type .
MProof.
  intros n. unfold sillyfun1.
  variabilize (Nat.eqb n 3) as t.
  assert (Heqe3 : t = (n =? 3)%nat) |1> reflexivity.
  move_back Heqe3.
  destruct t &> intro Heqe3.
Abort.
