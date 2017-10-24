Require Import Mtac2.Mtac2.

Import T.
Import T.notations.
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
variabilize (S x) "t".
assert (B:t = S x).
reflexivity.
Abort.

Require Import Arith.

Example exif (x : nat) : if beq_nat (S x) 1 then x = 0 : Type else True.
MProof.
variabilize (beq_nat _ _) "t".
assert (B:t = beq_nat (S x) 1).
reflexivity.
Abort.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  (sillyfun n = false) : Type.
MProof.
  intros n. unfold sillyfun.
  variabilize (beq_nat n 3) "t3".
  destruct t3.
  simpl. reflexivity.
  simpl.
  variabilize (beq_nat _ _) "t5".
  destruct t5 &> reflexivity.
Qed.



Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
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
  variabilize (beq_nat n 3) "t".
  assert (Heqe3 : t = (n =? 3)) |1> reflexivity.
  move_back Heqe3.
  destruct t &> intro Heqe3.
Abort.
