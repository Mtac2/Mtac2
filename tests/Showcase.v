Require Import MetaCoq.MetaCoq.
Import T.
Require Import Bool.Bool.

(** This file contains several examples showing the different
    tactics in MetaCoq. Many are taken from SF. *)

(* Basic tactics:
 - intros, cintros (with and without definitions).
 - destruct.
 - left, right.
 - reflexivity.
 - apply.
 - fix. TODO
 - generalize.
 - assert.
 - pose.
 - exists
*)

Theorem surjective_pairing : forall A B (p : A * B),
  p = (fst p, snd p).
MProof.
  typed_intros Type. destructn 0. intros. reflexivity.
Qed.

Theorem tl_length_pred : forall l: list nat,
  pred (length l) = length (tl l).
MProof.
  destructn 0 asp [ [] ; ["n"; "l'"] ].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
MProof.
  intros n m p q.
  assert (H : n + m = m + n).
  - rewrite -> PeanoNat.Nat.add_comm;; reflexivity.
  - rewrite -> H;; reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
MProof.
  cintros n {-
    r <- M.hyps; M.print_term r;; destructn 0;; intros m Hm
  -}.
  mexists (2 + m).
  apply Hm.
Qed.

Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  intros. select (_ -> _) apply;; assumption.
Qed.

Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  cintros _ _ _ _ {- select (_ -> _) apply;; assumption -}.
Qed.

Definition apply_fun : tactic :=
  A <- M.evar Type;
  B <- M.evar Type;
  select (A -> B) apply.

Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  intros;; apply_fun;; assumption.
Qed.

Theorem tl_length_pred' : forall A (l: list A),
  pred (length l) = length (tl l).
MProof.
  destructn 1;; intros;; reflexivity.
Qed.

Example cut_ex P Q R: (P \/ Q -> R) -> P -> R.
MProof.
  intros.
  cut (P \/ Q).
  - assumption.
  - left;; assumption.
Qed.

Theorem plus_n_O : forall n:nat, n = n + 0.
MProof.
  fix_tac "IH" 1.
  destructn 0.
  - reflexivity.
  - intro n'. simpl. rewrite <- IH.
    reflexivity.
Qed.


(** Ltac allows certain FP patterns. *)
Require Import Lists.ListTactics.

Ltac apply_one_of l :=
  list_fold_left ltac:(fun a b => (b || apply (elem a))) fail l.

Goal forall x y z : nat, In x (z :: y :: x :: nil).
Proof.
  intros.
  repeat (apply_one_of [Dyn in_eq; Dyn in_cons]).
Qed.

Definition apply_one_of l : tactic :=
  fold_left (fun a b=>a or (apply (elem b))) l (raise exception).

Goal forall x y z : nat, In x (z :: y :: x :: nil).
MProof.
  Time intros;; repeat (apply_one_of [Dyn in_eq; Dyn in_cons]).
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
MProof.
  intros a b c d e f.
  apply (trans_eq mwhere "y":=[c;d]).
Qed.

Notation "x ?" := (ltac:(mrun (apply x))) (at level 0).

Definition test (x y z: nat) : In x [x] := in_eq?.
