(** This file contains several examples showing the different tactics and tactic
    operators in Mtac2. Many of the examples are inspired from SF. *)

(** Here is a list of basic tactics included in Mtac2, that we present here:
 - intros, cintros, typed_intros (with and without definitions).
 - destruct (and its variants).
 - left, right.
 - reflexivity.
 - apply.
 - fix.
 - generalize.
 - assert.
 - pose.
 - exists
*)

(** We start by importing Mtac2. The module [Mtac2] imports most of Mtac2's
stuff. *)
Require Import Mtac2.Mtac2.
(** Since we are going to work with the [Tactics] module, we import the inner [T] module. *)
Import T.

(** We're going to prove stuff about lists. *)
Require Import Lists.List.
Import Lists.List.ListNotations.

(** A simple example to warm up. *)
Theorem surjective_pairing_1 : forall A B (p : A * B),
  p = (fst p, snd p).
MProof.
  (** [typed_intros] introduces everything of a certain type *)
  typed_intros Type.
  (** [destructn] is [destruct] for a certain (0-based) number of binders. *)
  destructn 0.
  intros.
  (** (We must FIX how the goal is presented, now it contains extra stuff about sorts) *)
  simpl.
  reflexivity.
Qed.

(** We can use the [&>] composition operator (left associative) of [Mtac2] to inline the proof. *)
Theorem surjective_pairing : forall A B (p : A * B),
  p = (fst p, snd p).
MProof.
  typed_intros Type &> destructn 0 &> reflexivity. (* [reflexivity] does [intros] *)
Qed.

(** Mtac2 has intro patterns, with a tactic call [pintros] and a combinator
(similar to SSReflect's [=>]) called [asp]. *)
Theorem tl_length_pred : forall l: list nat,
  pred (length l) = length (tl l).
MProof.
  destructn 0 asp [ [] ; ["n" ; "l'"] ].
  - (* l = nil *)
    simpl.
    reflexivity.
  - (* l = cons n l' *)
    simpl.
    reflexivity.
Qed.

(** Another example using [assert] and the [rewrite] tactic imported from Coq's
own. *)
Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
MProof.
  intros n m p q.
  assert (H : n + m = m + n).
  - rewrite -> PeanoNat.Nat.add_comm &> reflexivity.
  - rewrite -> H &> reflexivity.
Qed.

(** An example featuring scoped introduction of variables [cintros] and
[mexists]. *)
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
MProof.
  cintros n {- destructn 0 &> intros m Hm -}.
  simpl.
  mexists (2 + m).
  (** We need to FIX the beta-expanded goal *)
  apply Hm.
Qed.

(** An example featuring the handy [select] tactic to pick an element from the
list of hypotheses based on its type. *)
Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  intros. select (_ -> _) >>= apply. assumption.
Qed.

(** Note that we can't use [&>] to compose [intros] with [select] (try it!).
The reason is that the holes in the type (the underscores) are turn into
meta-variables, which can't refer to the introduced variables. *)

(** We can, however, inline the proof with cintros. In order to avoid parens we
need the right-associative composition operator [;;]. *)
Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  cintros _ _ _ _ {- select (_ -> _) >>= apply;; assumption -}.
Qed.


Definition apply_fun : tactic :=
  A <- M.evar Type;
  B <- M.evar Type;
  select (A -> B) >>= apply.

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
  fix_tac (TheName "IH") 1.
  destructn 0.
  - reflexivity.
  - intro n'. simpl. rewrite <- IH.
    reflexivity.
Qed.


(** Ltac allows certain FP patterns. *)
Require Import Lists.ListTactics.

Ltac apply_one_of l :=
  list_fold_left ltac:(fun a b => (b || apply (elemr a))) fail l.

Goal forall x y z : nat, In x (z :: y :: x :: nil).
Proof.
  intros.
  repeat (apply_one_of (Dynr in_eq :: Dynr in_cons :: nil)).
Qed.

Definition apply_one_of l : tactic :=
  mfold_left (fun a b=>a || (apply (elemr b)))%tactic l (raise exception).

Goal forall x y z : nat, In x (z :: y :: x :: nil).
MProof.
  Time intros;; T.repeat (apply_one_of [m:Dynr in_eq| Dynr in_cons]).
Qed.
Import Coq.Lists.List.ListNotations.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
MProof.
  intros a b c d e f.
  apply (trans_eq mwith ("y":=[c;d])).
Qed.

Notation "x ?" := (ltac:(mrun (apply x))) (at level 0).

Definition test (x y z: nat) : In x [x] := in_eq?.