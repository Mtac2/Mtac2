Require Import Mtac2.Mtac2.
Import Mtac2Notations.

Definition exact {A : Type} (x : A) : M A :=
  ret x.

Lemma test1 : forall P, P -> P.
MProof.
  exact (fun P x => x).
Qed.

Definition reflexivity {A : Type} {x : A} : M (x = x) :=
  ret (eq_refl : x = x).

Definition apply {B C : Type} (l : B -> C) : M C :=
  h <- evar B;
  ret (l h).

Lemma test2 : True.
MProof.
   apply (fun (x : True) => x).
   exact I.
Qed.

Lemma test3 : O = O.
MProof.
  reflexivity.
Qed.

Require Import Omega.

Goal forall n : nat, n = 0 \/ n = 1 \/ n > 1.
Proof.
  intro n.
  omega.
Qed.

Lemma bar : forall x y : nat, x = y -> y = x.
Proof.
  intros x y H.
  apply sym_eq.
  exact H.
Qed.

Definition intro {A : Type} {q} (s : forall x : A, M (q x))
: M (forall x : A, q x) :=
  nu x,
  p <- s x;
  abs x p.

Lemma test4 : forall (p : Prop), p = p.
MProof.
  intro (fun x => reflexivity).
Qed.
