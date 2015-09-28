Require Import Mtac2.Mtac2.
Import Mtac2Notations.

Definition exact {A : Type} (x : A) : M A :=
  ret x.

Lemma test1 : forall P, P -> P.
  MProof.
  exact (fun P x => x).
Qed.

Definition apply {B C : Type} (l : B -> C) : M C :=
  h <- evar B;
  ret (l h).

(* Lemma test2 : True.
MProof.
   apply (fun (x : True) => x).
   ret I.
 *)

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
Print bar.

Definition intro {A : Type} {q} (s : forall x : A, M (q x))
: M (forall x : A, q x) :=
  nu x,
  p <- s x;
  abs x p.

Lemma example2 : True -> True.
MProof.
  intro (fun x => ret x).

Qed.
Print example2.