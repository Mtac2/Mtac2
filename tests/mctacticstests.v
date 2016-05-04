Require Import MetaCoq.MCTactics.
Require Import Bool.Bool.
Require Import Lists.List.

Import ListNotations.
Import MetaCoqNotations.
Import MCTacticsNotations.

Goal True.
MProof.
  exact I.
Qed.

Goal False.
MProof.
  Fail exact I.
Abort.

Example fail_not_var : 0 = 0.
MProof.
  Fail destruct 0.
Abort.

Example ex_destr (n:nat) : n = n.
MProof.
  destruct n.
  - reflexivity.
  - intro n'.
    reflexivity.
Qed.

Goal forall b : bool, b = b.
MProof.
  intro b.
  - bbind (destruct b) [reflexivity; reflexivity].
Qed.

Goal forall b1 : bool, b1 = b1.
MProof.
  bbind (intro b1) [reflexivity].
Qed.

Goal forall b1 b2 b3 : bool, b1 && b2 && b3 = b3 && b2 && b1.
MProof.
  bindb (intro b1) (bindb (intro b2) (intro b3)).
  bindb (destruct b1) (bindb (destruct b2) ((bindb (destruct b3) reflexivity))).
Qed.

Goal forall b1 b2 b3 : bool, b1 && b2 && b3 = b3 && b2 && b1.
MProof.
  intro b1 ;; intro b2 ;; intro b3.
  destruct b1 ;; destruct b2 ;; destruct b3 ;; reflexivity.
Qed.

Goal forall b1 b2 b3 : bool, b1 && b2 && b3 = b3 && b2 && b1.
MProof.
  intros b1 ;; intros b2 b3.
  destruct b1 ;; destruct b2 ;; destruct b3 ;; reflexivity.
Qed.

Goal forall b1 b2 : bool, b1 && b2 = b2 && b1.
MProof.
  cintros b1 b2 {-
    destruct b1 ;; destruct b2 ;; reflexivity
  -}.
Qed.

Goal forall b1 b2 b3 : bool, b1 && b2 && b3 = b3 && b2 && b1.
MProof.
  cintros b1 b2 {-
    destruct b1 ;; destruct b2 ;;
    cintro b3 {- destruct b3 ;; reflexivity -}
  -}.
Qed.

Goal (forall x, x > 0) -> 3 > 0.
MProof.
  intro H.
  apply H.
Qed.

Goal (forall x, x > 0) -> 3 > 0.
MProof.
  cintro H {- apply H -}.
Qed.

Goal (forall x y, x > y \/ y < x -> x <> y) -> 3 <> 0.
MProof.
  cintro H {- apply H;; left;; omega -}.
Qed.
