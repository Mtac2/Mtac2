From Mtac2 Require Import Datatypes List Mtac2.
Import Mtac2.List.ListNotations.
Import T.

Require Import Bool.Bool.

Ltac induction n := induction n.

Definition qualify s := String.append "ltac." s.

Definition induction {A} (n:A) : tactic := ltac (qualify "induction") [m:Dyn n].

Goal forall n:nat, 0 <= n.
MProof.
  intros n.
  induction n &> [m:apply le_n| apply le_S;; assumption].
Qed.


Goal forall m n:nat, 0 <= n.
MProof.
  intros m n.
  (* m shouldn't be in the list of hypotheses, as it is shared *)
  (\tactic g =>
   r <- induction n g;
   match r with
   | (m:_,Goal _ _) :m: _ => M.ret r
   | _ => M.raise exception
   end) &> [m:apply le_n| apply le_S;; assumption].
Qed.

Ltac myapply H := apply H.
Definition apply' := qualify "myapply".

Ltac remove H := clear H.
Definition remove := qualify "remove".

Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  intros P Q f x.
  apply f.
  ltac remove [m:Dyn f].
  exact x.
Qed.

Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  intros P Q f x.
  g <- select (_->_); ltac apply' [m:Dyn g] ;; assumption.
Qed.

Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  intros P Q.
  cintros f x {-
    ltac apply' [m:Dyn f] ;; ltac apply' [m:Dyn x]
  -}.
Qed.

Ltac injection x := injection x.
Require Import Coq.Init.Logic.

Goal forall n m,  S n = S m -> n = m.
MProof.
  intros n m H.
  ltac (qualify "injection") [m:Dyn H].
  trivial.
Qed.
