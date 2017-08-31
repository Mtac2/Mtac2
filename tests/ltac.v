From MetaCoq Require Import Logic List Datatypes MetaCoq.
Import MetaCoq.List.ListNotations.
Import T.

Require Import Bool.Bool.

Ltac induction n := induction n.

Definition qualify s := String.append "ltac." s.

Definition induction {A} (n:A) : tactic := ltac (qualify "induction") [mc:Dyn n].

Goal forall n:nat, 0 <= n.
MProof.
  intros n.
  induction n &> [mc:apply le_n; apply le_S;; assumption].
Qed.


Goal forall m n:nat, 0 <= n.
MProof.
  intros m n.
  (* m shouldn't be in the list of hypotheses, as it is shared *)
  (\tactic g =>
   r <- induction n g;
   match r with
   | ((_,Goal _) :: _) => M.ret r
   | _ => M.raise exception
   end) &> [mc:apply le_n; apply le_S;; assumption].
Qed.

Ltac myapply H := apply H.
Definition apply' := qualify "myapply".

Ltac remove H := clear H.
Definition remove := qualify "remove".

Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  intros P Q f x.
  apply f.
  ltac remove [mc:Dyn f].
  exact x.
Qed.

Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  intros P Q f x.
  select (_->_) (fun g=>ltac apply' [mc:Dyn g]) ;; assumption.
Qed.

Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  intros P Q.
  cintros f x {-
    ltac apply' [mc:Dyn f] ;; ltac apply' [mc:Dyn x]
  -}.
Qed.

Ltac injection x := injection x.
Require Import Coq.Init.Logic.

Goal forall n m,  S n = S m -> n = m.
MProof.
  intros n m H.
  ltac (qualify "injection") [mc:Dyn H].
  trivial.
Qed.