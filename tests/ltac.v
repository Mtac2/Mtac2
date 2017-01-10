From MetaCoq
Require Import MetaCoq.

Require Import Bool.Bool.

Ltac induction n := induction n.

Definition qualify s := String.append "ltac." s.

Definition induction {A} (n:A) : tactic := ltac (qualify "induction") [Dyn n].

Goal forall n:nat, 0 <= n.
MProof.
  intros.
  induction n &> [apply le_n; apply le_S&> assumption].
Qed.


Goal forall m n:nat, 0 <= n.
MProof.
  intros.
  (* m shouldn't be in the list of hypotheses, as it is shared *)
  (fun g=>r <- induction n g;
   match r with
   | (Goal _ :: _) => ret r
   | _ => raise exception
   end) &> [apply le_n; apply le_S&> assumption].
Qed.

Ltac myapply H := apply H.
Definition apply' := qualify "myapply".

Ltac remove H := clear H.
Definition remove := qualify "remove".

Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  intros P Q f x.
  apply f.
  ltac remove [Dyn f].
  exact x.
Qed.

Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  intros P Q f x.
  select (_->_) (fun g=>ltac apply' [Dyn g]) &> assumption.
Qed.

Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  intros P Q.
  cintros f x {-
    ltac apply' [Dyn f] &> ltac apply' [Dyn x]
  -}.
Qed.

Ltac injection x := injection x.

Goal forall n m,  S n = S m -> n = m.
MProof.
  intros n m H.
  ltac (qualify "injection") [Dyn H].
  trivial.
Qed.