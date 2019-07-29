From Mtac2 Require Import Datatypes List Mtac2.
Import Mtac2.lib.List.ListNotations.
Import T.

Require Import Bool.Bool.

Ltac induction n := induction n.

Definition qualify s := String.append "" s.

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
   | (m:_,AnyMetavar _ _ _) :m: _ => M.ret r
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

Goal forall n m,  S n = S m -> n = m.
MProof.
  intros n m H.
  ltac (qualify "injection") [m:Dyn H].
  trivial.
Qed.

(** Testing that we can chain ltac tactics that modify the context *)
Goal forall n m,  S n = S m -> n = m.
MProof.
  intros n m H.
  induction n &> induction m &> T.try trivial.
Abort.

Goal forall n m,  1 + n = S m -> n = m.
MProof.
  intros n m H.
  Ltac unf H := unfold Nat.add in H.
  ltac "unf" [m: Dyn H] &> (select (_ = _) >>= fun H' => ltac "injection" [m: Dyn H']).
  trivial.
Qed.
