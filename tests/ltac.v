From MetaCoq
Require Import MetaCoq.

Require Import Bool.Bool.

Ltac induction n := induction n.

Definition qualify s := String.append "ltac." s.

Definition induction {A} (n:A) : tactic := ltac (qualify "induction") [Dyn n].

Goal forall n:nat, 0 <= n.
MProof.
  intros.
  induction n&> [apply le_n; apply le_S&> assumption].
Qed.


Goal forall m n:nat, 0 <= n.
MProof.
  intros.
  (* m shouldn't be in the list of hypotheses, as it is shared *)
  (fun g=>r <- induction n g;
   match r with
   | (TheGoal _ :: _) => ret r
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
  (* WHAT? it is not closing the goal with x, although it should *)
  (fun g=>r <- ltac remove [Dyn f] g; print_term r;; ret r):tactic.
Abort.

Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  intros P Q f x.
  Fail select (_->_) (fun g=>ltac apply' [Dyn g]). (* WHAT?? It says  "Unknown existential variable" *)
Abort.

Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  intros P Q.
  (* with indices it should work too *)
  Fail cintros f x {-
    ltac apply' [Dyn f]&> ltac apply' [Dyn x]
  -}.
Abort.
