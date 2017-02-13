Require Import MetaCoq.MetaCoq.

Goal forall x : nat, forall y : bool, True.
MProof.
intros x y.
(* works *)
match_goal ([[ (x : nat) (y : bool) |- _ ]] => idtac).
match_goal ([[ (y : bool) (y : nat) |- _ ]] => idtac).
(* it should fail *)
Fail match_goal ([[ (x : nat) (y : nat) |- _ ]] => idtac).
exact I.
Qed.

Goal forall (x : nat) (H : x > 0) (y : bool), True.
MProof.
intros x H y.
(* works *)
match_goal ([[ (x : nat) (y : bool) |- _ ]] => idtac).
match_goal ([[ (y : bool) (y : nat) |- _ ]] => idtac).
match_goal ([[ (z : nat) (Q : z > 0) |- _ ]] => idtac).
match_goal ([[ (z : nat) (w : bool) (Q : z > 0) |- _ ]] => idtac).
match_goal ([[ (w : bool) (z : nat) (Q : z > 0) |- _ ]] => idtac).
match_goal ([[ (Q : x > 0) (z : nat) |- _ ]] => idtac).

(* it should fail *)
Fail match_goal ([[ (x : nat) (y : nat) |- _ ]] => idtac).
exact I.
Qed.

Goal forall (x : nat) (H : x > 0) (y : bool), x = x.
MProof.
intros x H y.
match_goal ([[ (Q : x > 0) (z : nat) |- x = z ]] => reflexivity).
Qed.
