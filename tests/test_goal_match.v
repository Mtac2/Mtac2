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

Goal forall (x : nat) (H : x > 0) (y : bool), x = x.
MProof.
intros x H y.
match_goal ([[? a | (Q : a > 0) (z : nat) |- a = z ]] => reflexivity).
Qed.

Goal forall (x : nat) (H : x > 0) (y : bool), 0 + x = x.
MProof.
intros x H y.
match_goal ([[? a | (Q : a > 0) (z : nat) |- a = z ]] => apply (eq_refl a)).
Qed.

Goal forall (x : nat) (H : x > 0) (y : bool), 0 + x = x.
MProof.
intros x H y.
(* a is instantiated with x, and then when matching x with 0 + x it fails (as it should) *)
Fail match_goal_nored ([[? a | (Q : a > 0) (z : nat) |- a = z ]] => apply (eq_refl a)).
match_goal_nored ([[? a | (Q : a > 0) (z : nat) |- 0 + a = z ]] => apply (eq_refl a)).
Qed.
