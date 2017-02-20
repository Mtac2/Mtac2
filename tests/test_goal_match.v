Require Import MetaCoq.MetaCoq.

Goal forall x : nat, forall y : bool, True.
MProof.
intros x y.
(* works *)
match_goal with [[ (x : nat) (y : bool) |- _ ]] => idtac end.
match_goal with [[ (y : bool) (y : nat) |- _ ]] => idtac end.
(* it should fail *)
Fail match_goal with [[ (x : nat) (y : nat) |- _ ]] => idtac end.
exact I.
Qed.

Goal forall (x : nat) (H : x > 0) (y : bool), True.
MProof.
intros x H y.
(* works *)
match_goal with [[ (x : nat) (y : bool) |- _ ]] => idtac end.
match_goal with [[ (y : bool) (y : nat) |- _ ]] => idtac end.
match_goal with [[ (z : nat) (Q : z > 0) |- _ ]] => idtac end.
match_goal with [[ (z : nat) (w : bool) (Q : z > 0) |- _ ]] => idtac end.
match_goal with [[ (w : bool) (z : nat) (Q : z > 0) |- _ ]] => idtac end.
match_goal with [[ (Q : x > 0) (z : nat) |- _ ]] => idtac end.

(* it should fail *)
Fail match_goal ([[ (x : nat) (y : nat) |- _ ]] => idtac).
exact I.
Qed.

Goal forall (x : nat) (H : x > 0) (y : bool), x = x.
MProof.
intros x H y.
match_goal with [[ (Q : x > 0) (z : nat) |- x = z ]] => reflexivity end.
Qed.

Goal forall (x : nat) (H : x > 0) (y : bool), x = x.
MProof.
intros x H y.
match_goal with [[? a | (Q : a > 0) (z : nat) |- a = z ]] => reflexivity end.
Qed.

Goal forall (x : nat) (H : x > 0) (y : bool), 0 + x = x.
MProof.
intros x H y.
match_goal with [[? a | (Q : a > 0) (z : nat) |- a = z ]] => apply (eq_refl a) end.
Qed.

Goal forall (x : nat) (H : x > 0) (y : bool), 0 + x = x.
MProof.
intros x H y.
match_goal with
| [[? a |- a = a + a ]] => idtac
| [[? a | (Q : a > 0) (z : nat) |- a = z ]] => apply (eq_refl a)
| [[? a : nat |- a = a ]] => fail (Failure "should not happen")
end.
Qed.

Goal forall (x : nat) (H : x > 0) (y : bool), 0 + x = x.
MProof.
intros x H y.
(* a is instantiated with x, and then when matching x with 0 + x it fails (as it should) *)
Fail match_goal_nored with [[? a | (Q : a > 0) (z : nat) |- a = z ]] => apply (eq_refl a) end.
match_goal_nored with [[? a | (Q : a > 0) (z : nat) |- 0 + a = z ]] => apply (eq_refl a) end.
Qed.
