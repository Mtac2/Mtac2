From MetaCoq Require Import MetaCoq.

Definition ex1 := fun x:nat=>ltac:(mrun (ret x)).

Definition ex2 := fun x y:nat=>ltac:(mrun (ret (x + y))).

Definition ex3 := fun (x y:nat) (H : x < y) =>ltac:(mrun (ret H)).

Section test.

Variable x : nat.

Definition ex4 := fun x y:nat=>ltac:(mrun (ret (x + y))).

(* It is interpreting that the x comes from the Variable *)
Definition testex4 : ex4 = (fun x y:nat=>x + y) := eq_refl.
