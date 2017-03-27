From MetaCoq Require Import MetaCoq.

Definition ex1 := fun x:nat=>ltac:(mrun (M.ret x)).

Definition ex2 := fun x y:nat=>ltac:(mrun (M.ret (x + y))).

Definition ex3 := fun (x y:nat) (H : x < y) =>ltac:(mrun (M.ret H)).

Section test.

Variable x : nat.

Definition ex4 := fun x y:nat=>ltac:(mrun (M.ret (x + y))).

Definition ex4l := fun x y:nat=>ltac:(exact (x + y)).

Definition ex4plain := fun x y:nat=>x + y.

(* It is interpreting that the x comes from the Variable. That
   is a bug in Coq. For the moment we take it as if that is the
   expected behavior.  *)
Definition testex4 : ex4 = ex4l := eq_refl.

(* We do what must be done: rewrite x to be x0 *)
Definition ex5_eval := fun x y:nat=>M.eval (M.ret (x + y)).

Definition testex5 : ex5_eval = ex4plain := eq_refl.

End test.