From Mtac2 Require Import Base MTele.
Definition test_tele : MTele :=
  mTele (fun x : nat =>
           mTele (fun y : nat => mBase)
        ).

Check ltac:(mrun (
                M.decompose_app'
                  (m:=test_tele)
                  (p:=pBase)
                  (3+5)
                  (@plus)
                  (Logic.meq_refl)
                  (fun x y => M.ret (x,y)))
           ).

Check ltac:(mrun (
                M.decompose_app'
                  (m:=test_tele)
                  (p:=pTele _ pBase)
                  (3+5)
                  (T := fun (n m : nat) => nat)
                  (@plus)
                  (Logic.meq_refl)
                  (fun y => M.ret (y)))
           ).

Definition prop_tele : MTele :=
  mTele (fun _ : Prop => mTele (fun _ : Prop => mBase)).

Check ltac:(mrun (
                M.decompose_app'
                  (m:=prop_tele)
                  (p:=pBase)
                  (True \/ False)
                  (@or)
                  (Logic.meq_refl)
                  (fun x y => M.ret (x,y)))
           ).