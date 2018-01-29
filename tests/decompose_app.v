From Mtac2 Require Import Base MTele.
Definition test_tele : MTele :=
  mTele (fun x : nat =>
           mTele (fun y : nat => mBase)
        ).

Check ltac:(mrun (
                M.decompose_app'
                  (m:=test_tele)
                  (3+5)
                  (@plus)
                  (fun x y => M.ret (x,y)))
           ).

Definition prop_tele : MTele :=
  mTele (fun _ : Prop => mTele (fun _ : Prop => mBase)).

Check ltac:(mrun (
                M.decompose_app'
                  (m:=prop_tele)
                  (True \/ False)
                  (@or)
                  (fun x y => M.ret (x,y)))
           ).