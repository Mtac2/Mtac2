From Mtac2 Require Import Mtac2 MTele MTeleMatch MFixDef MTeleMatchDef.


Definition Mtest : nat -> nat -> nat -> nat -> M nat :=
  Eval cbn [mfix' curry uncurry UNCURRY RETURN] in
  mfix' (m :=mTele (fun a1 => mTele (fun a2 => mTele (fun a3 => mTele (fun a4 => mBase)))))
        (fun a1 a2 a3 a4 => nat)
       (fun (rec : nat -> nat -> nat -> nat -> M nat) a b c d =>
          match (a, b, c, d) with
          | (0, 0, 0, 0) => M.ret 0
          | (0, 0, 0, o) => rec a b c (pred o)
          | (0, 0, m, o) => rec a b (pred m) o
          | (0, n, m, o) => rec a (pred n) m o
          | (l, n, m, o) => rec (pred l) n m o
          end).

Definition Mtest2 : nat -> nat -> nat -> nat -> M nat :=
  mfix4 rec (a : nat) (b : nat) (c : nat) (d : nat) : M nat :=
          match (a, b, c, d) with
          | (0, 0, 0, 0) => M.ret 0
          | (0, 0, 0, o) => rec a b c (pred o)
          | (0, 0, m, o) => rec a b (pred m) o
          | (0, n, m, o) => rec a (pred n) m o
          | (l, n, m, o) => rec (pred l) n m o
          end.

Time Compute ltac:(mrun
                (
                   Mtest 4000 4000 4000 4000
                )
             ).

Time Compute ltac:(mrun
                (
                   Mtest2 4000 4000 4000 4000
                )
             ).