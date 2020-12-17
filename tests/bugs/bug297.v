From Mtac2 Require Import Mtac2.

Parameter x : moption nat.
Definition test : M nat :=
  mtry (M.nu Generate x (fun x=>M.ret 0))
  with StuckTerm => M.ret 0 end.

Mtac Do test.
