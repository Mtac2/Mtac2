Require Import MetaCoq.MetaCoq.


Axiom block : M nat.

Fail Definition block_fails := ltac:(mrun block).

Definition block_raises_failure :=
  ltac:(mrun (mtry block with StuckTerm => M.ret 0 end)%MC).

Example simple_ex :=
  ltac:(mrun (mtry M.raise exception with exception => M.ret 0 end)%MC).

Definition AnException (n : nat) : Exception. exact exception. Qed.
Example closed_ex :=
  ltac:(mrun (mtry M.raise (AnException 0) with [? n] AnException n => M.ret n end)%MC).

Example not_closed_but_closed (m : nat) :=
  ltac:(mrun (mtry M.raise (AnException m) with [? n] AnException n => M.ret n end)%MC).

Example nu_not_closed_raise_not_closed  :=
  ltac:(mrun (mtry \nu x:nat, M.raise (AnException x) with ExceptionNotGround => M.ret 0 end)%MC).

Example evar_not_closed_raise_not_closed  :=
  ltac:(mrun (mtry e <- M.evar nat; M.raise (AnException e) with ExceptionNotGround => M.ret 0 end)%MC).

Example evar_closed_is_fine  :=
  ltac:(mrun (mtry e <- M.evar nat; M.unify e 0 UniCoq;; M.raise (AnException e) with [? n] AnException n => M.ret n end)%MC).
