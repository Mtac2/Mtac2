Require Import MetaCoq.MetaCoq.


Axiom block : M nat.

Fail Definition block_fails := ltac:(mrun block).

Definition block_raises_failure :=
  ltac:(mrun (mtry block with StuckTerm => ret 0 end)).

Example simple_ex :=
  ltac:(mrun (mtry raise exception with exception => ret 0 end)).

Definition AnException (n : nat) : Exception. exact exception. Qed.
Example closed_ex :=
  ltac:(mrun (mtry raise (AnException 0) with [? n] AnException n => ret n end)).

Example not_closed_but_closed (m : nat) :=
  ltac:(mrun (mtry raise (AnException m) with [? n] AnException n => ret n end)).

Example nu_not_closed_raise_not_closed  :=
  ltac:(mrun (mtry \nu x:nat, raise (AnException x) with ExceptionNotGround => ret 0 end)).

Example evar_not_closed_raise_not_closed  :=
  ltac:(mrun (mtry e <- evar nat; raise (AnException e) with ExceptionNotGround => ret 0 end)).

Example evar_closed_is_fine  :=
  ltac:(mrun (mtry e <- evar nat; munify e 0 UniCoq;; raise (AnException e) with [? n] AnException n => ret n end)).
