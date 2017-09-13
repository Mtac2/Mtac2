Require Import Mtac2.Mtac2.

Definition test {A} (o : M (option A)) : M _ :=
  o <- o;
  match o with Some x => M.ret x | _ => M.raise exception end.

Goal True = True.
MProof.
  test (M.unify True True UniCoq).
Qed.

Goal True = False.
MProof.
  Fail test (M.unify True False UniCoq).
Abort.
