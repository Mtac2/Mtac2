Require Import MetaCoq.MetaCoq.
Require Import MetaCoq.MCTactics.
Import MetaCoqNotations.

Definition test {A} (o : M (option A)) :=
  o <- o;
  match o with Some x => ret x | _ => raise exception end.

Goal True = True.
MProof.
  test (munify True True UniCoq).
Qed.

Goal True = False.
MProof.
  Fail test (munify True False UniCoq).
Abort.
