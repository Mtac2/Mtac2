Require Import MetaCoq.MetaCoq.

Import TacticUnoverload.

Goal forall x:nat, True.
MProof.
  intro x.
  aP <- abs_prod x (x <= 0);
  mmatch aP with (forall y, y <= 0:Type) => ret _ | _ => failwith "Didn't work" end.
Abort.
