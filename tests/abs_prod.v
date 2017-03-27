Require Import MetaCoq.MetaCoq.

Goal forall x:nat, True.
MProof.
  intro x.
  (aP <- M.abs_prod x (x <= 0);
  mmatch aP with (forall y, y <= 0:Type) => M.ret _ | _ => M.failwith "Didn't work" end)%MC.
Abort.
