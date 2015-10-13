Require Import MetaCoq.MetaCoq.
Import MetaCoqNotations.

Goal True.
MProof.
  munify True True;; ret I.
Qed.

Goal True.
MProof.
  Fail munify True False.
Abort.

Goal True.
MProof.
  ttry (munify True False;; raise exception) (fun e=>
    munify e (NotUnifiableException True False);; ret I).
Qed.
