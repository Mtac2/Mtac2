Require Import MetaCoq.MetaCoq.
Import MetaCoqNotations.

Goal True.
MProof.
  munify True True (fun _=>True) (fun _=>ret I).
Qed.

Goal True.
MProof.
  Fail munify True False (fun _=>True) (fun _=>ret I).
Abort.

Goal True.
MProof.
  ttry (munify True False (fun _=>True) (fun _=>ret I)) (fun e=>
    munify e (NotUnifiableException True False) (fun _=>True) (fun _=>ret I)).
Qed.
