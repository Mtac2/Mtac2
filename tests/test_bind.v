Require Import MetaCoq.MCTactics.
Import MetaCoqNotations.

Goal True.
MProof.
  bind (ret I) (fun r => ret r).
Qed.

Goal True.
MProof.
  r <- ret I; ret r.
Qed.
