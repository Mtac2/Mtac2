Require Import Mtac2.Mtac2.
Import Mtac2Notations.

Goal True.
MProof.
  bind (ret I) (fun r => ret r).
Qed.

Goal True.
MProof.
  r <- ret I; ret r.
Qed.