From Mtac2 Require Import Base Datatypes.

Goal True.
MProof.
  M.ret I.
Qed.
Import M.notations.
Goal forall P:Type, forall x: P, P.
MProof.
  Mtac Do Set_Trace.
  M.nu "P" mNone (fun P:Type=>M.nu "x" mNone (fun x:P=> M.abs_fun x x >>= M.abs_fun P)).
  Mtac Do Unset_Trace.
Qed.

Goal True.
MProof.
  M.ret I. (* no more tracing *)
Qed.
