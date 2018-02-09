From Mtac2 Require Import Base Datatypes Tactics.
Import M.
Import M.notations.

Goal True.
MProof.
  Fail raise _. (* should say "ExceptionNotGround" *)
  Mtac Do Set_Debug_Exceptions.
  Fail raise _. (* should print ?e *)
  Fail nu "P" mNone (fun P:True=>M.ret P). (* should print P *)
  Fail (_:M True). (* should print "StuckTerm ?t" *)
  Mtac Do Unset_Debug_Exceptions.
  Fail (_:M True). (* shoudn't print anything *)
  M.ret I.
Qed.
