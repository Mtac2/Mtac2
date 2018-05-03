From Mtac2 Require Import Mtac2.

Goal True -> True.
MProof.
Fail T.intro_base (TheName "x x") (fun _=>T.idtac). (* it is failing with a failure, not an exception *)
Abort.