From Mtac2 Require Import Mtac2.

Goal True -> True.
MProof.
mtry (T.intro_base (TheName "x x") (fun _=>T.idtac)) with [? x] InvalidName x => T.idtac end.
mtry (T.intro_base (FreshFromStr "x x") (fun _=>T.idtac)) with [? x] InvalidName x => T.idtac end.
Abort.