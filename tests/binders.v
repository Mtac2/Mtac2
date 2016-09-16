Require Import MetaCoq.MetaCoq.

Example nu_new_name_works : forall x:nat, 0 <= x.
MProof.
  tnu "x" None (fun y=>abs y (le_0_n y)).
Qed.

Example nu_existing_name_fails (x: nat) : forall y:nat, 0 <= y.
MProof.
  mtry tnu "x" None (fun y=>abs y (le_0_n y)) with NameExistsInContext "x"=>ret _ end.
Abort.

Example nu_returning_x_fails (x: nat) : forall y:nat, 0 <= y.
MProof.
  mtry tnu "z" None (fun y=>ret y) with [? s] Failure s =>print s;; ret _ end.
Abort.
