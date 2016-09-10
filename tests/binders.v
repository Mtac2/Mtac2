Require Import MCImports.

Example nu_new_name_works : forall x:nat, 0 <= x.
MProof.
  tnu "x" None (fun y=>abs y (le_0_n y)).
Qed.

Example nu_existing_name_fails (x: nat) : forall y:nat, 0 <= y.
MProof.
  mtry tnu "x" None (fun y=>abs y (le_0_n y)) with NameExistsInContext "x"=>ret _ end.
Abort.
