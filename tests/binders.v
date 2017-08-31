Require Import MetaCoq.Datatypes MetaCoq.MetaCoq.

Example nu_new_name_works : forall x:nat, 0 <= x.
MProof.
  M.nu "x" None (fun y=> M.abs_fun y (le_0_n y)).
Qed.

Example nu_existing_name_fails (x: nat) : forall y:nat, 0 <= y.
MProof.
  (mtry M.nu "x" None (fun y=>M.abs_fun y (le_0_n y)) with NameExistsInContext "x"=>M.ret _ end)%MC.
Abort.

Example nu_returning_x_fails (x: nat) : forall y:nat, 0 <= y.
MProof.
  (mtry M.nu "z" None (fun y=>M.ret y) with VarAppearsInValue => M.ret _ end)%MC.
Abort.
