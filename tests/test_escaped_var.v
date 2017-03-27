Require Import MetaCoq.MetaCoq.

Require Import Bool.Bool.

Definition anat : nat.
MProof.
  (_ <- M.evar nat; M.ret 0)%MC.
MQed.

Definition escaped_evar : nat.
MProof.
x <- M.evar nat; M.ret x.
Fail MQed.
Admitted.