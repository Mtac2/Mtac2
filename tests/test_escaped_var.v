Require Import MetaCoq.MetaCoq.

Require Import Bool.Bool.

Definition anat : nat.
MProof.
  _ <- evar nat; ret 0.
MQed.

Definition escaped_evar : nat.
MProof.
x <- evar nat; ret x.
Fail MQed.
Admitted.