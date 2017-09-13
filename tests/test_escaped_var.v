Require Import Mtac2.Mtac2.

Require Import Bool.Bool.
Import M.notations.

Definition anat : nat.
MProof.
  _ <- M.evar nat; M.ret 0.
MQed.

Definition escaped_evar : nat.
MProof.
x <- M.evar nat; M.ret x.
Fail MQed. (* OK, the goal was not solved *)
M.ret 0.
Fail MQed. (* OK, no need for MQed, no goal is open (although we might want to have MQed work here) *)
Qed.
