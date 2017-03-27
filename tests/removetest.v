Require Import MetaCoq.MetaCoq.

Example test_remove1 (x y z : nat) : x > y -> x > y.
MProof.
  Fail M.remove x (M.ret id). (* the meta-variable depends on it *)
  Fail M.remove (id z) (M.ret id). (* must be a variable *)
  M.remove z (M.ret id). (* z is not required for the proof *)
Qed.

Example test_remove2 (z y x : nat) : x > y -> x > y.
MProof.
  M.remove z (M.ret id). (* z is not required for the proof *)
Qed.

Example test_remove3 : forall x y z : nat, x > y -> x > y.
MProof.
  (* z is not required for the proof *)
  (\nu x, \nu y, \nu z : nat,
   r1 <- M.remove z (M.ret id);
   r2 <- M.abs_fun z r1;
   r3 <- M.abs_fun (P:=fun y=>forall z, x > y -> x > y)  y r2;
   M.abs_fun (P:=fun x=>forall y, nat -> x > y -> x > y) x r3)%MC.
Qed.

Example test_remove4 : forall z x y : nat, x > y -> x > y.
MProof.
  (* z is not required for the proof *)
  (\nu z, \nu x, \nu y : nat,
   r1 <- M.remove z (M.ret id);
   r2 <- M.abs_fun y r1;
   r3 <- M.abs_fun (P:= fun x =>forall y : nat, x > y -> x > y) x r2;
   M.abs_fun z r3)%MC.
Qed.
