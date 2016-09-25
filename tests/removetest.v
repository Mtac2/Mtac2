Require Import MetaCoq.MetaCoq.

Example test_remove1 (x y z : nat) : x > y -> x > y.
MProof.
  Fail remove x (ret id). (* the meta-variable depends on it *)
  Fail remove (id z) (ret id). (* must be a variable *)
  remove z (ret id). (* z is not required for the proof *)
Qed.

Example test_remove2 (z y x : nat) : x > y -> x > y.
MProof.
  remove z (ret id). (* z is not required for the proof *)
Qed.

Example test_remove3 : forall x y z : nat, x > y -> x > y.
MProof.
  (* z is not required for the proof *)
  nu x, nu y, nu z : nat,
   r1 <- remove z (ret id);
   r2 <- abs_fun z r1;
   r3 <- abs_fun (P:=fun y=>forall z, x > y -> x > y)  y r2;
   abs_fun (P:=fun x=>forall y, nat -> x > y -> x > y) x r3.
Qed.

Example test_remove4 : forall z x y : nat, x > y -> x > y.
MProof.
  (* z is not required for the proof *)
  nu z, nu x, nu y : nat,
   r1 <- remove z (ret id);
   r2 <- abs_fun y r1;
   r3 <- abs_fun (P:= fun x =>forall y : nat, x > y -> x > y) x r2;
   abs_fun z r3.
Qed.
