Require Import Mtac2.Mtac2.

Goal True -> True -> True.
MProof.
  pintros \x y //.
Qed.

Goal nat -> True -> True.
MProof.
  pintros [| ~~ | \x ] \t //.
Qed.

Goal forall x y z : nat, x = y -> x + z = y + z.
MProof.
  pintros \x y z r> //.
Qed.

Goal forall x y z : nat, x = y -> x + z = y + z.
MProof.
  pintros \x y z <l //.
Qed.

Goal forall x y z : nat, x + z = y + z.
MProof.
  Fail pintros \x y z //. (* expected: not done *)
Abort.

Goal forall x z : nat, (forall y, y+0 = y) -> x + z = z + x.
MProof.
  (* is there a way to avoid the parens here? *)
  (pintros [| ~~ | \x'] [| ~~ | \z'] /=) &> [i: // | r> // | r> // | \IH].
Abort.
