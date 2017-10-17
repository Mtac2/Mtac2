Require Import Mtac2.Mtac2.

Goal True -> True -> True.
MProof.
  i:\x y //.
Qed.

Goal nat -> True -> True.
MProof.
  i:[| ~~ | \x ] \t //.
Qed.

Goal forall x y z : nat, x = y -> x + z = y + z.
MProof.
  i:\x y z r> //.
Qed.

Goal forall x y z : nat, x = y -> x + z = y + z.
MProof.
  i:\x y z <l //.
Qed.

Goal forall x y z : nat, x + z = y + z.
MProof.
  Fail i:\x y z //. (* expected: not done *)
Abort.

Goal forall x z : nat, (forall y, y+0 = y) -> x + z = z + x.
MProof.
  i:[| ~~ | \x'] [| ~~ | \z'] /=.
  - i://.
  - i:r> //.
  - i:r> //.
Abort.
