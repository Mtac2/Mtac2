Require Import MetaCoq.MetaCoq.

Example test_selector1 : forall n, n >= 0.
MProof.
  destructn 0 &> sfirst (apply le_0_n).
Abort.

Example test_selector2 : forall n, n >= 0.
MProof.
  destructn 0 &> srev &> slast (apply le_0_n).
Abort.

Example test_selector3 : forall n, n >= 0.
MProof.
  destructn 0 |1> apply le_0_n.
Abort.

Example test_selector4 : forall n, n >= 0.
MProof.
  destructn 0 &> srev l> apply le_0_n.
Abort.

Example test_selector5 : forall n, n >= 0.
MProof.
  destructn 0 &> srev |2> apply le_0_n.
Abort.

Example test_selector6 : forall n, n >= 0.
MProof.
  (destructn 0 &> srev |2> apply le_0_n) |1> idtac.
Abort.

Example test_selector7 : forall n, n >= 0.
MProof.
  Fail (destructn 0 &> srev |2> apply le_0_n) |2> print_goal.
Abort.
