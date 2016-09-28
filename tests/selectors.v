Require Import MetaCoq.MetaCoq.

Example test_selector1 : forall n, n >= 0.
MProof.
  destructn 0 &> sfirst &> apply le_0_n.
Abort.

Example test_selector2 : forall n, n >= 0.
MProof.
  destructn 0 &> srev &> slast &> apply le_0_n.
Abort.

Example test_selector3 : forall n, n >= 0.
MProof.
  destructn 0 &1> apply le_0_n.
Abort.

Example test_selector4 : forall n, n >= 0.
MProof.
  destructn 0 &> srev &n> apply le_0_n.
Abort.