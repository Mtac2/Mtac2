Require Import MetaCoq.MetaCoq.

Goal forall x, 0 + x = S x -> False.
MProof.
  intros x H.
  T.unfold_in plus H.
Abort.
