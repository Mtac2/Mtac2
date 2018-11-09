From Mtac2 Require Import Mtac2.
Import M.
Import M.notations.

Goal True.
MProof.
  (* unequal *)
  unify_cnt (B:=fun x=>x) UniCoq True False (failwith "equal?") (ret I).
Qed.

Goal True.
MProof.
  (* equal *)
  unify_cnt (B:=fun x=>x) UniCoq True True (ret I) (failwith "not equal?").
Qed.

Goal True.
MProof.
  (* unreduced Reduction: it shouldn't work *)
  pose (r := UniCoq).
  mtry
    unify_cnt (B:=fun _=>_) r True True (failwith "equal?") (failwith "not equal?")
  with NotAUnifStrategy => ret I end.
Qed.
