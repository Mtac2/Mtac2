Require Import MetaCoq.MetaCoq.

Example ex1 (x y: nat) (H: x>y) (z: nat) : True.
MProof.
  Cevar _ [ahyp H None; ahyp y None; ahyp x None].
  (* wrong order of variables *)
  Fail Cevar _ [ahyp x None; ahyp H None; ahyp y None].
  (* dup variable *)
  Fail Cevar _ [ahyp x None; ahyp x None; ahyp y None].
  Cevar _ [ahyp H None; ahyp y (Some 0); ahyp x None].
  exact I.
Qed.

Import TacticOverload.
Example ex2 : forall (x y: nat) (H: x>y) (z:nat), True.
MProof.
  Fail cintros (x y: nat) (H: x>y) (z: nat) {-
    e <- Cevar _ [ahyp H None; ahyp y None; ahyp x None];
    exact e
  -}. (* misses z in the evar *)

  cintros (x y: nat) (H: x>y) (z: nat) {-
    e <- Cevar True [ahyp H None; ahyp y None; ahyp x None];
    exact e
  -}.
   exact I.
Qed.

Example ex3 : forall (x y: nat) (H: x>y), True.
MProof.
  (* wrong order of variables *)
  Fail cintros (x y: nat) (H: x>y) {-
    e <- Cevar True [ahyp x None; ahyp H None; ahyp y None];
    exact e
  -}.
  (* dup variable *)
  Fail cintros (x y: nat) (H: x>y) {-
    e <- Cevar True [ahyp x None; ahyp x None; ahyp y None];
    exact e
  -}.
  cintros (x y: nat) (H: x>y) {-
    e <- Cevar _ [ahyp H None; ahyp y (Some x); ahyp x None];
    exact e
  -}.
  (* not a variable *)
  Fail Cevar _ [ahyp (x > y) None; ahyp y (Some x); ahyp x None].
  exact I.
Qed.
