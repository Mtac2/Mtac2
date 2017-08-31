From MetaCoq Require Import Logic List Datatypes MetaCoq.
Import MetaCoq.List.ListNotations.

Example ex1 (x y: nat) (H: x>y) (z: nat) : True.
MProof.
  M.Cevar _ [mc:ahyp H None; ahyp y None; ahyp x None].
  (* wrong order of variables *)
  Fail M.Cevar _ [mc:ahyp x None; ahyp H None; ahyp y None].
  (* dup variable *)
  Fail M.Cevar _ [mc:ahyp x None; ahyp x None; ahyp y None].
  M.Cevar _ [mc:ahyp H None; ahyp y (Some 0); ahyp x None].
  T.exact I.
Qed.

Example ex2 : forall (x y: nat) (H: x>y) (z:nat), True.
MProof.
  cintros (x y: nat) (H: x>y) (z: nat) {-
    e <- M.Cevar _ [mc:ahyp H None; ahyp y None; ahyp x None];
    T.exact e
  -}. (* misses z in the evar, but it still works, why? *)
  Unshelve.
  T.exact I.
Qed.

Example ex3 : forall (x y: nat) (H: x>y), True.
MProof.
  (* wrong order of variables *)
  Fail cintros (x y: nat) (H: x>y) {-
    e <- M.Cevar True [mc:ahyp x None; ahyp H None; ahyp y None];
    T.exact e
  -}.
  (* dup variable *)
  Fail cintros (x y: nat) (H: x>y) {-
    e <- M.Cevar True [mc:ahyp x None; ahyp x None; ahyp y None];
    T.exact e
  -}.
  cintros (x y: nat) (H: x>y) {-
    e <- M.Cevar _ [mc:ahyp H None; ahyp y (Some x); ahyp x None];
    T.exact e
  -}.
  (* not a variable *)
  Fail M.Cevar _ [mc:ahyp (x > y) None; ahyp y (Some x); ahyp x None].
  Unshelve.
  T.exact I.
Qed.
