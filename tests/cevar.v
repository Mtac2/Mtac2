From Mtac2 Require Import Mtac2.
Import Mtac2.List.ListNotations.

Example ex1 (x y: nat) (H: x>y) (z: nat) : True.
MProof.
  M.Cevar _ [m:ahyp H mNone | ahyp y mNone | ahyp x mNone].
  (* wrong order of variables *)
  Fail M.Cevar _ [m:ahyp x mNone| ahyp H mNone| ahyp y mNone].
  (* dup variable *)
  Fail M.Cevar _ [m:ahyp x mNone| ahyp x mNone| ahyp y mNone].
  Unshelve.
  M.Cevar _ [m:ahyp H mNone| ahyp y (mSome 0)| ahyp x mNone].
  Unshelve.
  T.exact I.
Qed.

Example ex2 : forall (x y: nat) (H: x>y) (z:nat), True.
MProof.
  cintros (x y: nat) (H: x>y) (z: nat) {-
    e <- M.Cevar _ [m:ahyp H mNone| ahyp y mNone| ahyp x mNone];
    T.exact e
  -}. (* misses z in the evar, but it still works, why? *)
  Unshelve.
  T.exact I.
Qed.

Example ex3 : forall (x y: nat) (H: x>y), True.
MProof.
  (* wrong order of variables *)
  Fail cintros (x y: nat) (H: x>y) {-
    e <- M.Cevar True [m:ahyp x mNone| ahyp H mNone| ahyp y mNone];
    T.exact e
  -}.
  (* dup variable *)
  Fail cintros (x y: nat) (H: x>y) {-
    e <- M.Cevar True [m:ahyp x mNone| ahyp x mNone| ahyp y mNone];
    T.exact e
  -}.
  cintros (x y: nat) (H: x>y) {-
    e <- M.Cevar _ [m:ahyp H mNone| ahyp y (mSome x)| ahyp x mNone];
    T.exact e
  -}.
  Unshelve.
    (* not a variable *)
  Fail M.Cevar _ [m:ahyp (x > y) mNone| ahyp y (mSome x)| ahyp x mNone].
  T.exact I.
Qed.
