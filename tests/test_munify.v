Require Import Mtac2.Mtac2.

Definition test {A} (o : M (moption A)) : M _ :=
  o <- o;
  match o with mSome x => M.ret x | _ => M.raise exception end.

Goal True =m= True.
MProof.
  test (M.unify True True UniCoq).
Qed.

Goal True =m= False.
MProof.
  Fail test (M.unify True False UniCoq).
Abort.
