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

Import M. Import M.notations.

Definition test_unfold := 1 + 1.
Set Unicoq Debug.
Fail Eval hnf in ltac:(mrun (
     A <- evar Type;
     t1 <- evar (A -> nat);
     t2 <- evar A;
     unify_or_fail UniMatchNoRed (t1 t2) test_unfold;;
     M.ret 0)).  (* Should fail: it shouldn't unfold test *)
