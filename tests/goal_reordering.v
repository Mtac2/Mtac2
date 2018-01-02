Require Import Mtac2.Mtac2.

Goal True.
MProof.
  (M.evar nat;; M.evar bool;; M.ret _)%MC. (* FIXME: why are all evars shelved when we do this in the tactic monad? *)
  Unshelve.
  M.ret _.
  Unshelve.
  M.ret _.
  Unshelve.
  M.ret true.
  Unshelve.
  M.ret I.
  M.ret 0.
Qed.

Definition ThrowANat (n : nat) : Exception. exact exception. Qed.
Definition test n : M nat :=
  mmatch n with
  | [? n'] S n' => M.raise (ThrowANat n')
  | _ => M.ret 0
  end.

Goal True.
MProof.
  M.mtry' (test 1;; M.ret I) (fun _=> M.ret I).
Qed.

Goal {n:nat| n = n}.
MProof.
  (mtry test 1;; M.raise exception
  with [? n'] ThrowANat n' => M.ret (exist _ n' _) end)%MC.
Abort.


Goal {n:nat| n = n}.
MProof.
  (mmatch 2 + 4 with
  | [? n] n + n => M.ret (exist _ (n + n) eq_refl)
  | [? n] n + n => M.ret (exist _ (n + n) eq_refl)
  | [? n] n + n => M.ret (exist _ (n + n) eq_refl)
  | [? n] n + n => M.ret (exist _ (n + n) eq_refl)
  | [? n m] n + m => M.ret (exist (fun n=>n=n) (n + m) eq_refl)
  end)%MC.
Qed.
