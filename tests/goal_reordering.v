Require Import MetaCoq.MetaCoq.
Import MetaCoqNotations.

Goal True.
MProof.
  evar nat;; evar bool;; ret _.
  ret _.
  ret _.
  ret I.
  ret 0.
  ret true.
Qed.

Definition ThrowANat (n : nat) : Exception. exact exception. Qed.
Definition test n :=
  mmatch n with
  | [? n'] S n' => raise (ThrowANat n')
  | _ => ret 0
  end.

Goal True.
MProof.
  ttry (test 1;; ret I) (fun _=>ret I).
Qed.

Goal {n:nat| n = n}.
MProof.
  mtry test 1;; raise exception
  with [? n'] ThrowANat n' => ret (exist _ n' _) end.
Abort.


Goal {n:nat| n = n}.
MProof.
  mmatch 2 + 4 with
  | [? n] n + n => ret (exist _ (n + n) eq_refl)
  | [? n] n + n => ret (exist _ (n + n) eq_refl)
  | [? n] n + n => ret (exist _ (n + n) eq_refl)
  | [? n] n + n => ret (exist _ (n + n) eq_refl)
  | [? n m] n + m => ret (exist (fun n=>n=n) (n + m) eq_refl)
  end.
Qed.
