Require Import Mtac2.Mtac2.

Inductive my_enum_type :=
  one | two | three.

Require Import Vector.

Import Fin.

Require Import Lia.

Lemma lt_0_S n : 0 < S n. Proof. lia. Qed.

(* NOTE: unidirectional version of Nat.succ_lt_mono for compatibility. *)
Lemma succ_lt_mono_lr (n m : nat) : n < m -> S n < S m.
Proof. now intros H; apply ->PeanoNat.Nat.succ_lt_mono. Qed.

Fixpoint prove_leq n m : M (n < m) :=
  match n, m with
  | 0, S _ => M.ret (lt_0_S _)
  | S n', S m' =>
    H <- prove_leq n' m';
    M.ret (succ_lt_mono_lr _ _ H)
  | _, _ => M.failwith "n not < m"
  end.

Definition to_fin_MP : T.selector unit := (fun l=>
  let n := mlength l in
  M.mapi (fun i '(m: _, g) =>
    H <- prove_leq i n;
    let v := rcbv (of_nat_lt H) in
    T.open_and_apply (T.exact v) g) l;;
  M.ret [m:])%MC.

Goal my_enum_type -> Fin.t 3.
MProof.
  intro H.
  T.destruct H &> to_fin_MP : gtactic unit. (* HACK: why do we need to specify the return type? *)
Qed.

Goal my_enum_type.
MProof.
  pose (H := FS (FS F1) : Fin.t 3).
  let p := proj1_sig (to_nat H) in
  T.nconstructor (S p).
Qed.
