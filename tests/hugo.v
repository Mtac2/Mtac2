Require Import MetaCoq.MetaCoq.

Inductive my_enum_type :=
  one | two | three.

Require Import Vector.

Import Fin.

Require Import Omega.

Lemma lt_0_S n : 0 < S n. Proof. omega. Qed.

Fixpoint prove_leq n m : M (n < m) :=
  match n, m with
  | 0, S _ => ret (lt_0_S _)
  | S n', S m' =>
    H <- prove_leq n' m';
    ret (Lt.lt_n_S _ _ H)
  | _, _ => failwith "n not < m"
  end.

Definition to_fin_MP : selector := fun l=>
  let n := List.length l in
  mmapi (fun i g =>
    H <- prove_leq i n;
    let v := rcbv (of_nat_lt H) in
    exact v g) l;;
  ret [].

Goal my_enum_type -> Fin.t 3.
MProof.
  intro H.
  destruct H &> to_fin_MP.
Qed.

Goal my_enum_type.
MProof.
  pose (H := FS (FS F1) : Fin.t 3).
  let p := proj1_sig (to_nat H) in
  constructor (S p).
Qed.
