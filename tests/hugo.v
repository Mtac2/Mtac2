Require Import MetaCoq.MetaCoq.

Inductive my_enum_type :=
  one | two | three.

Require Import Vector.

Import Fin.

Fixpoint to_fin (m : my_enum_type) : t 3 :=
  match m with
  | one => F1
  | two => FS F1
  | three => FS (FS F1)
  end.

Program Fixpoint to_fin' (m : my_enum_type) : t 3 :=
  match m with
  | one => of_nat_lt (p:=0) _
  | two => of_nat_lt (p:=1) _
  | three => of_nat_lt (p:=2) _
  end.
Eval compute in to_fin'.

Fixpoint mmapi' n {A B} (f : nat -> A -> M B) (l: list A) : M (list B) :=
  match l with
  | [] => ret []
  | x :: xs =>
    el <- f n x;
    xs' <- mmapi' (S n) f xs;
    ret (el :: xs')
  end.

Definition mmapi := @mmapi' 0.
Arguments mmapi {_ _} _ _.

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
