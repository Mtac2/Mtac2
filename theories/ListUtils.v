From MetaCoq Require Export Mtac2.
Import MtacNotations.
Require Import Lists.List.
Import ListNotations.

Definition mmap {A B : Type} (f : A -> M B) :=
  mfix1 rec (l : list A) : M (list B) :=
    match l with
    | [] =>
        ret []
    | (x :: xs) =>
        x <- f x;
        xs <- rec xs;
        ret (x :: xs)
    end.

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

Definition mfilter {A} (b : A -> M bool) : list A -> M (list A) :=
  fix f l :=
    match l with
    | [] => ret []
    | x :: xs => bx <- b x; r <- f xs;
                 if bx then ret (x::r) else ret r
    end.

Definition EmptyList : Exception. exact exception. Qed.
Definition hd_exception {A} (l : list A) : M A :=
  match l with
  | (a :: _) => ret a
  | _ => raise EmptyList
  end.

Fixpoint last_exception {A} (l : list A) : M A :=
  match l with
  | [a] => ret a
  | (_ :: s) => last_exception s
  | _ => raise EmptyList
  end.

Definition mfold_right {A B} (f : B -> A -> M A) (x : A) : list B -> M A :=
  fix loop l :=
    match l with
    | [] => ret x
    | x :: xs => r <- loop xs;
                 f x r
    end.

Definition mfold_left {A B} (f : A -> B -> M A) : list B -> A -> M A :=
  fix loop l (a : A) :=
    match l with
    | [] => ret a
    | b :: bs => r <- f a b;
                 loop bs r
    end.

Definition mindex_of {A} (f : A -> M bool) (l : list A) : M (option nat) :=
  ir <- mfold_left (fun (ir : (nat * option nat)) x =>
    let (i, r) := ir in
    match r with
    | Some _ => ret ir
    | _ => b <- f x;
           if b then ret (i, Some i) else ret (S i, None)
    end
  ) l (0, None);
  let (_, r) := ir in
  ret r.

Definition NotThatManyElements : Exception. exact exception. Qed.

Fixpoint nth_exception {A} n (l : list A) : M A :=
  match n, l with
  | 0, (a :: _) => ret a
  | S n, (_ :: s) => nth_exception n s
  | _, _ => raise NotThatManyElements
  end.

Definition miterate {A} (f : A -> M unit) : list A -> M unit :=
  fix loop l :=
    match l with
    | [] => ret tt
    | b :: bs => f b;; loop bs
    end.
