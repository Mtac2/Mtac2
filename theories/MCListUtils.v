Require Import MetaCoq.MetaCoq.
Import MetaCoqNotations.

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

Definition mfilter {A} (b : A -> M bool) : list A -> M (list A) :=
  fix f l :=
    match l with
    | [] => ret []
    | x :: xs => bx <- b x; r <- f xs;
                 if bx then ret (x::r) else ret r
    end.
