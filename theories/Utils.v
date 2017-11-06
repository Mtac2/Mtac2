From Mtac2 Require Import Datatypes List.
Import Mtac2.List.ListNotations.

Definition dec_bool {P} (x : {P}+{~P}) : bool :=
  match x with
  | left _ => true
  | _ => false
  end.

Definition option_to_bool {A} (ox : moption A) : bool :=
  match ox with mSome _ => true | _ => false end.

Definition is_empty {A} (l: mlist A) : bool :=
  match l with [m:] => true | _ => false end.

Fixpoint but_last {A} (l : mlist A) : mlist A :=
  match l with
  | [m:] => [m:]
  | [m:a] => [m:]
  | a :m: ls => a :m: but_last ls
  end.

Fixpoint nsplit {A} (n : nat) (l : mlist A) : mlist A * mlist A :=
  match n, l with
  | 0, l => ([m:], l)
  | S n', x :m: l' => let (l1, l2) := nsplit n' l' in (x :m: l1, l2)
  | _, _ => ([m:], [m:])
  end.
