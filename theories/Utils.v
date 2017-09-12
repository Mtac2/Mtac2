From MetaCoq Require Import Datatypes List.
Import MetaCoq.List.ListNotations.

Definition dec_bool {P} (x : {P}+{~P}) : bool :=
  match x with
  | left _ => true
  | _ => false
  end.

Definition option_to_bool {A} (ox : option A) : bool :=
  match ox with Some _ => true | _ => false end.

Definition is_empty {A} (l: list A) : bool :=
  match l with [m:] => true | _ => false end.

Fixpoint but_last {A} (l : list A) : list A :=
  match l with
  | [m:] => [m:]
  | [m:a] => [m:]
  | a :: ls => a :: but_last ls
  end.

Fixpoint nsplit {A} (n : nat) (l : list A) : list A * list A :=
  match n, l with
  | 0, l => ([m:], l)
  | S n', x :: l' => let (l1, l2) := nsplit n' l' in (x :: l1, l2)
  | _, _ => ([m:], [m:])
  end.
