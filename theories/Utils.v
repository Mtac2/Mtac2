Require Import Lists.List.

Definition dec_bool {P} (x : {P}+{~P}) : bool :=
  match x with
  | left _ => true
  | _ => false
  end.

Definition option_to_bool {A} (ox : option A) : bool :=
  match ox with Some _ => true | _ => false end.