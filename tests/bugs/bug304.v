Require Import Mtac2.Mtac2.
Import M.notations.
Import M.

(** we construct an equality of 4 =m= 2 from an equality of 2 =m= 2 *)
Polymorphic Definition test : M unit :=
  mtry
    (\nu n := 2,
      eq <- unify_or_fail UniCoq n 2;
      abs_let (P:=fun n=> n =m= 2) n 4 (eq : n =m= 2) : M (4 =m= 2));;
    print "This shouldn't run";;
    ret tt
  with AbsLetNotConvertible =>
    print "All good";;
    ret tt
  end.

Mtac Do test.
