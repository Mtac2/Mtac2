From Mtac2 Require Import Datatypes Mtac2.

Require Import Lists.List.
Import ListNotations.

(** assert x y e asserts that y is syntactically equal to x. Since we
need to make sure the convertibility check is not triggered, we assume
the terms x and/or y contains an evar e that is instantiated with
tt. *)
Definition assert_eq {A} (x y: A) : M unit :=
  o1 <- M.unify x y UniMatchNoRed;
  match o1 with
    | mSome _ => M.ret tt
    | _ => M.raise (NotUnifiable x y)
  end.

(* Lets in matches used to break let-reduce. *)
Mtac Do (
       match (let x := 1 in [x]) with
       | nil => M.raise exception
       | cons _ _ =>
         let n := reduce (RedStrong RedAll) (1 + 1) in
         assert_eq 2 n
       end
     ).
