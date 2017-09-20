From Mtac2 Require Import Mtac2.

Goal unit.
  MProof.
  (c <- M.declare dok_Definition "bla" false 1; M.print_term c;; M.ret tt)%MC.
Qed.



Typeclasses eauto := debug.
Structure ST := mkS { s : nat }.

Require Mtac2.List.
Import Mtac2.List.ListNotations.

Compute ltac:(mrun (c1 <- M.declare dok_CanonicalStructure "bla" false (fun (x : nat) => (fun x => mkS x) x);
                    c2 <- M.declare dok_Definition "bli" true c1;
                    M.declare_implicits c2 [m: Some ia_Implicit];;
                    M.ret tt)%MC).
Print bla.
Print Coercions.
Print Canonical Projections.
Print bli.
Fail Compute (bli 1).
Compute (@bli 1).

Module DeclareTest.
  Fail Compute ltac:(mrun (M.declare_implicits (1+1) [m:])).
  Local Arguments Nat.add {_ _}.
  Fail Compute ltac:(mrun (M.declare_implicits (Nat.add) [m:])).
  Fail Compute ltac:(mrun (M.declare_implicits (Nat.add (n:=1)) [m:])).
  Compute ltac:(mrun (M.declare_implicits (@Nat.add) [m:])).
End DeclareTest.