From Mtac2 Require Import Mtac2.
Import M.notations.
Definition test := c <- M.declare dok_Definition "bla" false 1; M.print_term c.
Goal unit.
  MProof.
  c <- M.declare dok_Definition "ble" false 1; M.print_term c.
Qed.

Goal unit.
MProof. test. Qed.

Typeclasses eauto := debug.
Structure ST := mkS { s : nat }.

Require Mtac2.lib.List.
Import Mtac2.lib.List.ListNotations.
Definition cs := c1 <- M.declare dok_CanonicalStructure "bla" false (fun (x : nat) => (fun x => mkS x) x);
                    c2 <- M.declare dok_Definition "bli" true c1;
                    M.declare_implicits c2 [m: ia_Implicit];;
                    M.ret tt.

Compute ltac:(mrun cs).
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
  Compute ltac:(mrun (M.declare_implicits (@Nat.add) [m: ia_Implicit | ia_Implicit])).
  Definition should_work0 := Nat.add (n:=3) (m :=2).
  Compute ltac:(mrun (M.declare_implicits (@Nat.add) [m: ia_Implicit | ia_Explicit])).
  Definition should_work2 := Nat.add (n:=3) 2.
  Compute ltac:(mrun (M.declare_implicits (@Nat.add) [m: ia_Explicit | ia_Implicit])).
  Definition should_work1 := Nat.add (m :=3) 2.
  Compute ltac:(mrun (M.declare_implicits (@Nat.add) [m: ia_Explicit | ia_Explicit])).
  Definition should_work := Nat.add 3 2.
End DeclareTest.
Require Import Strings.String.
Import M.notations.

Fixpoint defineN (n : nat) : M unit :=
  match n with
  | 0 => M.ret tt
  | S n =>
    s <- M.pretty_print n;
    M.declare dok_Definition ("NAT"++s)%string false n;;
    defineN n
  end.
Fail Print N0.
Compute ltac:(mrun (defineN 4)).

Print NAT0.
Print NAT1.
Print NAT2.
Print NAT3.
Fail Print NAT4.

Set Printing All. (* nasty *)
Fail Compute ltac:(mrun (defineN 4)).
Search "NAT". (* Now there are no definitions like "NATS (S O)" *)
Fail Compute ltac:(mrun (M.get_reference "NATS O")).

Definition ev := c <- M.declare dok_Definition "_" true (S O); M.print_term c.
Fail Compute (M.eval ev). (* FIX why? *)

Unset Printing All.

(* ouch, there should be a catchable error. but what about previously declared objects? *)
Definition alrdecl := mtry defineN 5 with [?s] AlreadyDeclared s => M.print s;; M.ret tt end.
Compute ltac:(mrun alrdecl).

Print NAT4. (* definitions before the failing one are declared. *)

(* we should check that the terms are closed w.r.t. section variables *)
(* JANNO: for now we just raise an catchable exception. *)
Compute fun x y =>
          ltac:(mrun (
                    mtry
                      M.declare dok_Definition "lenS" true (Le.le_n_S x y);; M.ret tt
                      with | UnboundVar => M.ret tt end
               )).

Compute M.eval (c <- M.declare dok_Definition "blu" true (Le.le_n_S); M.print_term c).

Print blu.


Definition backtracking_test :=
  mtry
    M.declare dok_Definition "newone" false tt;;
    M.declare dok_Definition "blu" false tt;;
    M.ret tt
  with [?s] AlreadyDeclared s => M.ret tt end.

Compute ltac:(mrun backtracking_test).

Print newone. (* is this expected? or should the "state" of definitions be also backtracked? *)
Print blu.
