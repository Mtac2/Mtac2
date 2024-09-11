Declare ML Module "coq-mtac2.plugin".

(* Declare ML Module must work without the Requires to be compatible
   with async proofs. Running it before them serves as a test
   (although it doesn't test that it still works without the prelude
   Requires). *)
From Mtac2 Require Import Logic Datatypes Logic List Utils Sorts MTele.
Import Sorts.
From Mtac2 Require Export Pattern.
From Mtac2.intf Require Export Dyn Reduction Unification DeclarationDefs M Lift .

Require Import Strings.String.
Require Import NArith.BinNat.
Require Import NArith.BinNatDef.
Import Mtac2.lib.List.ListNotations.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Module M.
  Export M.M.
(** Defines [eval f] to execute after elaboration the Mtactic [f].
    It allows e.g. [rewrite (eval f)]. *)
  Class runner A  (f : t A) := { eval : A }.
  Arguments runner {A} _.
  Arguments Build_runner {A} _ _.
  Arguments eval {A} _ {_}.
End M.

#[global] Hint Extern 20 (M.runner ?f) =>
(mrun (M.bind f (fun eres=> M.ret (M.Build_runner f eres))))  : typeclass_instances.


Import M.notations.

Notation "t 'mwith' ( k := u )" :=
  (ltac:(mrun (r <- M.mwith t k u; dcase r with _ as x in M.ret x)%MC))
    (at level 0).

(** creation of exceptions *)
Definition new_exception name := M.declare dok_Definition name true exception;; M.ret tt.
Definition binder_exception (f: unit->unit) := M.get_binder_name f >>= new_exception.
Notation "'New' 'Exception' n" := (binder_exception (fun n=>n)) (at level 0, n at next level).

Definition Check {A} (x:A) := M.print_term A.

Definition Set_Debug_Exceptions := M.set_debug_exceptions true.
Definition Unset_Debug_Exceptions := M.set_debug_exceptions false.
Definition Set_Trace := M.set_trace true.
Definition Unset_Trace := M.set_trace false.
