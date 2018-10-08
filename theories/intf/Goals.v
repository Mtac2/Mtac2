From Mtac2 Require Import Datatypes Logic intf.Sorts.
Import Sorts.S.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Polymorphic Inductive Cumulativity.

Inductive Hyp : Type :=
| ahyp : forall {A}, A -> moption A -> Hyp.

(** goal type *)
(* Inductive goal := *)
(*   | Goal : forall (s:Sort){A:stype_of s}, selem_of A -> goal *)
(*   | AHyp : forall {A:Type}, (A -> goal) -> goal *)
(*   | HypLet : Type -> goal -> goal *)
(*   | HypRem : forall {A:Type}, A -> goal -> goal *)
(*   | HypReplace : forall {A B:Type}, A -> A =m= B -> goal -> goal. *)


Inductive goal_state := | gs_base | gs_any.

Inductive goal@{U131 U132} : goal_state -> Type :=
  | Goal : forall (s : Sort) {A : stype_of@{U131 U132} s}, selem_of@{U132 U131 U132 U132} A -> goal gs_base
  | GoalOut : forall (s : Sort) {A : stype_of@{U131 U132} s}, selem_of@{U132 U131 U132 U132} A -> goal gs_any
  | AHyp : forall {A : Type@{U132}}, (A -> goal gs_any) -> goal gs_any
  | HypLet : Type@{U132} -> goal gs_any -> goal gs_any
  | HypRem : forall {A : Type@{U132}}, A -> goal gs_any -> goal gs_any
  | HypReplace : forall {A B : Type@{U132}},  A -> meq@{U131} A B -> goal gs_any -> goal gs_any.