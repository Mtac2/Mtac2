From Mtac2 Require Import Datatypes intf.Sorts.
Import Sorts.S.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

Inductive Hyp : Type :=
| ahyp : forall {A}, A -> moption A -> Hyp.

(** goal type *)
Inductive goal :=
  | Goal : forall (s:Sort){A:stype_of s}, selem_of A -> goal
  | AHyp : forall {A:Type}, (A -> goal) -> goal
  | HypLet : Type -> goal -> goal
  | HypRem : forall {A:Type}, A -> goal -> goal.