From Mtac2 Require Import Datatypes Logic intf.Sorts.
Import Sorts.S.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Polymorphic Inductive Cumulativity.

Inductive Hyp : Prop :=
| ahyp : forall {A}, A -> moption A -> Hyp.


Inductive goal_state : Set := | gs_open | gs_any.

Inductive goal@{U131 U132} : goal_state -> Prop :=
  | Metavar' : forall gs (s : Sort) (A : stype_of@{U131 U132} s), selem_of@{U131 U132} A -> goal gs
  | AHyp : forall {A : Type@{U132}}, (A -> goal gs_any) -> goal gs_any
  | HypLet : Type@{U132} -> goal gs_any -> goal gs_any
  | HypRem : forall {A : Type@{U132}}, A -> goal gs_any -> goal gs_any
  | HypReplace : forall {A B : Type@{U132}},  A -> meq@{U131} A B -> goal gs_any -> goal gs_any.

Notation "'Metavar'" := (Metavar' gs_open).
Notation "'AnyMetavar'" := (Metavar' gs_any).
