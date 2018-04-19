From Mtac2 Require Import Logic List intf.Unification Sorts intf.Exceptions.
Import Sorts.
Import ListNotations.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

(** Pattern matching without pain *)
(* The M will be instantiated with the M monad or the gtactic monad. In principle,
we could make it part of the B, but then higher order unification will fail. *)
Inductive pattern (M : Type -> Prop) (A : Type) (B : A -> Type) (y : A) : Prop :=
  | pany : M (B y) -> pattern M A B y
  | pbase : forall x : A, (y =m= x ->M (B x)) -> Unification -> pattern M A B y
  | ptele : forall {C:Type}, (forall x : C, pattern M A B y) -> pattern M A B y
  | psort : (Sort -> pattern M A B y) -> pattern M A B y.


Arguments pany {M A B y} _.
Arguments pbase {M A B y} _ _ _.
Arguments ptele {M A B y C} _.
Arguments psort {M A B y} _.

Delimit Scope pattern_scope with pattern.
Delimit Scope with_pattern_scope with with_pattern.


Set Primitive Projections.

Definition BranchExec (M : Type -> Prop) (A : Type) (B : A -> Type) (a : A) :=
  Exception -> forall a', a' =m= a -> M (B a').

Record Branch (M : Type -> Prop) (A : Type) (B : A -> Type) (a : A) :=
 BRANCH { branch_exec : BranchExec M A B a }.
Arguments branch_exec [_ _ _ _] _ _ _.
Arguments BRANCH [_ _ _ _] _.

Record BranchType M A B a  :=
  BRANCH_TYPE {
      branch_type : Type;
      branch_of : branch_type -> Branch M A B a
    }.
Arguments BRANCH_TYPE [_ _ _ _].
Arguments branch_type [_ _ _ _].
Arguments branch_of [_ _ _ _ _].

Unset Primitive Projections.




Notation "'with' | p1 | .. | pn 'end'" :=
  ((@mcons (Branch _ _ _ _) (p1%pattern) (.. (@mcons (Branch _ _ _ _) (pn%pattern) [m:]) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.
Notation "'with' p1 | .. | pn 'end'" :=
  ((@mcons (Branch _ _ _ _) (p1%pattern) (.. (@mcons (Branch _ _ _ _) (pn%pattern) [m:]) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.
