From Mtac2 Require Import Logic List intf.Unification Sorts MTele.
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


Inductive branch {M : Type -> Prop} : forall {A : Type} {B : A -> Type} {y : A}, Prop :=
| branch_pattern {A B y}: pattern M A B y -> @branch M A B y
| branch_app_static {A B y}:
    forall {m} (uni : Unification) (C : MTele_ConstT A m),
      MTele_sort (MTele_ConstMap (si := SType) SProp (T:=A) (fun a => M (B a)) C) ->
      @branch M A B y
| branch_forallP {B y}:
    (forall (X : Type) (Y : X -> Prop), M (B (forall x : X, Y x))) ->
    @branch M Prop B y
| branch_forallT {B y}:
    (forall (X : Type) (Y : X -> Type), M (B (forall x : X, Y x))) ->
    @branch M Type B y.
Arguments branch _ _ _ _ : clear implicits.


(* | branch_app_dynamic {A} {B : forall A, A -> Type} {y}: *)
(*     (forall X (Y : X -> Type) (f : forall x, Y x) (x : X), M (B _ (f x))) -> *)
(*     @branch M _ B A y *)


Notation "[¿ s .. t ] ps" := (psort (fun s => .. (psort (fun t => ps)) ..))
  (at level 202, s binder, t binder, ps at next level, only parsing) : pattern_scope.
Notation "'[S?' s .. t ] ps" := (psort (fun s => .. (psort (fun t => ps)) ..))
  (at level 202, s binder, t binder, ps at next level) : pattern_scope.

Notation "[? x .. y ] ps" := (ptele (fun x => .. (ptele (fun y => ps)).. ))
  (at level 202, x binder, y binder, ps at next level) : pattern_scope.
Notation "p => b" := (pbase p%core (fun _ => b%core) UniMatch)
  (no associativity, at level 201) : pattern_scope.
Notation "p => [ H ] b" := (pbase p%core (fun H => b%core) UniMatch)
  (no associativity, at level 201, H at next level) : pattern_scope.
Notation "p => [ H .. G ] b" := (pbase p%core (fun H => .. (fun G => b%core) .. ) UniMatch)
  (no associativity, at level 201, H binder, G binder) : pattern_scope.
Notation "'_' => b " := (pany b%core)
  (at level 201, b at next level) : pattern_scope.

Notation "p '=n>' b" := (pbase p%core (fun _ => b%core) UniMatchNoRed)
  (no associativity, at level 201) : pattern_scope.
Notation "p '=n>' [ H ] b" := (pbase p%core (fun H => b%core) UniMatchNoRed)
  (no associativity, at level 201, H at next level) : pattern_scope.
Notation "p =n> [ H .. G ] b" := (pbase p%core (fun H => .. (fun G => b%core) .. ) UniMatchNoRed)
  (no associativity, at level 201, H binder, G binder) : pattern_scope.

Notation "p '=u>' b" := (pbase p%core (fun _ => b%core) UniCoq)
  (no associativity, at level 201) : pattern_scope.
Notation "p '=u>' [ H ] b" := (pbase p%core (fun H => b%core) UniCoq)
  (no associativity, at level 201, H at next level) : pattern_scope.
Notation "p =u> [ H .. G ] b" := (pbase p%core (fun H => .. (fun G => b%core) .. ) UniCoq)
  (no associativity, at level 201, H binder, G binder) : pattern_scope.

Notation "p '=c>' b" := (pbase p%core (fun _ => b%core) UniEvarconv)
  (no associativity, at level 201) : pattern_scope.
Notation "p '=c>' [ H ] b" := (pbase p%core (fun H => b%core) UniEvarconv)
  (no associativity, at level 201, H at next level) : pattern_scope.
Notation "p =c> [ H .. G ] b" := (pbase p%core (fun H => .. (fun G => b%core) .. ) UniEvarconv)
  (no associativity, at level 201, H binder, G binder) : pattern_scope.

Delimit Scope pattern_scope with pattern.

Notation "[¿ s .. t ] ps" := (branch_pattern (psort (fun s => .. (psort (fun t => ps%pattern)) ..)))
  (at level 202, s binder, t binder, ps at next level, only parsing) : branch_scope.
Notation "'[S?' s .. t ] ps" := (branch_pattern (psort (fun s => .. (psort (fun t => ps%pattern)) ..)))
  (at level 202, s binder, t binder, ps at next level) : branch_scope.

Notation "[? x .. y ] ps" := (branch_pattern (ptele (fun x => .. (ptele (fun y => ps%pattern)).. )))
  (at level 202, x binder, y binder, ps at next level) : branch_scope.
Notation "p => b" := (branch_pattern (pbase p%core (fun _ => b%core) UniMatch))
  (no associativity, at level 201) : branch_scope.
Notation "p => [ H ] b" := (branch_pattern (pbase p%core (fun H => b%core) UniMatch))
  (no associativity, at level 201, H at next level) : branch_scope.
Notation "p => [ H .. G ] b" := (branch_pattern (pbase p%core (fun H => .. (fun G => b%core) .. ) UniMatch))
  (no associativity, at level 201, H binder, G binder) : branch_scope.
Notation "'_' => b " := (branch_pattern (pany b%core))
  (at level 201, b at next level) : branch_scope.

Notation "p '=n>' b" := (branch_pattern (pbase p%core (fun _ => b%core) UniMatchNoRed))
  (no associativity, at level 201) : branch_scope.
Notation "p '=n>' [ H ] b" := (branch_pattern (pbase p%core (fun H => b%core) UniMatchNoRed))
  (no associativity, at level 201, H at next level) : branch_scope.
Notation "p =n> [ H .. G ] b" := (branch_pattern (pbase p%core (fun H => .. (fun G => b%core) .. ) UniMatchNoRed))
  (no associativity, at level 201, H binder, G binder) : branch_scope.

Notation "p '=u>' b" := (branch_pattern (pbase p%core (fun _ => b%core) UniCoq))
  (no associativity, at level 201) : branch_scope.
Notation "p '=u>' [ H ] b" := (branch_pattern (pbase p%core (fun H => b%core) UniCoq))
  (no associativity, at level 201, H at next level) : branch_scope.
Notation "p =u> [ H .. G ] b" := (branch_pattern (pbase p%core (fun H => .. (fun G => b%core) .. ) UniCoq))
  (no associativity, at level 201, H binder, G binder) : branch_scope.

Notation "p '=c>' b" := (branch_pattern (pbase p%core (fun _ => b%core) UniEvarconv))
  (no associativity, at level 201) : branch_scope.
Notation "p '=c>' [ H ] b" := (branch_pattern (pbase p%core (fun H => b%core) UniEvarconv))
  (no associativity, at level 201, H at next level) : branch_scope.
Notation "p =c> [ H .. G ] b" := (branch_pattern (pbase p%core (fun H => .. (fun G => b%core) .. ) UniEvarconv))
  (no associativity, at level 201, H binder, G binder) : branch_scope.

Delimit Scope branch_scope with branch.

Notation "'with' | p1 | .. | pn 'end'" :=
  ((@mcons (branch _ _ _ _) p1%branch (.. (@mcons (branch _ _ _ _) pn%branch [m:]) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.
Notation "'with' p1 | .. | pn 'end'" :=
  ((@mcons (branch _ _ _ _) p1%branch (.. (@mcons (branch _ _ _ _) pn%branch [m:]) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.

Delimit Scope with_pattern_scope with with_pattern.

(* Syntax for decomposition of applications with a known head symbol.

   All arrows are annotated with "n" to signal that no reduction of the overall
   term will happen. The delimiter symbol "$" is annotated with the reduction
   strategy used for the initial arguments *)

Notation "'[#' ] f '|' x .. z '=n>' b" :=
  (branch_app_static
     (m := mTele (fun x => .. (mTele (fun z => mBase)) ..))
     UniMatchNoRed
     f
     (fun x => .. (fun z => b) ..)
  ) (at level 91, x binder, z binder) : branch_scope.

Notation "'[#' ] f '|' '=n>' b" :=
  (branch_app_static (m := mBase) UniMatchNoRed f b) (at level 91) : branch_scope.

Notation "'[#' ] f '|' x .. z '=m>' b" :=
  (branch_app_static
     (m := mTele (fun x => .. (mTele (fun z => mBase)) ..))
     UniMatch
     f
     (fun x => .. (fun z => b) ..)
  ) (at level 91, x binder, z binder) : branch_scope.

Notation "'[#' ] f '|' '=m>' b" :=
  (branch_app_static (m := mBase) UniMatch f b) (at level 91) : branch_scope.

Notation "'[#' ] f '|' x .. z '=u>' b" :=
  (branch_app_static
     (m := mTele (fun x => .. (mTele (fun z => mBase)) ..))
     UniCoq
     f
     (fun x => .. (fun z => b) ..)
  ) (at level 91, x binder, z binder) : branch_scope.

Notation "'[#' ] f '|' '=u>' b" :=
  (branch_app_static (m := mBase) UniCoq f b) (at level 91) : branch_scope.

Notation "'[#' ] f '|' x .. z '=c>' b" :=
  (branch_app_static
     (m := mTele (fun x => .. (mTele (fun z => mBase)) ..))
     UniEvarconv
     f
     (fun x => .. (fun z => b) ..)
  ) (at level 91, x binder, z binder) : branch_scope.

Notation "'[#' ] f '|' '=c>' b" :=
  (branch_app_static (m := mBase) UniEvarconv f b) (at level 91) : branch_scope.


(* Syntax for decomposition of [forall x : X, P x].

   We define two variants, one for [Prop] and for [Type].
   The initial tokens are [[!Prop]] and [[!Type]] and the remaining
   syntax tries to mirror an actual [forall].
 *)
Notation "'[!Prop' ] 'forall' '_' : X , P =n> b" :=
  (branch_forallP (fun X P => b))
    (at level 91) : branch_scope.
Notation "'[!Type' ] 'forall' '_' : X , P =n> b" :=
  (branch_forallT (fun X P => b))
    (at level 91) : branch_scope.