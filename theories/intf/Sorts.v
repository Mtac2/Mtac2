Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(** Types that can hold either a [Prop] or a [Type] *)
Set Universe Polymorphism.
Unset Universe Minimization ToSet.


Inductive Block_DONT_COMMIT := SType | SProp.


Reserved Notation "Typeₛ".
Reserved Notation "Propₛ".
Module S.

Monomorphic Inductive Sort : Type := Prop_sort | Type_sort.

Notation "Typeₛ" := Type_sort.
Notation "Propₛ" := Prop_sort.

(** Creates a fresh type according to [s] *)
Definition stype_of (s : Sort) : Type :=
  match s with Typeₛ => Type | Propₛ => Prop end.
Arguments stype_of !_ : simpl nomatch.

(** When working with a sort [s], we cannot simply say "we have an
    element of [stype_of s]". For that, we make [selem_of T], where
    [T] is a [stype_of s]. *)
Definition selem_of@{i j+} {s : Sort} : stype_of@{i j} s -> Type@{j} :=
  match s return stype_of s -> Type@{j} with
  | Typeₛ => fun x => x
  | Propₛ => fun x => x
  end.
Arguments selem_of {!_} _ : simpl nomatch.

Fail Local Example CannotMakeAnElementOfaSort s (P : stype_of s) (x : P) := x.
Local Example WeCanWithElemOf s (P : stype_of s) (x : selem_of P) := x.

Definition selem_lift {s : Sort} : @selem_of Typeₛ (stype_of s) -> Type :=
  match s as s' return @selem_of Typeₛ (stype_of s') -> Type with
  | Typeₛ => fun x => x
  | Propₛ => fun y => y
  end.


Definition ForAll
            {sort : Sort} {A : Type} :
  (A -> stype_of sort) -> stype_of sort :=
  match
    sort as sort'
    return ((A -> stype_of sort') -> stype_of sort')
  with
  | Propₛ => fun F => forall a : A, F a
  | Typeₛ => fun F => forall a : A, F a
  end.

Definition Impl {sort : Sort} A (B : stype_of sort) : stype_of sort :=
  ForAll (sort := sort) (fun _ : A => B).

Definition Fun {sort} {A : Type} :
  forall {F : A -> stype_of sort}, (forall a, selem_of (F a)) -> selem_of (ForAll F) :=
  match sort as sort' return
        forall {F : A -> stype_of sort'}, (forall a, selem_of (F a)) -> selem_of (ForAll F)
  with
  | Propₛ => fun _ f => f
  | Typeₛ => fun _ f => f
  end.

Definition App {sort} {A : Type} : forall {F : A -> _},  selem_of (ForAll (sort := sort) F) -> forall a, selem_of (F a) :=
  match sort as sort' return forall F, selem_of (ForAll (sort := sort') F) -> forall a, selem_of (F a) with
  | Propₛ => fun F f a => f a
  | Typeₛ => fun F f a => f a
  end.

Definition Impl_lift {sort} {A : Type} : forall {B : stype_of sort}, (A -> selem_of B) -> selem_of (Impl A B) :=
  match sort with
  | Propₛ => fun B f => f
  | Typeₛ => fun B f => f
  end.

Definition lift_Impl {sort} {A : Type} : forall {B : stype_of sort}, selem_of (Impl A B) -> (A -> selem_of B) :=
  match sort with
  | Propₛ => fun B f => f
  | Typeₛ => fun B f => f
  end.


End S.

Import S.

Delimit Scope Sort_scope with sort.
Notation "Typeₛ" := Type_sort.
Notation "Propₛ" := Prop_sort.
Notation "forallₛ  x .. y ,  T" :=
  (ForAll (fun x => .. (fun y => T) ..))
    (at level 200, x binder, y binder) : Sort_scope.
Notation "∀ₛ  x .. y ,  T" :=
  (ForAll (fun x => .. (fun y => T) ..))
 (at level 200, x binder, y binder).
Notation "S ->ₛ T" :=
  (∀ₛ _ : S, T)%sort
    (at level 200) : Sort_scope.
Notation "funₛ  x .. y =>  t" :=
  (Fun (fun x => .. (fun y => t) ..))
    (at level 200, x binder, y binder) : Sort_scope.
Notation "λₛ  x .. y ,  t" :=
  (Fun (fun x => .. (fun y => t) ..))
    (at level 200, x binder, y binder) : Sort_scope.

Coercion stype_of : Sort >-> Sortclass.
Coercion selem_of : stype_of >-> Sortclass.
