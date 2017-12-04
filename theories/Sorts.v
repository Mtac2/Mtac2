Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(** Types that can hold either a [Prop] or a [Type] *)
Module Sorts.

Inductive Sort : Type := SProp | SType.

(** Creates a fresh type according to [s] *)
Definition stype_of (s : Sort) : Type :=
  match s with SType => Type | SProp => Prop end.
Arguments stype_of !_ : simpl nomatch.

(** When working with a sort [s], we cannot simply say "we have an
    element of [stype_of s]". For that, we make [selem_of T], where
    [T] is a [stype_of s]. *)
Definition selem_of {s : Sort} (x : stype_of s) : Type :=
  match s return stype_of s -> Type with
  | SType => fun x => x
  | SProp => fun x => x
  end x.
Arguments selem_of {!_} _ : simpl nomatch.

Fail Local Example CannotMakeAnElementOfaSort s (P : stype_of s) (x : P) := x.
Local Example WeCanWithElemOf s (P : stype_of s) (x : selem_of P) := x.

Definition ForAll
            {sort : Sort} {A : Type} :
  (A -> stype_of sort) -> stype_of sort :=
  match
    sort as sort'
    return ((A -> stype_of sort') -> stype_of sort')
  with
  | SProp => fun F => forall a : A, F a
  | SType => fun F => forall a : A, F a
  end.

Definition Impl {sort : Sort} A (B : stype_of sort) : stype_of sort :=
  ForAll (sort := sort) (fun _ : A => B).

Definition Fun {sort} {A : Type} :
  forall {F : A -> stype_of sort}, (forall a, selem_of (F a)) -> selem_of (ForAll F) :=
  match sort as sort' return
        forall {F : A -> stype_of sort'}, (forall a, selem_of (F a)) -> selem_of (ForAll F)
  with
  | SProp => fun _ f => f
  | SType => fun _ f => f
  end.

Definition App {sort} {A : Type} : forall {F : A -> _},  selem_of (ForAll (sort := sort) F) -> forall a, selem_of (F a) :=
  match sort as sort' return forall F, selem_of (ForAll (sort := sort') F) -> forall a, selem_of (F a) with
  | SProp => fun F f a => f a
  | SType => fun F f a => f a
  end.
End Sorts.

Import Sorts.

Coercion stype_of : Sort >-> Sortclass.
Coercion selem_of : stype_of >-> Sortclass.
