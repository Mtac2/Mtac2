Module MonoList.

From Coq Require Import List.
Import ListNotations.

Class MBind (M : Type -> Type) :=
  mbind : forall {A B}, (A -> M B) -> M A -> M B.
#[global] Instance list_bind : MBind list := fun A B f =>
  fix go (l : list A) :=
    match l with nil => nil | cons x l => f x ++ go l end%list.

Set Printing Universes.

Polymorphic Record dyn := Dyn { type : Type; elem : type }.

Fail Definition fails : list dyn := [Dyn _ (@List.app)].

End MonoList.

Module PolyList.

Polymorphic Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A.
Arguments nil {A}.
Arguments cons {A} a l.
Infix "::" := cons (at level 60, right associativity) : list_scope.
Delimit Scope list_scope with list.
Bind Scope list_scope with list.

Local Open Scope list_scope.

Definition app (A : Type) : list A -> list A -> list A :=
  fix app l m :=
  match l with
   | nil => m
   | a :: l1 => a :: app l1 m
  end.
Arguments app {_}.
Infix "++" := app (right associativity, at level 60) : list_scope.

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : list_scope.

Class MBind (M : Type -> Type) :=
  mbind : forall {A B}, (A -> M B) -> M A -> M B.
#[global] Instance list_bind : MBind list := fun A B f =>
  fix go (l : list A) :=
    match l with nil => nil | cons x l => f x ++ go l end%list.

Set Printing Universes.

Polymorphic Record dyn := Dyn { type : Type; elem : type }.

Definition doesnotfail : list dyn := [Dyn _ (@List.app)].

End PolyList.