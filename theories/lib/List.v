(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export Mtac2.lib.Datatypes.
Set Implicit Arguments.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Open Scope mlist_scope.

Module ListNotations.
Notation "[m: ]" := mnil (format "[m: ]") : mlist_scope.
Notation "[m: x ]" := (mcons x mnil) : mlist_scope.
Notation "[m: x | y | .. | z ]" :=
  (mcons x (mcons y .. (mcons z mnil) ..))
    (format "'[hv  ' [m:  x '//' |  y  '//' |  .. '//' |  z ']' ]") : mlist_scope.
End ListNotations.

Import ListNotations.

Definition mhd {A} (default:A) (l:mlist A) :=
  match l with
  | [m:] => default
  | x :m: _ => x
  end.

Definition mhd_error {A} (l:mlist A) : moption A :=
  match l with
  | [m:] => mNone
  | x :m: _ => mSome x
  end.

Definition mtl {A} (l:mlist A) :=
  match l with
  | [m:] => mnil
  | a :m: m => m
  end.

Fixpoint mnth {A} (n:nat) (l:mlist A) (default:A) {struct l} : A :=
  match n, l with
  | O, x :m: l' => x
  | O, other => default
  | S m, [m:] => default
  | S m, x :m: t => mnth m t default
  end.

Fixpoint mnth_ok {A} (n:nat) (l:mlist A) (default:A) {struct l} : bool :=
  match n, l with
  | O, x :m: l' => true
  | O, other => false
  | S m, [m:] => false
  | S m, x :m: t => mnth_ok m t default
  end.

Fixpoint mnth_error {A} (l:mlist A) (n:nat) {struct n} : moption A :=
  match n, l with
  | O, x :m: _ => mSome x
  | S n, _ :m: l => mnth_error l n
  | _, _ => mNone
  end.

Definition mnth_default {A}(default:A) (l:mlist A) (n:nat) : A :=
  match mnth_error l n with
  | mSome x => x
  | mNone => default
  end.

Fixpoint mlast {A} (l:mlist A) (d:A) : A :=
  match l with
  | [m:] => d
  | [m:a] => a
  | a :m: l => mlast l d
  end.

Fixpoint mremovemlast {A} (l:mlist A) : mlist A :=
  match l with
  | [m:] =>  [m:]
  | [m:a] => [m:]
  | a :m: l => a :m: mremovemlast l
  end.

Fixpoint mrev {A} (l:mlist A) : mlist A :=
  match l with
  | [m:] => [m:]
  | x :m: l' => mrev l' +m+ [m:x]
  end.

Fixpoint mrev_append {A} (l l': mlist A) : mlist A :=
  match l with
  | [m:] => l'
  | a:m:l => mrev_append l (a:m:l')
  end.

Definition mrev' {A} l : mlist A := mrev_append l [m:].

Fixpoint mconcat {A} (l : mlist (mlist A)) : mlist A :=
  match l with
  | mnil => mnil
  | mcons x l => x +m+ mconcat l
  end.

Definition mmap {A B} (f : A -> B) :=
  fix mmap (l:mlist A) : mlist B :=
  match l with
    | [m:] => [m:]
    | a :m: t => (f a) :m: (mmap t)
  end.

Definition mflat_mmap {A B} (f:A -> mlist B) :=
  fix mflat_mmap (l:mlist A) : mlist B :=
  match l with
    | mnil => mnil
    | mcons x t => (f x)+m+(mflat_mmap t)
  end.

Section Fold_Left_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : A -> B -> A.

  Fixpoint mfold_left (l:mlist B) (a0:A) : A :=
    match l with
    | mnil => a0
    | mcons b t => mfold_left t (f a0 b)
    end.
End Fold_Left_Recursor.

Section Fold_Right_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : B -> A -> A.
  Variable a0 : A.

  Fixpoint mfold_right (l:mlist B) : A :=
    match l with
    | mnil => a0
    | mcons b t => f b (mfold_right t)
    end.
End Fold_Right_Recursor.

Section Bool.
  Variable A : Type.
  Variable f : A -> bool.

  Fixpoint mexistsb (l:mlist A) : bool :=
    match l with
    | mnil => false
    | a:m:l => f a || mexistsb l
    end.

  Fixpoint mforallb (l:mlist A) : bool :=
    match l with
    | mnil => true
    | a:m:l => f a && mforallb l
    end.

  Fixpoint mfilter (l:mlist A) : mlist A :=
    match l with
    | mnil => mnil
    | x :m: l => if f x then x:m:(mfilter l) else mfilter l
    end.

  Fixpoint mfind (l:mlist A) : moption A :=
    match l with
    | mnil => mNone
    | x :m: mtl => if f x then mSome x else mfind mtl
    end.

  Fixpoint mpartition (l:mlist A) : mlist A * mlist A :=
    match l with
    | mnil => (mnil, mnil)
    | x :m: mtl => let (g,d) := mpartition mtl in
      if f x then (x:m:g,d) else (g,x:m:d)
      end.
End Bool.

Fixpoint msplit {A B} (l:mlist (A*B)) : mlist A * mlist B :=
  match l with
  | [m:] => ([m:], [m:])
  | (x,y) :m: mtl => let (left,right) := msplit mtl in (x:m:left, y:m:right)
  end.

Fixpoint mcombine {A B} (l : mlist A) (l' : mlist B) : mlist (A*B) :=
  match l,l' with
  | x:m:mtl, y:m:mtl' => (x,y):m:(mcombine mtl mtl')
  | _, _ => mnil
  end.

Fixpoint mlist_prod {A B} (l:mlist A) (l':mlist B) : mlist (A * B) :=
  match l with
  | mnil => mnil
  | mcons x t => (mmap (fun y:B => (x, y)) l')+m+(mlist_prod t l')
  end.

Fixpoint mfirstn {A} (n:nat)(l:mlist A) : mlist A :=
  match n with
  | 0 => mnil
  | S n => match l with
	  | mnil => mnil
	  | a:m:l => a:m:(mfirstn n l)
    end
  end.

Fixpoint mskipn {A} (n:nat)(l:mlist A) : mlist A :=
  match n with
  | 0 => l
  | S n => match l with
	  | mnil => mnil
	  | a:m:l => mskipn n l
    end
  end.

Fixpoint mseq (start len:nat) : mlist nat :=
  match len with
  | 0 => mnil
  | S len => start :m: mseq (S start) len
  end.

Fixpoint mrepeat {A} (x : A) (n: nat ) :=
  match n with
  | O => [m:]
  | S k => x:m:(mrepeat x k)
  end.
