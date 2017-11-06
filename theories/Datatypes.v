(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Set Implicit Arguments.

Require Import Notations.
(* Require Import Logic. *)
(* Declare ML Module "nat_syntax_plugin". *)

(* (********************************************************************) *)
(* (** * Container datatypes *) *)

(* (* Set Universe Polymorphism. *) *)

(* (** [option A] is the extension of [A] with an extra element [None] *) *)

(* Inductive option (A:Type) : Type := *)
(*   | Some : A -> option A *)
(*   | None : option A. *)

(* Arguments Some {A} a. *)
(* Arguments None {A}. *)

(* Definition option_map (A B:Type) (f:A->B) (o : option A) : option B := *)
(*   match o with *)
(*     | Some a => @Some B (f a) *)
(*     | None => @None B *)
(*   end. *)

(* (** [sum A B], written [A + B], is the disjoint sum of [A] and [B] *) *)

(* Inductive sum (A B:Type) : Type := *)
(*   | inl : A -> sum A B *)
(*   | inr : B -> sum A B. *)

(* Notation "x + y" := (sum x y) : type_scope. *)

(* Arguments inl {A B} _ , [A] B _. *)
(* Arguments inr {A B} _ , A [B] _. *)

(* (** [prod A B], written [A * B], is the product of [A] and [B]; *)
(*     the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *) *)

(* Inductive prod (A B:Type) : Type := *)
(*   pair : A -> B -> prod A B. *)

(* Add Printing Let prod. *)

(* Notation "x * y" := (prod x y) : type_scope. *)
(* Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope. *)

(* Arguments pair {A B} _ _. *)

(* Section projections. *)
(*   Context {A : Type} {B : Type}. *)

(*   Definition fst (p:A * B) := match p with *)
(* 				| (x, y) => x *)
(*                               end. *)
(*   Definition snd (p:A * B) := match p with *)
(* 				| (x, y) => y *)
(*                               end. *)
(* End projections. *)

(* Hint Resolve pair inl inr: core. *)

(* Lemma surjective_pairing : *)
(*   forall (A B:Type) (p:A * B), p = pair (fst p) (snd p). *)
(* Proof. *)
(*   destruct p; reflexivity. *)
(* Qed. *)

(* Lemma injective_projections : *)
(*   forall (A B:Type) (p1 p2:A * B), *)
(*     fst p1 = fst p2 -> snd p1 = snd p2 -> p1 = p2. *)
(* Proof. *)
(*   destruct p1; destruct p2; simpl; intros Hfst Hsnd. *)
(*   rewrite Hfst; rewrite Hsnd; reflexivity. *)
(* Qed. *)

(* Definition prod_uncurry (A B C:Type) (f:prod A B -> C) *)
(*   (x:A) (y:B) : C := f (pair x y). *)

(* Definition prod_curry (A B C:Type) (f:A -> B -> C) *)
(*   (p:prod A B) : C := match p with *)
(*                        | pair x y => f x y *)
(*                        end. *)

(** Polymorphic lists and some operations *)

Inductive mlist (A : Type) : Type :=
 | mnil : mlist A
 | mcons : A -> mlist A -> mlist A.

Arguments mnil {A}.
Arguments mcons {A} a l.
Infix ":m:" := mcons (at level 60, right associativity) : mlist_scope.
Delimit Scope mlist_scope with mlist.
Bind Scope mlist_scope with mlist.

Local Open Scope mlist_scope.

Definition mlength (A : Type) : mlist A -> nat :=
  fix length l :=
  match l with
   | mnil => O
   | _ :m: l' => S (length l')
  end.

(** Concatenation of two lists *)

Definition mapp (A : Type) : mlist A -> mlist A -> mlist A :=
  fix mapp l m :=
  match l with
   | mnil => m
   | a :m: l1 => a :m: mapp l1 m
  end.


Infix "+m+" := mapp (right associativity, at level 60) : mlist_scope.
