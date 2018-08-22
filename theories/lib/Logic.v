(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Set Implicit Arguments.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Reserved Notation "x =m= y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x =m= y" (at level 70, no associativity).


(** * First-order quantifiers *)

(** [ex P], or simply [exists x, P x], or also [exists x:A, P x],
    expresses the existence of an [x] of some type [A] in [Set] which
    satisfies the predicate [P].  This is existential quantification.

    [ex2 P Q], or simply [exists2 x, P x & Q x], or also
    [exists2 x:A, P x & Q x], expresses the existence of an [x] of
    type [A] which satisfies both predicates [P] and [Q].

    Universal quantification is primitively written [forall x:A, Q]. By
    symmetry with existential quantification, the construction [all P]
    is provided too.
*)

Inductive mex (A:Type) (P:A -> Prop) : Prop :=
  mex_intro : forall x:A, P x -> mex (A:=A) P.

(** * Equality *)

(** [eq x y], or simply [x=y] expresses the equality of [x] and
    [y]. Both [x] and [y] must belong to the same type [A].
    The definition is inductive and states the reflexivity of the equality.
    The others properties (symmetry, transitivity, replacement of
    equals by equals) are proved below. The type of [x] and [y] can be
    made explicit using the notation [x = y :> A]. This is Leibniz equality
    as it expresses that [x] and [y] are equal iff every property on
    [A] which is true of [x] is also true of [y] *)

Inductive meq (A:Type) (x:A) : A -> Prop :=
     meq_refl : x =m= x :>A
where "x =m= y :> A" := (@meq A x y) : type_scope.

Notation "x =m= y" := (x =m= y :>_) : type_scope.

Arguments meq {A} x _.
Arguments meq_refl {A x} , [A] x.

Arguments meq_ind [A] x P _ y _.
Arguments meq_rec [A] x P _ y _.
Arguments meq_rect [A] x P _ y _.


(* Section Logic_lemmas. *)

Section equality.
  Variables A B : Type.
  Variable f : A -> B.
  Variables x y z : A.

  Theorem meq_sym : x =m= y -> y =m= x.
  Proof.
    destruct 1; reflexivity.
  Defined.

  Theorem meq_trans : x =m= y -> y =m= z -> x =m= z.
  Proof.
    destruct 2; trivial.
  Defined.

  Theorem mf_equal : x =m= y -> f x =m= f y.
  Proof.
    destruct 1; reflexivity.
  Defined.
End equality.

  Definition meq_ind_r :
    forall (A:Type) (x:A) (P:A -> Prop), P x -> forall y:A, y =m= x -> P y.
    intros A x P H y H0. elim meq_sym with (1 := H0); assumption.
  Defined.

  Definition meq_rec_r :
    forall (A:Type) (x:A) (P:A -> Set), P x -> forall y:A, y =m= x -> P y.
    intros A x P H y H0; elim meq_sym with (1 := H0); assumption.
  Defined.

  Definition meq_rect_r :
    forall (A:Type) (x:A) (P:A -> Type), P x -> forall y:A, y =m= x -> P y.
    intros A x P H y H0; elim meq_sym with (1 := H0); assumption.
  Defined.
(* End Logic_lemmas. *)

(* Module EqNotations. *)
(*   Notation "'rew' H 'in' H'" := (eq_rect _ _ H' _ H) *)
(*     (at level 10, H' at level 10, *)
(*      format "'[' 'rew'  H  in  '/' H' ']'"). *)
(*   Notation "'rew' [ P ] H 'in' H'" := (eq_rect _ P H' _ H) *)
(*     (at level 10, H' at level 10, *)
(*      format "'[' 'rew'  [ P ]  '/    ' H  in  '/' H' ']'"). *)
(*   Notation "'rew' <- H 'in' H'" := (eq_rect_r _ H' H) *)
(*     (at level 10, H' at level 10, *)
(*      format "'[' 'rew'  <-  H  in  '/' H' ']'"). *)
(*   Notation "'rew' <- [ P ] H 'in' H'" := (eq_rect_r P H' H) *)
(*     (at level 10, H' at level 10, *)
(*      format "'[' 'rew'  <-  [ P ]  '/    ' H  in  '/' H' ']'"). *)
(*   Notation "'rew' -> H 'in' H'" := (eq_rect _ _ H' _ H) *)
(*     (at level 10, H' at level 10, only parsing). *)
(*   Notation "'rew' -> [ P ] H 'in' H'" := (eq_rect _ P H' _ H) *)
(*     (at level 10, H' at level 10, only parsing). *)

(* End EqNotations. *)

(* Import EqNotations. *)

(* Lemma rew_opp_r : forall A (P:A->Type) (x y:A) (H:x=y) (a:P y), rew H in rew <- H in a = a. *)
(* Proof. *)
(* intros. *)
(* destruct H. *)
(* reflexivity. *)
(* Defined. *)

(* Lemma rew_opp_l : forall A (P:A->Type) (x y:A) (H:x=y) (a:P x), rew <- H in rew H in a = a. *)
(* Proof. *)
(* intros. *)
(* destruct H. *)
(* reflexivity. *)
(* Defined. *)

(* Theorem f_equal2 : *)
(*   forall (A1 A2 B:Type) (f:A1 -> A2 -> B) (x1 y1:A1) *)
(*     (x2 y2:A2), x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2. *)
(* Proof. *)
(*   destruct 1; destruct 1; reflexivity. *)
(* Qed. *)

(* Theorem f_equal3 : *)
(*   forall (A1 A2 A3 B:Type) (f:A1 -> A2 -> A3 -> B) (x1 y1:A1) *)
(*     (x2 y2:A2) (x3 y3:A3), *)
(*     x1 = y1 -> x2 = y2 -> x3 = y3 -> f x1 x2 x3 = f y1 y2 y3. *)
(* Proof. *)
(*   destruct 1; destruct 1; destruct 1; reflexivity. *)
(* Qed. *)

(* Theorem f_equal4 : *)
(*   forall (A1 A2 A3 A4 B:Type) (f:A1 -> A2 -> A3 -> A4 -> B) *)
(*     (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4), *)
(*     x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> f x1 x2 x3 x4 = f y1 y2 y3 y4. *)
(* Proof. *)
(*   destruct 1; destruct 1; destruct 1; destruct 1; reflexivity. *)
(* Qed. *)

(* Theorem f_equal5 : *)
(*   forall (A1 A2 A3 A4 A5 B:Type) (f:A1 -> A2 -> A3 -> A4 -> A5 -> B) *)
(*     (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4) (x5 y5:A5), *)
(*     x1 = y1 -> *)
(*     x2 = y2 -> *)
(*     x3 = y3 -> x4 = y4 -> x5 = y5 -> f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5. *)
(* Proof. *)
(*   destruct 1; destruct 1; destruct 1; destruct 1; destruct 1; reflexivity. *)
(* Qed. *)

(* Theorem f_equal_compose : forall A B C (a b:A) (f:A->B) (g:B->C) (e:a=b), *)
(*   f_equal g (f_equal f e) = f_equal (fun a => g (f a)) e. *)
(* Proof. *)
(*   destruct e. reflexivity. *)
(* Defined. *)

(* (** The goupoid structure of equality *) *)

(* Theorem eq_trans_refl_l : forall A (x y:A) (e:x=y), eq_trans eq_refl e = e. *)
(* Proof. *)
(*   destruct e. reflexivity. *)
(* Defined. *)

(* Theorem eq_trans_refl_r : forall A (x y:A) (e:x=y), eq_trans e eq_refl = e. *)
(* Proof. *)
(*   destruct e. reflexivity. *)
(* Defined. *)

(* Theorem eq_sym_involutive : forall A (x y:A) (e:x=y), eq_sym (eq_sym e) = e. *)
(* Proof. *)
(*   destruct e; reflexivity. *)
(* Defined. *)

(* Theorem eq_trans_sym_inv_l : forall A (x y:A) (e:x=y), eq_trans (eq_sym e) e = eq_refl. *)
(* Proof. *)
(*   destruct e; reflexivity. *)
(* Defined. *)

(* Theorem eq_trans_sym_inv_r : forall A (x y:A) (e:x=y), eq_trans e (eq_sym e) = eq_refl. *)
(* Proof. *)
(*   destruct e; reflexivity. *)
(* Defined. *)

(* Theorem eq_trans_assoc : forall A (x y z t:A) (e:x=y) (e':y=z) (e'':z=t), *)
(*   eq_trans e (eq_trans e' e'') = eq_trans (eq_trans e e') e''. *)
(* Proof. *)
(*   destruct e''; reflexivity. *)
(* Defined. *)

(* (** Extra properties of equality *) *)

(* Theorem eq_id_comm_l : forall A (f:A->A) (Hf:forall a, a = f a), forall a, f_equal f (Hf a) = Hf (f a). *)
(* Proof. *)
(*   intros. *)
(*   unfold f_equal. *)
(*   rewrite <- (eq_trans_sym_inv_l (Hf a)). *)
(*   destruct (Hf a) at 1 2. *)
(*   destruct (Hf a). *)
(*   reflexivity. *)
(* Defined. *)

(* Theorem eq_id_comm_r : forall A (f:A->A) (Hf:forall a, f a = a), forall a, f_equal f (Hf a) = Hf (f a). *)
(* Proof. *)
(*   intros. *)
(*   unfold f_equal. *)
(*   rewrite <- (eq_trans_sym_inv_l (Hf (f (f a)))). *)
(*   set (Hfsymf := fun a => eq_sym (Hf a)). *)
(*   change (eq_sym (Hf (f (f a)))) with (Hfsymf (f (f a))). *)
(*   pattern (Hfsymf (f (f a))). *)
(*   destruct (eq_id_comm_l f Hfsymf (f a)). *)
(*   destruct (eq_id_comm_l f Hfsymf a). *)
(*   unfold Hfsymf. *)
(*   destruct (Hf a). simpl. *)
(*   rewrite eq_trans_refl_l. *)
(*   reflexivity. *)
(* Defined. *)

(* Lemma eq_refl_map_distr : forall A B x (f:A->B), f_equal f (eq_refl x) = eq_refl (f x). *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma eq_trans_map_distr : forall A B x y z (f:A->B) (e:x=y) (e':y=z), f_equal f (eq_trans e e') = eq_trans (f_equal f e) (f_equal f e'). *)
(* Proof. *)
(* destruct e'. *)
(* reflexivity. *)
(* Defined. *)

(* Lemma eq_sym_map_distr : forall A B (x y:A) (f:A->B) (e:x=y), eq_sym (f_equal f e) = f_equal f (eq_sym e). *)
(* Proof. *)
(* destruct e. *)
(* reflexivity. *)
(* Defined. *)

(* Lemma eq_trans_sym_distr : forall A (x y z:A) (e:x=y) (e':y=z), eq_sym (eq_trans e e') = eq_trans (eq_sym e') (eq_sym e). *)
(* Proof. *)
(* destruct e, e'. *)
(* reflexivity. *)
(* Defined. *)

(* Lemma eq_trans_rew_distr : forall A (P:A -> Type) (x y z:A) (e:x=y) (e':y=z) (k:P x), *)
(*     rew (eq_trans e e') in k = rew e' in rew e in k. *)
(* Proof. *)
(*   destruct e, e'; reflexivity. *)
(* Qed. *)

(* Lemma rew_const : forall A P (x y:A) (e:x=y) (k:P), *)
(*     rew [fun _ => P] e in k = k. *)
(* Proof. *)
(*   destruct e; reflexivity. *)
(* Qed. *)
