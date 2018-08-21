(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Basic specifications : sets that may contain logical information *)

Set Implicit Arguments.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Require Import Notations.
Require Import Datatypes.
Require Import Logic.

(** Subsets and Msigma-types *)

(** [(msig A P)], or more suggestively [{x:A | P x}], denotes the subset
    of elements of the type [A] which satisfy the predicate [P].
    Similarly [(msig2 A P Q)], or [{x:A | P x & Q x}], denotes the subset
    of elements of the type [A] which satisfy both [P] and [Q]. *)

Inductive msig (A:Type) (P:A -> Prop) : Type :=
    mexist : forall x:A, P x -> msig P.

Inductive msig2 (A:Type) (P Q:A -> Prop) : Type :=
    mexist2 : forall x:A, P x -> Q x -> msig2 P Q.

(** [(msigT A P)], or more suggestively [{x:A & (P x)}] is a Msigma-type.
    Similarly for [(msigT2 A P Q)], also written [{x:A & (P x) & (Q x)}]. *)

Inductive msigT (A:Type) (P:A -> Type) : Type :=
    mexistT : forall x:A, P x -> msigT P.

Inductive msigT2 (A:Type) (P Q:A -> Type) : Type :=
    mexistT2 : forall x:A, P x -> Q x -> msigT2 P Q.

(* Notations *)

Arguments msig (A P)%type.
Arguments msig2 (A P Q)%type.
Arguments msigT (A P)%type.
Arguments msigT2 (A P Q)%type.

(* Notation "{ x  |  P }" := (msig (fun x => P)) : type_scope. *)
(* Notation "{ x  |  P  & Q }" := (msig2 (fun x => P) (fun x => Q)) : type_scope. *)
(* Notation "{ x : A  |  P }" := (msig (A:=A) (fun x => P)) : type_scope. *)
(* Notation "{ x : A  |  P  & Q }" := (msig2 (A:=A) (fun x => P) (fun x => Q)) : *)
(*   type_scope. *)
(* Notation "{ x : A  & P }" := (msigT (A:=A) (fun x => P)) : type_scope. *)
(* Notation "{ x : A  & P  & Q }" := (msigT2 (A:=A) (fun x => P) (fun x => Q)) : *)
(*   type_scope. *)

Add Printing Let msig.
Add Printing Let msig2.
Add Printing Let msigT.
Add Printing Let msigT2.


(** Mprojections of [msig]

    An element [y] of a subset [{x:A | (P x)}] is the pair of an [a]
    of type [A] and of a proof [h] that [a] satisfies [P].  Then
    [(mproj1_msig y)] is the witness [a] and [(mproj2_msig y)] is the
    proof of [(P a)] *)

(* Set Universe Polymorphism. *)
Section Subset_mprojections.

  Variable A : Type.
  Variable P : A -> Prop.

  Definition mproj1_msig (e:msig P) := match e with
                                    | mexist _ a b => a
                                    end.

  Definition mproj2_msig (e:msig P) :=
    match e return P (mproj1_msig e) with
    | mexist _ a b => b
    end.

End Subset_mprojections.


(** [msig2] of a predicate can be mprojected to a [msig].

    This allows [mproj1_msig] and [mproj2_msig] to be usable with [msig2].

    The [let] statements occur in the body of the [exist] so that
    [mproj1_msig] of a coerced [X : msig2 P Q] will unify with [let (a,
    _, _) := X in a] *)

Definition msig_of_msig2 (A : Type) (P Q : A -> Prop) (X : msig2 P Q) : msig P
  := mexist P
           (let (a, _, _) := X in a)
           (let (x, p, _) as s return (P (let (a, _, _) := s in a)) := X in p).

(** Mprojections of [msig2]

    An element [y] of a subset [{x:A | (P x) & (Q x)}] is the triple
    of an [a] of type [A], a of a proof [h] that [a] satisfies [P],
    and a proof [h'] that [a] satisfies [Q].  Then
    [(mproj1_msig (msig_of_msig2 y))] is the witness [a],
    [(mproj2_msig (msig_of_msig2 y))] is the proof of [(P a)], and
    [(mproj3_msig y)] is the proof of [(Q a)]. *)

Section Subset_mprojections2.

  Variable A : Type.
  Variables P Q : A -> Prop.

  Definition mproj3_msig (e : msig2 P Q) :=
    let (a, b, c) return Q (mproj1_msig (msig_of_msig2 e)) := e in c.

End Subset_mprojections2.


(** Mprojections of [msigT]

    An element [x] of a msigma-type [{y:A & P y}] is a dependent pair
    made of an [a] of type [A] and an [h] of type [P a].  Then,
    [(mprojT1 x)] is the first mprojection and [(mprojT2 x)] is the
    second mprojection, the type of which depends on the [mprojT1]. *)



Section Mprojections.

  Variable A : Type.
  Variable P : A -> Type.

  Definition mprojT1 (x:msigT P) : A := match x with
                                      | mexistT _ a _ => a
                                      end.

  Definition mprojT2 (x:msigT P) : P (mprojT1 x) :=
    match x return P (mprojT1 x) with
    | mexistT _ _ h => h
    end.

End Mprojections.

(** [msigT2] of a predicate can be mprojected to a [msigT].

    This allows [mprojT1] and [mprojT2] to be usable with [msigT2].

    The [let] statements occur in the body of the [existT] so that
    [mprojT1] of a coerced [X : msigT2 P Q] will unify with [let (a,
    _, _) := X in a] *)

Definition msigT_of_msigT2 (A : Type) (P Q : A -> Type) (X : msigT2 P Q) : msigT P
  := mexistT P
            (let (a, _, _) := X in a)
            (let (x, p, _) as s return (P (let (a, _, _) := s in a)) := X in p).

(** Mprojections of [msigT2]

    An element [x] of a msigma-type [{y:A & P y & Q y}] is a dependent
    pair made of an [a] of type [A], an [h] of type [P a], and an [h']
    of type [Q a].  Then, [(mprojT1 (msigT_of_msigT2 x))] is the first
    mprojection, [(mprojT2 (msigT_of_msigT2 x))] is the second mprojection,
    and [(mprojT3 x)] is the third mprojection, the types of which
    depends on the [mprojT1]. *)

Section Mprojections2.

  Variable A : Type.
  Variables P Q : A -> Type.

  Definition mprojT3 (e : msigT2 P Q) :=
    let (a, b, c) return Q (mprojT1 (msigT_of_msigT2 e)) := e in c.

End Mprojections2.

(** [msigT] of a predicate is equivalent to [msig] *)

Definition msig_of_msigT (A : Type) (P : A -> Prop) (X : msigT P) : msig P
  := mexist P (mprojT1 X) (mprojT2 X).

Definition msigT_of_msig (A : Type) (P : A -> Prop) (X : msig P) : msigT P
  := mexistT P (mproj1_msig X) (mproj2_msig X).

(** [msigT2] of a predicate is equivalent to [msig2] *)

Definition msig2_of_msigT2 (A : Type) (P Q : A -> Prop) (X : msigT2 P Q) : msig2 P Q
  := mexist2 P Q (mprojT1 (msigT_of_msigT2 X)) (mprojT2 (msigT_of_msigT2 X)) (mprojT3 X).

Definition msigT2_of_msig2 (A : Type) (P Q : A -> Prop) (X : msig2 P Q) : msigT2 P Q
  := mexistT2 P Q (mproj1_msig (msig_of_msig2 X)) (mproj2_msig (msig_of_msig2 X)) (mproj3_msig X).

(** [sumbool] is a boolean type equipped with the justification of
    their value *)

Inductive sumbool (A B:Prop) : Set :=
  | left : A -> {A} + {B}
  | right : B -> {A} + {B}
 where "{ A } + { B }" := (sumbool A B) : type_scope.

Add Printing If sumbool.

Arguments left {A B} _, [A] B _.
Arguments right {A B} _ , A [B] _.

(** [sumor] is an option type equipped with the justification of why
    it may not be a regular value *)

Inductive sumor (A:Type) (B:Prop) : Type :=
  | inleft : A -> A + {B}
  | inright : B -> A + {B}
 where "A + { B }" := (sumor A B) : type_scope.

Add Printing If sumor.

Arguments inleft {A B} _ , [A] B _.
Arguments inright {A B} _ , A [B] _.

(* Unset Universe Polymorphism. *)

(** Various forms of the axiom of choice for specifications *)

(* Section Choice_lemmas. *)

(*   Variables S S' : Set. *)
(*   Variable R : S -> S' -> Prop. *)
(*   Variable R' : S -> S' -> Set. *)
(*   Variables R1 R2 : S -> Prop. *)

(*   Lemma Choice : *)
(*    (forall x:S, {y:S' | R x y}) -> {f:S -> S' | forall z:S, R z (f z)}. *)
(*   Proof. *)
(*    intro H. *)
(*    exists (fun z => mproj1_msig (H z)). *)
(*    intro z; destruct (H z); assumption. *)
(*   Defined. *)

(*   Lemma Choice2 : *)
(*    (forall x:S, {y:S' & R' x y}) -> {f:S -> S' & forall z:S, R' z (f z)}. *)
(*   Proof. *)
(*     intro H. *)
(*     exists (fun z => mprojT1 (H z)). *)
(*     intro z; destruct (H z); assumption. *)
(*   Defined. *)

(*   Lemma bool_choice : *)
(*    (forall x:S, {R1 x} + {R2 x}) -> *)
(*      {f:S -> bool | forall x:S, f x = true /\ R1 x \/ f x = false /\ R2 x}. *)
(*   Proof. *)
(*     intro H. *)
(*     exists (fun z:S => if H z then true else false). *)
(*     intro z; destruct (H z); auto. *)
(*   Defined. *)

(* End Choice_lemmas. *)

(* Section Dependent_choice_lemmas. *)

(*   Variables X : Set. *)
(*   Variable R : X -> X -> Prop. *)

(*   Lemma dependent_choice : *)
(*     (forall x:X, {y | R x y}) -> *)
(*     forall x0, {f : nat -> X | f O = x0 /\ forall n, R (f n) (f (S n))}. *)
(*   Proof. *)
(*     intros H x0.  *)
(*     set (f:=fix f n := match n with O => x0 | S n' => mproj1_msig (H (f n')) end). *)
(*     exists f. *)
(*     split. reflexivity.  *)
(*     induction n; simpl; apply mproj2_msig. *)
(*   Defined. *)

(* End Dependent_choice_lemmas. *)


 (** A result of type [(Exc A)] is either a normal value of type [A] or
     an [error] :

     [Inductive Exc [A:Type] : Type := value : A->(Exc A) | error : (Exc A)].

     It is implemented using the option type. *)
(* Section Exc. *)
(*   Variable A : Type. *)

(*   Definition Exc := option A. *)
(*   Definition value := @Some A. *)
(*   Definition error := @None A. *)
(* End Exc. *)
(* Arguments error {A}. *)

(* Definition except := False_rec. (* for compatibility with previous versions *) *)

(* Arguments except [P] _. *)

(* Theorem absurd_set : forall (A:Prop) (C:Set), A -> ~ A -> C. *)
(* Proof. *)
(*   intros A C h1 h2. *)
(*   apply False_rec. *)
(*   apply (h2 h1). *)
(* Defined. *)

(* Hint Resolve left right inleft inright: core v62. *)
(* Hint Resolve exist exist2 existT existT2: core. *)

(* Compatibility *)

(* Notation msigS := msigT (compat "8.2"). *)
(* Notation existS := existT (compat "8.2"). *)
(* Notation msigS_rect := msigT_rect (compat "8.2"). *)
(* Notation msigS_rec := msigT_rec (compat "8.2"). *)
(* Notation msigS_ind := msigT_ind (compat "8.2"). *)
(* Notation mprojS1 := mprojT1 (compat "8.2"). *)
(* Notation mprojS2 := mprojT2 (compat "8.2"). *)

(* Notation msigS2 := msigT2 (compat "8.2"). *)
(* Notation existS2 := existT2 (compat "8.2"). *)
(* Notation msigS2_rect := msigT2_rect (compat "8.2"). *)
(* Notation msigS2_rec := msigT2_rec (compat "8.2"). *)
(* Notation msigS2_ind := msigT2_ind (compat "8.2"). *)
