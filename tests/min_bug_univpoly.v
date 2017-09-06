(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
Set Universe Polymorphism.
Set Implicit Arguments.

Require Export Notations.

(** * Equality *)

(** [eq x y], or simply [x=y] expresses the equality of [x] and
    [y]. Both [x] and [y] must belong to the same type [A].
    The definition is inductive and states the reflexivity of the equality.
    The others properties (symmetry, transitivity, replacement of
    equals by equals) are proved below. The type of [x] and [y] can be
    made explicit using the notation [x = y :> A]. This is Leibniz equality
    as it expresses that [x] and [y] are equal iff every property on
    [A] which is true of [x] is also true of [y] *)

Inductive eq (A:Type) (x:A) : A -> Prop :=
    eq_refl : x = x :>A

where "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (x <> y :>_) : type_scope.

Arguments eq {A} x _.
Arguments eq_refl {A x} , [A] x.

Arguments eq_ind [A] x P _ y _.
Arguments eq_rec [A] x P _ y _.
Arguments eq_rect [A] x P _ y _.


Section Logic_lemmas.

  Section equality.
    Variables A B : Type.
    Variable f : A -> B.
    Variables x y z : A.

    Theorem eq_sym : x = y -> y = x.
    Proof.
      destruct 1; reflexivity.
    Defined.

    Theorem eq_trans : x = y -> y = z -> x = z.
    Proof.
      destruct 2; trivial.
    Defined.

    Theorem f_equal : x = y -> f x = f y.
    Proof.
      destruct 1; reflexivity.
    Defined.

    Theorem not_eq_sym : x <> y -> y <> x.
    Proof.
      red; intros h1 h2; apply h1; destruct h2; reflexivity.
    Qed.

  End equality.

  Definition eq_ind_r :
    forall (A:Type) (x:A) (P:A -> Prop), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0. elim eq_sym with (1 := H0); assumption.
  Defined.

  Definition eq_rec_r :
    forall (A:Type) (x:A) (P:A -> Set), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0; elim eq_sym with (1 := H0); assumption.
  Defined.

  Definition eq_rect_r :
    forall (A:Type) (x:A) (P:A -> Type), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0; elim eq_sym with (1 := H0); assumption.
  Defined.
End Logic_lemmas.

Module EqNotations.
  Notation "'rew' H 'in' H'" := (eq_rect _ _ H' _ H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  H  in  '/' H' ']'").
  Notation "'rew' [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' <- H 'in' H'" := (eq_rect_r _ H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  <-  H  in  '/' H' ']'").
  Notation "'rew' <- [ P ] H 'in' H'" := (eq_rect_r P H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  <-  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' -> H 'in' H'" := (eq_rect _ _ H' _ H)
    (at level 10, H' at level 10, only parsing).
  Notation "'rew' -> [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
    (at level 10, H' at level 10, only parsing).

End EqNotations.

Import EqNotations.

Lemma rew_opp_r : forall A (P:A->Type) (x y:A) (H:x=y) (a:P y), rew H in rew <- H in a = a.
Proof.
intros.
destruct H.
reflexivity.
Defined.

Lemma rew_opp_l : forall A (P:A->Type) (x y:A) (H:x=y) (a:P x), rew <- H in rew H in a = a.
Proof.
intros.
destruct H.
reflexivity.
Defined.

Theorem f_equal2 :
  forall (A1 A2 B:Type) (f:A1 -> A2 -> B) (x1 y1:A1)
    (x2 y2:A2), x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.
Proof.
  destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal3 :
  forall (A1 A2 A3 B:Type) (f:A1 -> A2 -> A3 -> B) (x1 y1:A1)
    (x2 y2:A2) (x3 y3:A3),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> f x1 x2 x3 = f y1 y2 y3.
Proof.
  destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal4 :
  forall (A1 A2 A3 A4 B:Type) (f:A1 -> A2 -> A3 -> A4 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> f x1 x2 x3 x4 = f y1 y2 y3 y4.
Proof.
  destruct 1; destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal5 :
  forall (A1 A2 A3 A4 A5 B:Type) (f:A1 -> A2 -> A3 -> A4 -> A5 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4) (x5 y5:A5),
    x1 = y1 ->
    x2 = y2 ->
    x3 = y3 -> x4 = y4 -> x5 = y5 -> f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5.
Proof.
  destruct 1; destruct 1; destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal_compose : forall A B C (a b:A) (f:A->B) (g:B->C) (e:a=b),
  f_equal g (f_equal f e) = f_equal (fun a => g (f a)) e.
Proof.
  destruct e. reflexivity.
Defined.

(** The goupoid structure of equality *)

Theorem eq_trans_refl_l : forall A (x y:A) (e:x=y), eq_trans eq_refl e = e.
Proof.
  destruct e. reflexivity.
Defined.

Theorem eq_trans_refl_r : forall A (x y:A) (e:x=y), eq_trans e eq_refl = e.
Proof.
  destruct e. reflexivity.
Defined.

Theorem eq_sym_involutive : forall A (x y:A) (e:x=y), eq_sym (eq_sym e) = e.
Proof.
  destruct e; reflexivity.
Defined.

Theorem eq_trans_sym_inv_l : forall A (x y:A) (e:x=y), eq_trans (eq_sym e) e = eq_refl.
Proof.
  destruct e; reflexivity.
Defined.

Theorem eq_trans_sym_inv_r : forall A (x y:A) (e:x=y), eq_trans e (eq_sym e) = eq_refl.
Proof.
  destruct e; reflexivity.
Defined.

Theorem eq_trans_assoc : forall A (x y z t:A) (e:x=y) (e':y=z) (e'':z=t),
  eq_trans e (eq_trans e' e'') = eq_trans (eq_trans e e') e''.
Proof.
  destruct e''; reflexivity.
Defined.

(** Extra properties of equality *)

Theorem eq_id_comm_l : forall A (f:A->A) (Hf:forall a, a = f a), forall a, f_equal f (Hf a) = Hf (f a).
Proof.
  intros.
  unfold f_equal.
  rewrite <- (eq_trans_sym_inv_l (Hf a)).
  destruct (Hf a) at 1 2.
  destruct (Hf a).
  reflexivity.
Defined.

Theorem eq_id_comm_r : forall A (f:A->A) (Hf:forall a, f a = a), forall a, f_equal f (Hf a) = Hf (f a).
Proof.
  intros.
  unfold f_equal.
  rewrite <- (eq_trans_sym_inv_l (Hf (f (f a)))).
  set (Hfsymf := fun a => eq_sym (Hf a)).
  change (eq_sym (Hf (f (f a)))) with (Hfsymf (f (f a))).
  pattern (Hfsymf (f (f a))).
  destruct (eq_id_comm_l f Hfsymf (f a)).
  destruct (eq_id_comm_l f Hfsymf a).
  unfold Hfsymf.
  destruct (Hf a). simpl.
  rewrite eq_trans_refl_l.
  reflexivity.
Defined.

Lemma eq_refl_map_distr : forall A B x (f:A->B), f_equal f (eq_refl x) = eq_refl (f x).
Proof.
  reflexivity.
Qed.

Lemma eq_trans_map_distr : forall A B x y z (f:A->B) (e:x=y) (e':y=z), f_equal f (eq_trans e e') = eq_trans (f_equal f e) (f_equal f e').
Proof.
destruct e'.
reflexivity.
Defined.

Lemma eq_sym_map_distr : forall A B (x y:A) (f:A->B) (e:x=y), eq_sym (f_equal f e) = f_equal f (eq_sym e).
Proof.
destruct e.
reflexivity.
Defined.

Lemma eq_trans_sym_distr : forall A (x y z:A) (e:x=y) (e':y=z), eq_sym (eq_trans e e') = eq_trans (eq_sym e') (eq_sym e).
Proof.
destruct e, e'.
reflexivity.
Defined.

Lemma eq_trans_rew_distr : forall A (P:A -> Type) (x y z:A) (e:x=y) (e':y=z) (k:P x),
    rew (eq_trans e e') in k = rew e' in rew e in k.
Proof.
  destruct e, e'; reflexivity.
Qed.

Lemma rew_const : forall A P (x y:A) (e:x=y) (k:P),
    rew [fun _ => P] e in k = k.
Proof.
  destruct e; reflexivity.
Qed.

Set Implicit Arguments.

Declare ML Module "nat_syntax_plugin".

(********************************************************************)
(** * Container datatypes *)

(* Set Universe Polymorphism. *)

(** [option A] is the extension of [A] with an extra element [None] *)

Inductive option (A:Type) : Type :=
  | Some : A -> option A
  | None : option A.

Arguments Some {A} a.
Arguments None {A}.

Definition option_map (A B:Type) (f:A->B) (o : option A) : option B :=
  match o with
    | Some a => @Some B (f a)
    | None => @None B
  end.

(** [sum A B], written [A + B], is the disjoint sum of [A] and [B] *)

Inductive sum (A B:Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.

Notation "x + y" := (sum x y) : type_scope.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

Inductive prod (A B:Type) : Type :=
  pair : A -> B -> prod A B.

Add Printing Let prod.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Arguments pair {A B} _ _.

Section projections.
  Context {A : Type} {B : Type}.

  Definition fst (p:A * B) := match p with
				| (x, y) => x
                              end.
  Definition snd (p:A * B) := match p with
				| (x, y) => y
                              end.
End projections.

Hint Resolve pair inl inr: core.

Lemma surjective_pairing :
  forall (A B:Type) (p:A * B), p = pair (fst p) (snd p).
Proof.
  destruct p; reflexivity.
Qed.

Lemma injective_projections :
  forall (A B:Type) (p1 p2:A * B),
    fst p1 = fst p2 -> snd p1 = snd p2 -> p1 = p2.
Proof.
  destruct p1; destruct p2; simpl; intros Hfst Hsnd.
  rewrite Hfst; rewrite Hsnd; reflexivity.
Qed.

Definition prod_uncurry (A B C:Type) (f:prod A B -> C)
  (x:A) (y:B) : C := f (pair x y).

Definition prod_curry (A B C:Type) (f:A -> B -> C)
  (p:prod A B) : C := match p with
                       | pair x y => f x y
                       end.

(** Polymorphic lists and some operations *)

Inductive list (A : Type) : Type :=
 | nil : list A
 | cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} a l.
Infix "::" := cons (at level 60, right associativity) : list_scope.
Delimit Scope list_scope with list.
Bind Scope list_scope with list.

Local Open Scope list_scope.

Definition length (A : Type) : list A -> nat :=
  fix length l :=
  match l with
   | nil => O
   | _ :: l' => S (length l')
  end.

(** Concatenation of two lists *)

Definition app (A : Type) : list A -> list A -> list A :=
  fix app l m :=
  match l with
   | nil => m
   | a :: l1 => a :: app l1 m
  end.


Infix "++" := app (right associativity, at level 60) : list_scope.

Module MList.
Require Setoid.
Require Import PeanoNat Le Gt Minus Bool Lt.

Set Implicit Arguments.
(* Set Universe Polymorphism. *)

(******************************************************************)
(** * Basics: definition of polymorphic lists and some operations *)
(******************************************************************)

(** The definition of [list] is now in [Init/Datatypes],
    as well as the definitions of [length] and [app] *)

Open Scope list_scope.

(** Standard notations for lists.
In a special module to avoid conflicts. *)
Module ListNotations.
Notation "[mc: ]" := nil (format "[mc: ]") : list_scope.
Notation "[mc: x ]" := (cons x nil) : list_scope.
Notation "[mc: x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : list_scope.
End ListNotations.

Import ListNotations.

Section Lists.

  Variable A : Type.

  (** Head and tail *)

  Definition hd (default:A) (l:list A) :=
    match l with
      | [mc:] => default
      | x :: _ => x
    end.

  Definition hd_error (l:list A) :=
    match l with
      | [mc:] => None
      | x :: _ => Some x
    end.

  Definition tl (l:list A) :=
    match l with
      | [mc:] => nil
      | a :: m => m
    end.

  (** The [In] predicate *)
  Fixpoint In (a:A) (l:list A) : Prop :=
    match l with
      | [mc:] => False
      | b :: m => b = a \/ In a m
    end.

End Lists.


(*******************************************)
(** * Operations on the elements of a list *)
(*******************************************)

Section Elts.

  Variable A : Type.

  (*****************************)
  (** ** Nth element of a list *)
  (*****************************)

  Fixpoint nth (n:nat) (l:list A) (default:A) {struct l} : A :=
    match n, l with
      | O, x :: l' => x
      | O, other => default
      | S m, [mc:] => default
      | S m, x :: t => nth m t default
    end.

  Fixpoint nth_ok (n:nat) (l:list A) (default:A) {struct l} : bool :=
    match n, l with
      | O, x :: l' => true
      | O, other => false
      | S m, [mc:] => false
      | S m, x :: t => nth_ok m t default
    end.

  Fixpoint nth_error (l:list A) (n:nat) {struct n} : option A :=
    match n, l with
      | O, x :: _ => Some x
      | S n, _ :: l => nth_error l n
      | _, _ => None
    end.

  Definition nth_default (default:A) (l:list A) (n:nat) : A :=
    match nth_error l n with
      | Some x => x
      | None => default
    end.

  (*****************)
  (** ** Remove    *)
  (*****************)

  Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

  Fixpoint remove (x : A) (l : list A) : list A :=
    match l with
      | [mc:] => [mc:]
      | y::tl => if (eq_dec x y) then remove x tl else y::(remove x tl)
    end.


(******************************)
(** ** Last element of a list *)
(******************************)

  (** [last l d] returns the last element of the list [l],
    or the default value [d] if [l] is empty. *)

  Fixpoint last (l:list A) (d:A) : A :=
  match l with
    | [mc:] => d
    | [mc:a] => a
    | a :: l => last l d
  end.

  (** [removelast l] remove the last element of [l] *)

  Fixpoint removelast (l:list A) : list A :=
    match l with
      | [mc:] =>  [mc:]
      | [mc:a] => [mc:]
      | a :: l => a :: removelast l
    end.


  (******************************************)
  (** ** Counting occurrences of an element *)
  (******************************************)

  Fixpoint count_occ (l : list A) (x : A) : nat :=
    match l with
      | [mc:] => 0
      | y :: tl =>
        let n := count_occ tl x in
        if eq_dec y x then S n else n
    end.

End Elts.

(*******************************)
(** * Manipulating whole lists *)
(*******************************)

Section ListOps.

  Variable A : Type.

  (*************************)
  (** ** Reverse           *)
  (*************************)

  Fixpoint rev (l:list A) : list A :=
    match l with
      | [mc:] => [mc:]
      | x :: l' => rev l' ++ [mc:x]
    end.


  (**  An alternative tail-recursive definition for reverse *)

  Fixpoint rev_append (l l': list A) : list A :=
    match l with
      | [mc:] => l'
      | a::l => rev_append l (a::l')
    end.

  Definition rev' l : list A := rev_append l [mc:].


(*********************************************)
(** Reverse Induction Principle on Lists  *)
(*********************************************)

  (*************************)
  (** ** Concatenation     *)
  (*************************)

  Fixpoint concat (l : list (list A)) : list A :=
  match l with
  | nil => nil
  | cons x l => x ++ concat l
  end.


  (***********************************)
  (** ** Decidable equality on lists *)
  (***********************************)

  Hypothesis eq_dec : forall (x y : A), {x = y}+{x <> y}.

End ListOps.

(***************************************************)
(** * Applying functions to the elements of a list *)
(***************************************************)

(************)
(** ** Map  *)
(************)

Section Map.
  Variables (A : Type) (B : Type).
  Variable f : A -> B.

  Fixpoint map (l:list A) : list B :=
    match l with
      | [mc:] => [mc:]
      | a :: t => (f a) :: (map t)
    end.

  (** [flat_map] *)

  Definition flat_map (f:A -> list B) :=
    fix flat_map (l:list A) : list B :=
    match l with
      | nil => nil
      | cons x t => (f x)++(flat_map t)
    end.

End Map.


(************************************)
(** Left-to-right iterator on lists *)
(************************************)

Section Fold_Left_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : A -> B -> A.

  Fixpoint fold_left (l:list B) (a0:A) : A :=
    match l with
      | nil => a0
      | cons b t => fold_left t (f a0 b)
    end.

End Fold_Left_Recursor.

(************************************)
(** Right-to-left iterator on lists *)
(************************************)

Section Fold_Right_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : B -> A -> A.
  Variable a0 : A.

  Fixpoint fold_right (l:list B) : A :=
    match l with
      | nil => a0
      | cons b t => f b (fold_right t)
    end.

End Fold_Right_Recursor.

  (** [(list_power x y)] is [y^x], or the set of sequences of elts of [y]
      indexed by elts of [x], sorted in lexicographic order. *)

  Fixpoint list_power (A B:Type)(l:list A) (l':list B) :
    list (list (A * B)) :=
    match l with
      | nil => cons nil nil
      | cons x t =>
	flat_map (fun f:list (A * B) => map (fun y:B => cons (x, y) f) l')
        (list_power t l')
    end.


  (*************************************)
  (** ** Boolean operations over lists *)
  (*************************************)

  Section Bool.
    Variable A : Type.
    Variable f : A -> bool.

  (** find whether a boolean function can be satisfied by an
       elements of the list. *)

    Fixpoint existsb (l:list A) : bool :=
      match l with
	| nil => false
	| a::l => f a || existsb l
      end.

  (** find whether a boolean function is satisfied by
    all the elements of a list. *)

    Fixpoint forallb (l:list A) : bool :=
      match l with
	| nil => true
	| a::l => f a && forallb l
      end.

  (** [filter] *)

    Fixpoint filter (l:list A) : list A :=
      match l with
	| nil => nil
	| x :: l => if f x then x::(filter l) else filter l
      end.

  (** [find] *)

    Fixpoint find (l:list A) : option A :=
      match l with
	| nil => None
	| x :: tl => if f x then Some x else find tl
      end.

  (** [partition] *)

    Fixpoint partition (l:list A) : list A * list A :=
      match l with
	| nil => (nil, nil)
	| x :: tl => let (g,d) := partition tl in
	  if f x then (x::g,d) else (g,x::d)
      end.

  End Bool.




  (******************************************************)
  (** ** Operations on lists of pairs or lists of lists *)
  (******************************************************)

  Section ListPairs.
    Variables (A : Type) (B : Type).

  (** [split] derives two lists from a list of pairs *)

    Fixpoint split (l:list (A*B)) : list A * list B :=
      match l with
	| [mc:] => ([mc:], [mc:])
	| (x,y) :: tl => let (left,right) := split tl in (x::left, y::right)
      end.

  (** [list_prod] has the same signature as [combine], but unlike
     [combine], it adds every possible pairs, not only those at the
     same position. *)

    Fixpoint list_prod (l:list A) (l':list B) :
      list (A * B) :=
      match l with
	| nil => nil
	| cons x t => (map (fun y:B => (x, y)) l')++(list_prod t l')
      end.

  End ListPairs.




(*****************************************)
(** * Miscellaneous operations on lists  *)
(*****************************************)




(******************************)
(** ** Set inclusion on list  *)
(******************************)

Section SetIncl.

  Variable A : Type.

  Definition incl (l m:list A) := forall a:A, In a l -> In a m.
  Hint Unfold incl.


End SetIncl.


(**************************************)
(** * Cutting a list at some position *)
(**************************************)

Section Cutting.

  Variable A : Type.

  Fixpoint firstn (n:nat)(l:list A) : list A :=
    match n with
      | 0 => nil
      | S n => match l with
		 | nil => nil
		 | a::l => a::(firstn n l)
	       end
    end.


  Fixpoint skipn (n:nat)(l:list A) : list A :=
    match n with
      | 0 => l
      | S n => match l with
		 | nil => nil
		 | a::l => skipn n l
	       end
    end.


End Cutting.

(**********************************************************************)
(** ** Predicate for List addition/removal (no need for decidability) *)
(**********************************************************************)

Section Add.

  Variable A : Type.

  (* [Add a l l'] means that [l'] is exactly [l], with [a] added
     once somewhere *)
  Inductive Add (a:A) : list A -> list A -> Prop :=
    | Add_head l : Add a l (a::l)
    | Add_cons x l l' : Add a l l' -> Add a (x::l) (x::l').


End Add.


(***********************************)
(** ** Sequence of natural numbers *)
(***********************************)

Section NatSeq.

  (** [seq] computes the sequence of [len] contiguous integers
      that starts at [start]. For instance, [seq 2 3] is [2::3::4::nil]. *)

  Fixpoint seq (start len:nat) : list nat :=
    match len with
      | 0 => nil
      | S len => start :: seq (S start) len
    end.


End NatSeq.

Section Exists_Forall.

  (** * Existential and universal predicates over lists *)

  Variable A:Type.

  Section One_predicate.

    Variable P:A->Prop.

    Inductive Exists : list A -> Prop :=
      | Exists_cons_hd : forall x l, P x -> Exists (x::l)
      | Exists_cons_tl : forall x l, Exists l -> Exists (x::l).

    Hint Constructors Exists.

    Inductive Forall : list A -> Prop :=
      | Forall_nil : Forall nil
      | Forall_cons : forall x l, P x -> Forall l -> Forall (x::l).

    Hint Constructors Forall.

  End One_predicate.

End Exists_Forall.

Hint Constructors Exists.
Hint Constructors Forall.

Section Forall2.

  (** [Forall2]: stating that elements of two lists are pairwise related. *)

  Variables A B : Type.
  Variable R : A -> B -> Prop.

  Inductive Forall2 : list A -> list B -> Prop :=
    | Forall2_nil : Forall2 [mc:] [mc:]
    | Forall2_cons : forall x y l l',
      R x y -> Forall2 l l' -> Forall2 (x::l) (y::l').

  Hint Constructors Forall2.

End Forall2.

Hint Constructors Forall2.

Section ForallPairs.

  (** [ForallPairs] : specifies that a certain relation should
    always hold when inspecting all possible pairs of elements of a list. *)

  Variable A : Type.
  Variable R : A -> A -> Prop.

  Definition ForallPairs l :=
    forall a b, In a l -> In b l -> R a b.

  (** [ForallOrdPairs] : we still check a relation over all pairs
     of elements of a list, but now the order of elements matters. *)

  Inductive ForallOrdPairs : list A -> Prop :=
    | FOP_nil : ForallOrdPairs nil
    | FOP_cons : forall a l,
      Forall (R a) l -> ForallOrdPairs l -> ForallOrdPairs (a::l).

  Hint Constructors ForallOrdPairs.
End ForallPairs.

(** * Inversion of predicates over lists based on head symbol *)

Ltac is_list_constr c :=
 match c with
  | nil => idtac
  | (_::_) => idtac
  | _ => fail
 end.

Ltac invlist f :=
 match goal with
  | H:f ?l |- _ => is_list_constr l; inversion_clear H; invlist f
  | H:f _ ?l |- _ => is_list_constr l; inversion_clear H; invlist f
  | H:f _ _ ?l |- _ => is_list_constr l; inversion_clear H; invlist f
  | H:f _ _ _ ?l |- _ => is_list_constr l; inversion_clear H; invlist f
  | H:f _ _ _ _ ?l |- _ => is_list_constr l; inversion_clear H; invlist f
  | _ => idtac
 end.


Section Repeat.

  Variable A : Type.
  Fixpoint repeat (x : A) (n: nat ) :=
    match n with
      | O => [mc:]
      | S k => x::(repeat x k)
    end.

End Repeat.

Notation nil := nil (only parsing).
Notation cons := cons (only parsing).
Notation length := length (only parsing).
Notation app := app (only parsing).
(* Compatibility Names *)
Notation tail := tl (only parsing).
Notation head := hd_error (only parsing).

End MList.

Import MList.
Import MList.ListNotations.
Open Scope list.

Definition dec_bool {P} (x : {P}+{~P}) : bool :=
  match x with
  | left _ => true
  | _ => false
  end.

Definition option_to_bool {A} (ox : option A) : bool :=
  match ox with Some _ => true | _ => false end.

Definition is_empty {A} (l: list A) : bool :=
  match l with [mc:] => true | _ => false end.

Fixpoint but_last {A} (l : list A) : list A :=
  match l with
  | [mc:] => [mc:]
  | [mc:a] => [mc:]
  | a :: ls => a :: but_last ls
  end.

Fixpoint nsplit {A} (n : nat) (l : list A) : list A * list A :=
  match n, l with
  | 0, l => ([mc:], l)
  | S n', x :: l' => let (l1, l2) := nsplit n' l' in (x :: l1, l2)
  | _, _ => ([mc:], [mc:])
  end.


(* Need to load Unicoq to get the module dependency right *)
Declare ML Module "unicoq".
(** Load library "MetaCoqPlugin.cma". *)
Declare ML Module "MetaCoqPlugin".

Require Import Strings.String.
Require Import NArith.BinNat.
Require Import NArith.BinNatDef.
Unset Implicit Arguments.

(* From MetaCoq Require Export Types. *)

(* Set Universe Polymorphism. *)
Unset Universe Minimization ToSet.

Inductive Exception : Type := exception : Exception.

Definition StuckTerm : Exception. exact exception. Qed.

Definition NotAList : Exception. exact exception. Qed.

Definition TermNotGround : Exception. exact exception. Qed.

Definition WrongTerm : Exception. exact exception. Qed.

Definition HypMissesDependency : Exception. exact exception. Qed.
Definition TypeMissesDependency : Exception. exact exception. Qed.
Definition DuplicatedVariable : Exception. exact exception. Qed.
Definition NotAVar : Exception. exact exception. Qed.

Definition LtacError (s:string) : Exception. exact exception. Qed.

Definition NotUnifiable {A} (x y : A) : Exception. exact exception. Qed.

Definition Failure (s : string) : Exception. exact exception. Qed.

Definition NameExistsInContext (s : string) : Exception. exact exception. Qed.

Definition ExceptionNotGround : Exception. exact exception. Qed.

Definition CannotRemoveVar (x : string) : Exception. exact exception. Qed.

Definition RefNotFound (x : string) : Exception. exact exception. Qed.

Definition AbsDependencyError : Exception. exact exception. Qed.

Definition VarAppearsInValue : Exception. exact exception. Qed.

Definition NotAGoal : Exception. exact exception. Qed.

Definition DoesNotMatch : Exception. exact exception. Qed.
Definition NoPatternMatches : Exception. exact exception. Qed.
Definition Anomaly : Exception. exact exception. Qed.
Definition Continue : Exception. exact exception. Qed.

Definition NameNotFound (n: string) : Exception. exact exception. Qed.
Definition WrongType (T: Type) : Exception. exact exception. Qed.

Definition EmptyList : Exception. exact exception. Qed.
Definition NotThatManyElements : Exception. exact exception. Qed.

Definition CantCoerce : Exception. exact exception. Qed.
Definition NotCumul {A B} (x: A) (y: B) : Exception. exact exception. Qed.

Definition NotAnEvar {A} (x: A) : Exception. exact exception. Qed.
Definition CantInstantiate {A} (x t: A) : Exception. exact exception. Qed.

Polymorphic Record dyn := Dyn { type : Type; elem :> type }.
Arguments Dyn {_} _.

Inductive redlist A := rlnil | rlcons : A -> redlist A -> redlist A.

Arguments rlnil {_}.
Arguments rlcons {_} _ _.

Notation "[]rl" := rlnil.
Notation "[rl: x ; .. ; y ]" := (rlcons x (.. (rlcons y rlnil) ..)).

Inductive RedFlags :=
| RedBeta | RedDelta | RedMatch | RedFix | RedZeta
| RedDeltaC | RedDeltaX
| RedDeltaOnly : redlist dyn -> RedFlags
| RedDeltaBut : redlist dyn -> RedFlags.

Inductive Reduction :=
| RedNone
| RedSimpl
| RedOneStep
| RedWhd : redlist RedFlags -> Reduction
| RedStrong : redlist RedFlags -> Reduction
| RedVmCompute.

Inductive Unification : Type :=
| UniCoq : Unification
| UniMatch : Unification
| UniMatchNoRed : Unification
| UniEvarconv : Unification.

Inductive Hyp : Type :=
| ahyp : forall {A}, A -> option A -> Hyp.

Record Case :=
    mkCase {
        case_ind : Type;
        case_val : case_ind;
        case_return : dyn;
        case_branches : list dyn
        }.

(* Reduction primitive. It throws [NotAList] if the list of flags is not a list.  *)
Definition reduce (r : Reduction) {A} (x : A) := x.

Notation RedAll := ([rl:RedBeta;RedDelta;RedZeta;RedMatch;RedFix]).
Notation RedNF := (RedStrong RedAll).
Notation RedHNF := (RedWhd RedAll).

Notation rsimpl := (reduce RedSimpl).
Notation rhnf := (reduce RedHNF).
Notation rcbv := (reduce RedNF).
Notation rone_step := (reduce RedOneStep).
Notation "'dreduce' ( l1 , .. , ln )" :=
  (reduce (RedStrong [rl:RedBeta; RedFix; RedMatch;
           RedDeltaOnly (rlcons (Dyn (@l1)) ( .. (rlcons (Dyn (@ln)) rlnil) ..))]))
  (at level 0).

(** goal type *)
Inductive goal :=
  | Goal : forall {A}, A -> goal
  | AHyp : forall {A}, option A -> (A -> goal) -> goal
  | HypRem : forall {A}, A -> goal -> goal.

(** Pattern matching without pain *)
(* The M will be instantiated with the M monad or the gtactic monad. In principle,
we could make it part of the B, but then higher order unification will fail. *)
Inductive pattern (M : Type -> Type) (A : Type) (B : A -> Type) (y : A) : Prop :=
  | pbase : forall x : A, (y = x -> M (B x)) -> Unification -> pattern M A B y
  | ptele : forall {C}, (forall x : C, pattern M A B y) -> pattern M A B y.

Arguments pbase {M A B y} _ _ _.
Arguments ptele {M A B y C} _.

Notation "[? x .. y ] ps" := (ptele (fun x => .. (ptele (fun y => ps)).. ))
  (at level 202, x binder, y binder, ps at next level) : pattern_scope.
Notation "p => b" := (pbase p%core (fun _ => b%core) UniMatch)
  (no associativity, at level 201) : pattern_scope.
Notation "p => [ H ] b" := (pbase p%core (fun H => b%core) UniMatch)
  (no associativity, at level 201, H at next level) : pattern_scope.
Notation "'_' => b " := (ptele (fun x=> pbase x (fun _ => b%core) UniMatch))
  (at level 201, b at next level) : pattern_scope.

Notation "p '=n>' b" := (pbase p%core (fun _ => b%core) UniMatchNoRed)
  (no associativity, at level 201) : pattern_scope.
Notation "p '=n>' [ H ] b" := (pbase p%core (fun H => b%core) UniMatchNoRed)
  (no associativity, at level 201, H at next level) : pattern_scope.

Notation "p '=u>' b" := (pbase p%core (fun _ => b%core) UniCoq)
  (no associativity, at level 201) : pattern_scope.
Notation "p '=u>' [ H ] b" := (pbase p%core (fun H => b%core) UniCoq)
  (no associativity, at level 201, H at next level) : pattern_scope.

Delimit Scope pattern_scope with pattern.

Notation "'with' | p1 | .. | pn 'end'" :=
  ((@cons (pattern _ _ _ _) p1%pattern (.. (@cons (pattern _ _ _ _) pn%pattern nil) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.
Notation "'with' p1 | .. | pn 'end'" :=
  ((@cons (pattern _ _ _ _) p1%pattern (.. (@cons (pattern _ _ _ _) pn%pattern nil) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.

Delimit Scope with_pattern_scope with with_pattern.

(** THE definition of MetaCoq *)

Module M.
Inductive t : Type -> Prop :=
| ret : forall {A : Type}, A -> t A
| bind : forall {A : Type} {B : Type},
   t A -> (A -> t B) -> t B
| mtry' : forall {A : Type}, t A -> (Exception -> t A) -> t A
| raise : forall {A : Type}, Exception -> t A
| fix1' : forall {A : Type} {B : A -> Type} (S : Type -> Prop),
  (forall a : Type, S a -> t a) ->
  ((forall x : A, S (B x)) -> (forall x : A, S (B x))) ->
  forall x : A, t (B x)
| fix2' : forall {A1 : Type} {A2 : A1 -> Type} {B : forall (a1 : A1), A2 a1 -> Type} (S : Type -> Prop),
  (forall a : Type, S a -> t a) ->
  ((forall (x1 : A1) (x2 : A2 x1), S (B x1 x2)) ->
    (forall (x1 : A1) (x2 : A2 x1), S (B x1 x2))) ->
  forall (x1 : A1) (x2 : A2 x1), t (B x1 x2)
| fix3' : forall {A1 : Type} {A2 : A1 -> Type}  {A3 : forall (a1 : A1), A2 a1 -> Type} {B : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type} (S : Type -> Prop),
  (forall a : Type, S a -> t a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), S (B x1 x2 x3)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), S (B x1 x2 x3))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), t (B x1 x2 x3)
| fix4' : forall {A1 : Type} {A2 : A1 -> Type} {A3 : forall (a1 : A1), A2 a1 -> Type} {A4 : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type} {B : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2), A4 a1 a2 a3 -> Type} (S : Type -> Prop),
  (forall a : Type, S a -> t a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), S (B x1 x2 x3 x4)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), S (B x1 x2 x3 x4))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), t (B x1 x2 x3 x4)
| fix5' : forall {A1 : Type} {A2 : A1 -> Type} {A3 : forall (a1 : A1), A2 a1 -> Type} {A4 : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type} {A5 : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2), A4 a1 a2 a3 -> Type} {B : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2) (a4 : A4 a1 a2 a3), A5 a1 a2 a3 a4 -> Type} (S : Type -> Prop),
  (forall a : Type, S a -> t a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), S (B x1 x2 x3 x4 x5)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), S (B x1 x2 x3 x4 x5))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), t (B x1 x2 x3 x4 x5)

(** [is_var e] returns if [e] is a variable. *)
| is_var : forall {A : Type}, A -> t bool

(* [nu x od f] executes [f x] where variable [x] is added to the local context,
   optionally with definition [d] with [od = Some d].  It raises
   [NameExistsInContext] if the name "x" is in the context, or
   [VarAppearsInValue] if executing [f x] results in a term containing variable
   [x]. *)
| nu : forall {A : Type} {B : Type}, string -> option A -> (A -> t B) -> t B

(** [abs_fun x e] abstracts variable [x] from [e]. It raises [NotAVar[] if [x]
    is not a variable, or [AbsDependencyError] if [e] or its type [P] depends on
    a variable also depending on [x]. *)
| abs_fun : forall {A : Type} {P : A -> Type} (x : A), P x -> t (forall x, P x)

(** [abs_let x d e] returns [let x := d in e]. It raises [NotAVar] if [x] is not
    a variable, or [AbsDependencyError] if [e] or its type [P] depends on a
    variable also depending on [x]. *)
| abs_let : forall {A : Type} {P : A -> Type} (x: A) (y: A), P x -> t (let x := y in P x)

(** [abs_prod x e] returns [forall x, e]. It raises [NotAVar] if [x] is not a
    variable, or [AbsDependencyError] if [e] or its type [P] depends on a
    variable also depending on [x]. *)
| abs_prod : forall {A : Type} (x : A), Type -> t Type

(** [abs_fix f t n] returns [fix f {struct n} := t].
    [f]'s type must have n products, that is, be [forall x1, ..., xn, T] *)
| abs_fix : forall {A : Type}, A -> A -> N -> t A

(** [get_binder_name t] returns the name of variable [x] if:
    - [t = x],
    - [t = forall x, P x],
    - [t = fun x=>b],
    - [t = let x := d in b].
    It raises [WrongTerm] in any other case.
*)
| get_binder_name : forall {A : Type}, A -> t string

(** [remove x t] executes [t] in a context without variable [x].
    Raises [NotAVar] if [x] is not a variable, and
    [CannotRemoveVar "x"] if [t] or the environment depends on [x]. *)
| remove : forall {A : Type} {B : Type}, A -> t B -> t B

(** [evar A ohyps] creates a meta-variable with type [A] and,
    optionally, in the context resulting from [ohyp].

    It might raise [HypMissesDependency] if some variable in [ohyp]
    is referring to a variable not in the rest of the list
    (the order matters, and is from new-to-old). For instance,
    if [H : x > 0], then the context containing [H] and [x] should be
    given as:
    [ [ahyp H None; ahyp x None] ]

    If the type [A] is referring to variables not in the list of
    hypotheses, it raise [TypeMissesDependency]. If the list contains
    something that is not a variable, it raises [NotAVar]. If it contains duplicated
    occurrences of a variable, it raises a [DuplicatedVariable].
*)
| gen_evar : forall (A : Type), option (list Hyp) -> t A

(** [is_evar e] returns if [e] is a meta-variable. *)
| is_evar : forall {A : Type}, A -> t bool

(** [hash e n] returns a number smaller than [n] representing
    a hash of term [e] *)
| hash : forall {A : Type}, A -> N -> t N

(** [solve_typeclasses] calls type classes resolution. *)
| solve_typeclasses : t unit

(** [print s] prints string [s] to stdout. *)
| print : string -> t unit

(** [pretty_print e] converts term [e] to string. *)
| pretty_print : forall {A : Type}, A -> t string

(** [hyps] returns the list of hypotheses. *)
| hyps : t (list Hyp)

| destcase : forall {A : Type} (a : A), t (Case)

(** Given an inductive type A, applied to all its parameters (but not *)
(*     necessarily indices), it returns the type applied to exactly the *)
(*     parameters, and a list of constructors (applied to the parameters). *)
| constrs : forall {A : Type} (a : A), t (prod dyn (list dyn))
| makecase : forall (C : Case), t dyn

(** [munify x y r] uses reduction strategy [r] to equate [x] and [y].
    It uses convertibility of universes, meaning that it fails if [x]
    is [Prop] and [y] is [Type]. If they are both types, it will
    try to equate its leveles. *)
| unify {A} (x y : A) : Unification -> t (option (x = y))

(** [munify_univ A B r] uses reduction strategy [r] to equate universes
    [A] and [B].  It uses cumulativity of universes, e.g., it succeeds if
    [x] is [Prop] and [y] is [Type]. *)
| unify_univ (A B : Type) : Unification -> t (option (A -> B))

(** [get_reference s] returns the constant that is reference by s. *)
| get_reference : string -> t dyn

(** [get_var s] returns the var named after s. *)
| get_var : string -> t dyn

| call_ltac : forall {A : Type}, string -> list dyn -> t (prod A (list goal))
| list_ltac : t unit
.

Arguments t _%type.

Definition Cevar (A : Type) (ctx : list Hyp) : t A := gen_evar A (Some ctx).
Definition evar (A : Type) : t A := gen_evar A None.

Definition failwith {A} (s : string) : t A := raise (Failure s).

Definition fix1 {A} B := @fix1' A B t (fun _ x => x).
Definition fix2 {A1 A2} B := @fix2' A1 A2 B t (fun _ x => x).
Definition fix3 {A1 A2 A3} B := @fix3' A1 A2 A3 B t (fun _ x => x).
Definition fix4 {A1 A2 A3 A4} B := @fix4' A1 A2 A3 A4 B t (fun _ x => x).
Definition fix5 {A1 A2 A3 A4 A5} B := @fix5' A1 A2 A3 A4 A5 B t (fun _ x => x).

(** Defines [eval f] to execute after elaboration the Mtactic [f].
    It allows e.g. [rewrite (eval f)]. *)
Class runner A  (f : t A) := { eval : A }.
Arguments runner {A} _.
Arguments Build_runner {A} _ _.
Arguments eval {A} _ {_}.

Hint Extern 20 (runner ?f) =>
  (exact (Build_runner f ltac:(mrun f)))  : typeclass_instances.

Definition print_term {A} (x : A) : t unit :=
  bind (pretty_print x) (fun s=> print s).

Module monad_notations.
  Bind Scope M_scope with t.
  Delimit Scope M_scope with MC.
  Open Scope M_scope.

  Notation "r '<-' t1 ';' t2" := (@bind _ _ t1 (fun r=> t2%MC))
    (at level 81, right associativity, format "'[' r  '<-'  '[' t1 ;  ']' ']' '/' t2 ") : M_scope.
  Notation "t1 ';;' t2" := (bind t1 (fun _ => t2%MC))
    (at level 81, right associativity, format "'[' '[' t1 ;;  ']' ']' '/' t2 ") : M_scope.
  Notation "t >>= f" := (bind t f) (at level 70) : M_scope.

  Notation "'mif' b 'then' t 'else' u" :=
    (cond <- b; if cond then t else u) (at level 200) : M_scope.
End monad_notations.

Import monad_notations.

Fixpoint open_pattern {A P y} (p : pattern t A P y) : t (P y) :=
  match p with
  | pbase x f u =>
    oeq <- unify x y u;
    match oeq return t (P y) with
    | Some eq =>
      (* eq has type x = t, but for the pattern we need t = x.
         we still want to provide eq_refl though, so we reduce it *)
      let h := reduce (RedStrong [rl:RedBeta;RedDelta;RedMatch]) (eq_sym eq) in
      let 'eq_refl := eq in
      (* For some reason, we need to return the beta-reduction of the pattern, or some tactic fails *)
      let b := reduce (RedStrong [rl:RedBeta]) (f h) in b
    | None => raise DoesNotMatch
    end
  | @ptele _ _ _ _ C f => e <- evar C; open_pattern (f e)
  end.

Fixpoint mmatch' {A P} (y : A) (ps : list (pattern t A P y)) : t (P y) :=
  match ps with
  | [mc:] => raise NoPatternMatches
  | p :: ps' =>
    mtry' (open_pattern p) (fun e =>
      mif unify e DoesNotMatch UniMatchNoRed then mmatch' y ps' else raise e)
  end.

Module notations.
  Export monad_notations.

  (* We cannot make this notation recursive, so we loose
     notation in favor of naming. *)
  Notation "'\nu' x , a" := (
    let f := fun x => a in
    n <- get_binder_name f;
    nu n None f) (at level 81, x at next level, right associativity) : M_scope.

  Notation "'\nu' x : A , a" := (
    let f := fun x:A=>a in
    n <- get_binder_name f;
    nu n None f) (at level 81, x at next level, right associativity) : M_scope.

  Notation "'\nu' x := t , a" := (
    let f := fun x => a in
    n <- get_binder_name f;
    nu n (Some t) f) (at level 81, x at next level, right associativity) : M_scope.

  Notation "'mfix1' f ( x : A ) : 'M' T := b" :=
    (fix1 (fun x=>T%type) (fun f (x : A)=>b%MC))
    (at level 85, f at level 0, x at next level, format
    "'[v  ' 'mfix1'  f  '(' x  ':'  A ')'  ':'  'M'  T  ':=' '/  ' b ']'") : M_scope.

  Notation "'mfix2' f ( x : A ) ( y : B ) : 'M' T := b" :=
    (fix2 (fun (x : A) (y : B)=>T%type) (fun f (x : A) (y : B)=>b%MC))
    (at level 85, f at level 0, x at next level, y at next level, format
    "'[v  ' 'mfix2'  f  '(' x  ':'  A ')'  '(' y  ':'  B ')'  ':'  'M'  T  ':=' '/  ' b ']'") : M_scope.

  Notation "'mfix3' f ( x : A ) ( y : B ) ( z : C ) : 'M' T := b" :=
    (fix3 (fun (x : A) (y : B) (z : C)=>T%type) (fun f (x : A) (y : B) (z : C)=>b%MC))
    (at level 85, f at level 0, x at next level, y at next level, z at next level, format
    "'[v  ' 'mfix3'  f  '(' x  ':'  A ')'  '(' y  ':'  B ')'  '(' z  ':'  C ')'  ':'  'M'  T  ':=' '/  ' b ']'") : M_scope.

  Notation "'mfix4' f ( x1 : A1 ) ( x2 : A2 ) ( x3 : A3 ) ( x4 : A4 ) : 'M' T := b" :=
    (fix4 (fun (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4)=>T%type) (fun f (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4) =>b%MC))
    (at level 85, f at level 0, x1 at next level, x2 at next level, x3 at next level, x4 at next level, format
    "'[v  ' 'mfix4'  f  '(' x1  ':'  A1 ')'  '(' x2  ':'  A2 ')'  '(' x3  ':'  A3 ')'  '(' x4  ':'  A4 ')'  ':'  'M'  T  ':=' '/  ' b ']'") : M_scope.

  Notation "'mfix5' f ( x1 : A1 ) ( x2 : A2 ) ( x3 : A3 ) ( x4 : A4 ) ( x5 : A5 ) : 'M' T := b" :=
    (fix5 (fun (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4) (x5 : A5)=>T%type) (fun f (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4) (x5 : A5) =>b%MC))
    (at level 85, f at level 0, x1 at next level, x2 at next level, x3 at next level, x4 at next level, x5 at next level, format
    "'[v  ' 'mfix5'  f  '(' x1  ':'  A1 ')'  '(' x2  ':'  A2 ')'  '(' x3  ':'  A3 ')'  '(' x4  ':'  A4 ')'  '(' x5  ':'  A5 ')'  ':'  'M'  T  ':=' '/  ' b ']'") : M_scope.

  Notation "'mmatch' x ls" :=
    (@mmatch' _ (fun _ => _) x ls%with_pattern)
    (at level 90, ls at level 91) : M_scope.
  Notation "'mmatch' x 'return' 'M' p ls" :=
    (@mmatch' _ (fun x => p%type) x ls%with_pattern)
    (at level 90, ls at level 91) : M_scope.
  Notation "'mmatch' x 'as' y 'return' 'M' p ls" :=
    (@mmatch' _ (fun y => p%type) x ls%with_pattern)
    (at level 90, ls at level 91) : M_scope.

  Notation "'mtry' a ls" :=
    (mtry' a (fun e =>
      (@mmatch' _ (fun _ => _) e
                   (app ls%with_pattern [mc:([? x] x => raise x)%pattern]))))
      (at level 82, a at level 100, ls at level 91, only parsing) : M_scope.
End notations.

Import notations.

(* Utilities for lists *)
Definition map {A B} (f : A -> t B) :=
  mfix1 rec (l : list A) : M (list B) :=
    match l with
    | [mc:] => ret [mc:]
    | x :: xs => x <- f x; xs <- rec xs; ret (x :: xs)
    end.

Fixpoint mapi' (n : nat) {A B} (f : nat -> A -> t B) (l: list A) : t (list B) :=
  match l with
  | [mc:] => ret [mc:]
  | x :: xs =>
    el <- f n x;
    xs' <- mapi' (S n) f xs;
    ret (el :: xs')
  end.

Definition mapi := @mapi' 0.
Arguments mapi {_ _} _ _.

Definition filter {A} (b : A -> t bool) : list A -> t (list A) :=
  fix f l :=
    match l with
    | [mc:] => ret [mc:]
    | x :: xs => bx <- b x; r <- f xs;
                 if bx then ret (x :: r) else ret r
    end.

Definition hd {A} (l : list A) : t A :=
  match l with
  | a :: _ => ret a
  | _ => raise EmptyList
  end.

Fixpoint last {A} (l : list A) : t A :=
  match l with
  | [mc:a] => ret a
  | _ :: s => last s
  | _ => raise EmptyList
  end.

Definition fold_right {A B} (f : B -> A -> t A) (x : A) : list B -> t A :=
  fix loop l :=
    match l with
    | [mc:] => ret x
    | x :: xs => r <- loop xs; f x r
    end.

Definition fold_left {A B} (f : A -> B -> t A) : list B -> A -> t A :=
  fix loop l (a : A) :=
    match l with
    | [mc:] => ret a
    | b :: bs => r <- f a b; loop bs r
    end.

Definition index_of {A} (f : A -> t bool) (l : list A) : t (option nat) :=
  ir <- fold_left (fun (ir : (nat * option nat)) x =>
    let (i, r) := ir in
    match r with
    | Some _ => ret ir
    | _ => mif f x then ret (i, Some i) else ret (S i, None)
    end
  ) l (0, None);
  let (_, r) := ir in
  ret r.

Fixpoint nth {A} (n : nat) (l : list A) : t A :=
  match n, l with
  | 0, a :: _ => ret a
  | S n, _ :: s => nth n s
  | _, _ => raise NotThatManyElements
  end.

Definition iterate {A} (f : A -> t unit) : list A -> t unit :=
  fix loop l :=
    match l with
    | [mc:] => ret tt
    | b :: bs => f b;; loop bs
    end.

(** More utilitie *)
Definition mwith {A B} (c : A) (n : string) (v : B) : t dyn :=
  (mfix1 app (d : dyn) : M _ :=
    let (ty, el) := d in
    mmatch d with
    | [? T1 T2 f] @Dyn (forall x:T1, T2 x) f =>
      binder <- get_binder_name ty;
      oeq <- unify binder n UniMatchNoRed;
      if oeq then
        oeq' <- unify B T1 UniCoq;
        match oeq' with
        | Some eq' =>
          let v' := reduce (RedWhd [rl:RedMatch]) match eq' as x in _ = x with eq_refl=> v end in
          ret (Dyn (f v'))
        | _ => raise (WrongType T1)
        end
      else
        e <- evar T1;
        app (Dyn (f e))
    | _ => raise (NameNotFound n)
    end
  ) (Dyn c).

Definition type_of {A} (x : A) : Type := A.
Definition type_inside {A} (x : t A) : Type := A.

Definition unify_cumul {A B} (x: A) (y: B) (u : Unification) : t bool :=
  of <- unify_univ A B u;
  match of with
  | Some f =>
    let fx := reduce RedOneStep (f x) in
    oeq <- unify fx y u;
    match oeq with Some _ => ret true | None => ret false end
  | None => ret false
  end.

(** Unifies [x] with [y] and raises [NotUnifiable] if it they
    are not unifiable. *)
Definition unify_or_fail {A} (x y : A) : t (x = y) :=
  oeq <- unify x y UniCoq;
  match oeq with
  | None => raise (NotUnifiable x y)
  | Some eq => ret eq
  end.

(** Unifies [x] with [y] using cumulativity and raises [NotCumul] if it they
    are not unifiable. *)
Definition cumul_or_fail {A B} (x: A) (y: B) : t unit :=
  b <- unify_cumul x y UniCoq;
  if b then ret tt else raise (NotCumul x y).

Program Definition names_of_hyp : t (list string) :=
  env <- hyps;
  MList.fold_left (fun (ns : t (list string)) (h:Hyp)=>
    let (_, var, _) := h in
    n <- get_binder_name var;
    r <- ns; ret (n :: r)) env (ret [mc:]).

Definition hyps_except {A} (x : A) : t (list Hyp) :=
  l <- M.hyps;
  filter (fun y =>
    mmatch y with
    | [? b] ahyp x b => M.ret false
    | _ => ret true
    end) l.

Definition find_hyp_index {A} (x : A) : t(option nat) :=
  l <- M.hyps;
  index_of (fun y =>
    mmatch y with
    | [? b] ahyp x b => M.ret true
    | _ => ret false
    end) l.

(** given a string s it appends a marker to avoid collition with user
    provided names *)
Definition anonymize (s : string) : t string :=
  let s' := rcbv ("__" ++ s)%string in
  ret s'.

Definition fresh_name (name: string) : t string :=
  names <- names_of_hyp;
  let find name : t bool :=
    let res := reduce RedNF (find (fun n => dec_bool (string_dec name n)) names) in
    match res with None => ret false | _ => ret true end
  in
  (mfix1 f (name: string) : M string :=
     mif find name then
       let name := reduce RedNF (name ++ "_")%string in
       f name
     else ret name) name.

Definition fresh_binder_name {A} (x : A) : t string :=
  name <- mtry get_binder_name x with WrongTerm => ret "x"%string end;
  fresh_name name.

Definition unfold_projection {A} (y : A) : t A :=
  let x := rone_step y in
  let x := reduce (RedWhd [rl:RedBeta;RedMatch]) x in ret x.

(** [coerce x] coreces element [x] of type [A] into
    an element of type [B], assuming [A] and [B] are
    unifiable. It raises [CantCoerce] if it fails. *)
Definition coerce {A B : Type} (x : A) : t B :=
  oH <- unify A B UniCoq;
  match oH with
  | Some H => match H with eq_refl => ret x end
  | _ => raise CantCoerce
  end.

Definition is_prop_or_type (d : dyn) : t bool :=
  mmatch d with
  | Dyn Prop => ret true
  | Dyn Type => ret true
  | _ => ret false
  end.

(** [goal_type g] extracts the type of the goal or raises [NotAGoal]
    if [g] is not [Goal]. *)
Definition goal_type (g : goal) : t Type :=
  match g with
  | @Goal A _ => ret A
  | _ => raise NotAGoal
  end.

(** Convertion functions from [dyn] to [goal]. *)
Definition dyn_to_goal (d : dyn) : goal :=
  match d with
  | Dyn x => Goal x
  end.

Definition goal_to_dyn (g : goal) : t dyn :=
  match g with
  | Goal d => ret (Dyn d)
  | _ => raise NotAGoal
  end.

Definition cprint {A} (s : string) (c : A) : t unit :=
  x <- pretty_print c;
  let s := reduce RedNF (s ++ x)%string in
  print s.

(** Printing of a goal *)
Definition print_hyp (a : Hyp) : t unit :=
  let (A, x, ot) := a in
  sA <- pretty_print A;
  sx <- pretty_print x;
  match ot with
  | Some t =>
    st <- pretty_print t;
    M.print (sx ++ " := " ++ st ++ " : " ++ sA)
  | None => print (sx ++ " : " ++ sA)
  end.

Definition print_hyps : t unit :=
  l <- hyps;
  let l := rev' l in
  iterate print_hyp l.

Definition print_goal (g : goal) : t unit :=
  let repeat c := (fix repeat s n :=
    match n with
    | 0 => s
    | S n => repeat (c++s)%string n
    end) ""%string in
  G <- goal_type g;
  sg <- pretty_print G;
  let sep := repeat "="%string 20 in
  print_hyps;;
  print sep;;
  print sg;;
  ret tt.

(** [decompose x] decomposes value [x] into a head and a spine of
    arguments. For instance, [decompose (3 + 3)] returns
    [(Dyn add, [Dyn 3; Dyn 3])] *)
Definition decompose {A} (x : A) :=
  (mfix2 f (d : dyn) (args: list dyn) : M (dyn * list dyn) :=
    mmatch d with
    | [? A B (t1: A -> B) t2] Dyn (t1 t2) => f (Dyn t1) (Dyn t2 :: args)
    | [? A B (t1: forall x:A, B x) t2] Dyn (t1 t2) => f (Dyn t1) (Dyn t2 :: args)
    | _ => ret (d, args)
    end) (Dyn x) [mc:].

(** [instantiate x t] tries to instantiate meta-variable [x] with [t].
    It fails with [NotAnEvar] if [x] is not a meta-variable (applied to a spine), or
    [CantInstantiate] if it fails to find a suitable instantiation. [t] is beta-reduced
    to avoid false dependencies. *)
Definition instantiate {A} (x y : A) : t unit :=
  k <- decompose x;
  let (h, _) := k in
  let h := rcbv h.(elem) in
  b <- is_evar h;
  let t := reduce (RedWhd [rl:RedBeta]) t in
  if b then
    r <- unify x y UniEvarconv;
    match r with
    | Some _ => M.ret tt
    | _ => raise (CantInstantiate x y)
    end
  else raise (NotAnEvar h).
End M.

Notation M := M.t.

Import M.notations.

Notation "t 'mwhere' m := u" :=
  (elem (ltac:(mrun (v <- M.mwith t m u; M.ret v)%MC))) (at level 0).

Require Import Strings.String.
Import M.notations.

Require Import Strings.String.
Require Import NArith.BinNat.
Require Import NArith.BinNatDef.

(* Local Set Universe Polymorphism. *)

(** Exceptions *)
Definition NoGoalsLeft : Exception. exact exception. Qed.
Definition NotSameSize : Exception. exact exception. Qed.

Definition NotAProduct : Exception. exact exception. Qed.

Definition SomethingNotRight {A} (t : A) : Exception. exact exception. Qed.

Definition CantApply {T1 T2} (x:T1) (y:T2) : Exception. exact exception. Qed.

Definition CantFindConstructor : Exception. exact exception. Qed.
Definition ConstructorsStartsFrom1 : Exception. exact exception. Qed.

Definition Not1Constructor : Exception. exact exception. Qed.
Definition Not2Constructor : Exception. exact exception. Qed.

Definition DoesNotMatchGoal : Exception. exact exception. Qed.
Definition NoPatternMatchesGoal : Exception. exact exception. Qed.

Definition NotThatType : Exception. exact exception. Qed.

Definition NoProgress : Exception. constructor. Qed.

(** The type for tactics *)
Definition gtactic (A : Type) := goal -> M (list (A * goal)).
Notation tactic := (gtactic unit).

Delimit Scope tactic_scope with tactic.
Bind Scope tactic_scope with gtactic.

Module T.
Definition with_goal {A} (f : goal -> M A) := fun g =>
  y <- f g; M.ret [mc:(y,g)].

Coercion of_M {A} (x : M A) : gtactic A := with_goal (fun _ => x).

Definition mtry' {A} (t : gtactic A)
    (f : Exception -> gtactic A) : gtactic A := fun g =>
  M.mtry' (t g) (fun e => f e g).

Definition raise {A} (e : Exception) : gtactic A := M.raise e.

Definition fix0 (B : Type) : (gtactic B -> gtactic B) -> gtactic B :=
  @M.fix1 goal (fun _ => list (B * goal)).

Definition fix1 {A} (B : A -> Type) :
    ((forall x : A, gtactic (B x)) -> (forall x : A, gtactic (B x))) ->
    forall x : A, gtactic (B x) :=
  @M.fix2 A (fun _ => goal) (fun x _ => list (B x * goal)).

Definition fix2 {A1} {A2 : A1 -> Type} (B : forall a1 : A1, A2 a1 -> Type) :
    ((forall (x1 : A1) (x2 : A2 x1), gtactic (B x1 x2)) ->
      forall (x1 : A1) (x2 : A2 x1), gtactic (B x1 x2)) ->
    forall (x1 : A1) (x2 : A2 x1), gtactic (B x1 x2) :=
  @M.fix3 A1 A2 (fun _ _ => goal) (fun x y _ => list (B x y * goal)).

Definition fix3 {A1} {A2 : A1 -> Type} {A3 : forall a1 : A1, A2 a1 -> Type}
  (B : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type) :
    ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), gtactic (B x1 x2 x3)) ->
      forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), gtactic (B x1 x2 x3)) ->
    forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), gtactic (B x1 x2 x3) :=
  @M.fix4 A1 A2 A3 (fun _ _ _ => goal) (fun x y z _ => list (B x y z * goal)).

Definition fix4 {A1} {A2 : A1 -> Type} {A3 : forall a1 : A1, A2 a1 -> Type}
    {A4 : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type}
    (B : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2), A4 a1 a2 a3 -> Type) :
    ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), gtactic (B x1 x2 x3 x4)) ->
      forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), gtactic (B x1 x2 x3 x4)) ->
    forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), gtactic (B x1 x2 x3 x4) :=
  @M.fix5 A1 A2 A3 A4 (fun _ _ _ _ => goal) (fun x y z z' _ => list (B x y z z' * goal)).

Fixpoint pattern_map {A} {B : A -> Type} (g : goal) (y : A)
    (p : pattern gtactic A B y) : pattern M A (fun y => list (B y * goal)) y :=
  match p with
  | pbase x f r => pbase x (fun Heq => f Heq g) r
  | ptele f => ptele (fun x => pattern_map g y (f x))
  end.

Definition mmatch' {A P} (y : A)
    (ps : list (pattern gtactic A P y)) : gtactic (P y) := fun g =>
  M.mmatch' y (map (pattern_map g y) ps).

Definition ret {A} (x : A) : gtactic A := fun g => M.ret [mc:(x,g)].
Definition idtac : tactic := ret tt.

Definition try (t : tactic) : tactic := fun g=>
  mtry t g with _ => M.ret [mc:(tt, g)] end.

Definition or {A} (t u : gtactic A) : gtactic A := fun g=>
  mtry t g with _ => u g end.

Definition get_binder_name {A} (x : A) : gtactic string := fun g =>
  s <- M.get_binder_name x; M.ret [mc:(s,g)].

(** [close_goals x l] takes the list of goals [l] and appends
    hypothesis [x] to each of them. *)
Definition close_goals {A B} (y : B) : list (A * goal) -> M (list (A * goal)) :=
  M.map (fun '(x,g') => r <- M.abs_fun y g'; M.ret (x, @AHyp B None r)).

(** [let_close_goals x l] takes the list of goals [l] and appends
    hypothesis [x] with its definition to each of them (it assumes it is defined). *)
Definition let_close_goals {A B} (y : B) : list (A * goal) -> M (list (A * goal)) :=
  let t := rone_step y in (* to obtain x's definition *)
  M.map (fun '(x,g') => r <- M.abs_fun y g'; M.ret (x, @AHyp B (Some t) r)).

(** [rem_hyp x l] "removes" hypothesis [x] from the list of goals [l]. *)
Definition rem_hyp {A B} (x : B) (l: list (A * goal)) : M (list (A * goal)) :=
  let v := dreduce (@MList.map) (MList.map (fun '(y,g) => (y, HypRem x g)) l) in M.ret v.

(** Returns if a goal is open, i.e., a meta-variable. *)
Fixpoint is_open (g : goal) : M bool :=
  match g with
  | Goal e => M.is_evar e
  | @AHyp C _ f =>
    x <- M.fresh_binder_name f;
    (* we get the name in order to avoid inserting existing names
      (nu will raise an exception otherwise) *)
    M.nu x None (fun x : C => is_open (f x))
  | HypRem _ g => is_open g (* we don't care about the variable *)
  end.

(** removes the goals that were solved *)
Definition filter_goals {A} : list (A * goal) -> M (list (A * goal)) :=
  M.filter (fun '(x,g) => is_open g).

(** [open_and_apply t] is a tactic that "opens" the current goal
    (pushes all the hypotheses in the context) and applies tactic [t]
    to the so-opened goal. The result is "closed" back. *)
Definition open_and_apply {A} (t : gtactic A) : gtactic A :=
  fix open g :=
    match g return M _ with
    | Goal _ => t g
    | @AHyp C None f =>
      x <- M.fresh_binder_name f;
      M.nu x None (fun x : C =>
        open (f x) >>= close_goals x)
    | @AHyp C (Some t) f =>
      x <- M.fresh_binder_name f;
      M.nu x (Some t) (fun x : C =>
        open (f x) >>= let_close_goals x)
    | HypRem x f =>
      M.remove x (open f) >>= rem_hyp x
    end.

Definition bind {A B} (t : gtactic A) (f : A -> gtactic B) : gtactic B := fun g =>
  gs <- t g;
  r <- M.map (fun '(x,g') => open_and_apply (f x) g') gs;
  let res := dreduce (concat, @app) (concat r) in
  M.ret res.

Class Seq (A B C : Type) :=
  seq : gtactic A -> C -> gtactic B.
Arguments seq {A B C _} _%tactic _%tactic.

Instance seq_one {A B} : Seq A B (gtactic B) := fun t1 t2 => bind t1 (fun _ => t2).

Fixpoint gmap {A} (tacs : list (gtactic A)) (gs : list goal) : M (list (list (A * goal))) :=
  match tacs, gs with
  | [mc:], [mc:] => M.ret [mc:]
  | tac :: tacs', g :: gs' =>
    fa <- open_and_apply tac g;
    rest <- gmap tacs' gs';
    M.ret (fa :: rest)
  | l, l' => M.raise NotSameSize
  end.

Instance seq_list {A B} : Seq A B (list (gtactic B)) := fun t f g =>
  gs <- t g;
  ls <- gmap f (map snd gs);
  let res := dreduce (MList.concat, app) (concat ls) in
  M.ret res.

Definition exact {A} (x:A) : tactic := fun g =>
  match g with
  | Goal g => M.cumul_or_fail x g;; M.ret [mc:]
  | _ => M.raise NotAGoal
  end.

Definition goal_type : gtactic Type := with_goal M.goal_type.

(** [intro_base n t] introduces variable or definition named [n]
    in the context and executes [t n].
    Raises [NotAProduct] if the goal is not a product or a let-binding. *)
Definition intro_base {A B} (var : string) (t : A -> gtactic B) : gtactic B := fun g =>
  mmatch g with
  | [? B (def: B) P e] @Goal (let x := def in P x) e =n>
    (* normal match will not instantiate meta-variables from the scrutinee, so we do the inification here*)
    eqBA <- M.unify_or_fail B A;
    M.nu var (Some def) (fun x=>
      let Px := reduce (RedWhd [rl:RedBeta]) (P x) in
      e' <- M.evar Px;
      nG <- M.abs_let (P:=P) x def e';
      exact nG g;;
      let x := reduce (RedWhd [rl:RedMatch]) (match eqBA with eq_refl => x end) in
      t x (Goal e') >>= let_close_goals x)
  | [? P e] @Goal (forall x:A, P x) e =u>
    M.nu var None (fun x=>
      let Px := reduce (RedWhd [rl:RedBeta]) (P x) in
      e' <- M.evar Px;
      nG <- M.abs_fun (P:=P) x e';
      exact nG g;;
      t x (Goal e') >>= close_goals x)
  | _ => M.raise NotAProduct
  end.

Definition intro_cont {A B} (t : A -> gtactic B) : gtactic B := fun g=>
  n <- M.get_binder_name t;
  intro_base n t g.

(** Given a name of a variable, it introduces it in the context *)
Definition intro_simpl (var : string) : tactic := fun g =>
  A <- M.evar Type;
  intro_base var (fun _ : A => idtac) g.

(** Introduces an anonymous name based on a binder *)
Definition intro_anonymous {A} (T : A) (f : string -> M string) (g : goal) : M goal :=
  name <- M.get_binder_name T;
  axn <- M.anonymize name;
  axn <- f axn;
  res <- intro_simpl axn g >>= M.hd;
  M.ret (snd res).

(** Introduces all hypotheses. Does not fail if there are 0. *)
Definition intros_all : tactic :=
  mfix1 f (g : goal) : M (list (unit * goal)) :=
    open_and_apply (fun g =>
      match g return M (list (unit * goal)) with
      | @Goal T e =>
        mtry intro_anonymous T M.ret g >>= f with
        | WrongTerm => M.ret [mc:(tt,g)]
        | NotAProduct => M.ret [mc:(tt,g)]
        | [? s] NameExistsInContext s => intro_anonymous T M.fresh_name g >>= f
        end
      | _ => M.raise NotAGoal
      end) g.

(** Introduces up to n binders. Throws [NotAProduct] if there
    aren't enough products in the goal.  *)
Definition introsn : nat -> tactic :=
  mfix2 f (n : nat) (g : goal) : M (list (unit * goal)) :=
    open_and_apply (fun g =>
      match n, g with
      | 0, g => M.ret [mc:(tt,g)]
      | S n', @Goal T e =>
        mtry intro_anonymous T M.ret g >>= f n' with
        | WrongTerm => M.raise NotAProduct
        | [? s] NameExistsInContext s => intro_anonymous T M.fresh_name g >>= f n'
        end
      | _, _ => M.failwith "Should never get here"
      end) g.

(** Applies reflexivity *)
Definition prim_reflexivity : tactic := fun g =>
  A <- M.evar Type;
  x <- M.evar A;
  M.unify_or_fail g (Goal (Coq.Init.Logic.eq_refl x));; M.ret [mc:].

(** Fist introduces the hypotheses and then applies reflexivity *)
Definition reflexivity : tactic := fun g =>
  l <- intros_all g;
  g <- M.hd l;
  open_and_apply prim_reflexivity (snd g).

(** Overloaded binding *)
Definition copy_ctx {A} (B : A -> Type) : dyn -> M Type :=
  mfix1 rec (d : dyn) : M Type :=
    mmatch d with
    | [? c : A] Dyn c =>
      let Bc := reduce (RedWhd [rl:RedBeta]) (B c) in
      M.ret Bc
    | [? C (D : C -> Type) (c : forall y:C, D y)] Dyn c =>
      n <- M.fresh_binder_name c;
      M.nu n None (fun y=>
        r <- rec (Dyn (c y));
        M.abs_prod y r)
    | [? C D (c : C->D)] Dyn c =>
      n <- M.fresh_binder_name c;
      M.nu n None (fun y=>
        r <- rec (Dyn (c y));
        M.abs_prod y r)
    | _ => M.print_term A;; M.raise (SomethingNotRight d)
    end.

(** Generalizes a goal given a certain hypothesis [x]. It does not
    remove [x] from the goal. *)
Definition generalize {A} (x : A) : tactic := fun g =>
  P <- M.goal_type g;
  aP <- M.abs_prod x P; (* aP = (forall x:A, P) *)
  e <- M.evar aP;
  mmatch aP with
  | [? Q : A -> Type] (forall z:A, Q z) =n> [H]
    let e' :=
      rcbv match H in _ = Q return Q with eq_refl _ => e end in
    exact (e' x) g;;
    M.ret [mc:(tt, Goal e)]
  | _ => M.failwith "generalize: should never happen"
  end.

(** Clear hypothesis [x] and continues the execution on [cont] *)
Definition cclear {A B} (x:A) (cont : gtactic B) : gtactic B := fun g=>
  gT <- M.goal_type g;
  r <- M.remove x (
    e <- M.evar gT;
    l <- cont (Goal e);
    M.ret (e, l));
  let (e, l) := r in
  exact e g;;
  rem_hyp x l.

Definition clear {A} (x : A) : tactic := cclear x idtac.

Definition destruct {A : Type} (n : A) : tactic := fun g=>
  let A := rhnf A in
  b <- let n := rcbv n in M.is_var n;
  ctx <- if b then M.hyps_except n else M.hyps;
  P <- M.Cevar (A->Type) ctx;
  let Pn := P n in
  gT <- M.goal_type g;
  M.unify_or_fail Pn gT;;
  l <- M.constrs A;
  l <- M.map (fun d : dyn =>
    (* a constructor c has type (forall x, ... y, A) and we return
       (forall x, ... y, P (c x .. y)) *)
    t' <- copy_ctx P d;
    e <- M.Cevar t' ctx;
    M.ret {| elem := e |}) (snd l);
  let c := {| case_ind := A;
              case_val := n;
              case_return := {| elem := P |};
              case_branches := l
           |} in
  case <- M.makecase c;
  case <- M.unfold_projection (elem case);
  exact case g;;
  let res := dreduce (map, M.dyn_to_goal)
                     (map (fun d => (tt, M.dyn_to_goal d)) l) in
  M.ret res.

(** Destructs the n-th hypotheses in the goal (counting from 0) *)
Definition destructn (n : nat) : tactic :=
  bind (introsn n) (fun _ g =>
    A <- M.evar Type;
    n <- M.fresh_name "tmp";
    @intro_base A _ n destruct g).

Definition apply {T} (c : T) : tactic := fun g=>
  match g with Goal eg =>
    (mfix1 app (d : dyn) : M (list (unit * goal)) :=
      let (_, el) := d in
      mif M.unify_cumul el eg UniCoq then M.ret [mc:] else
        mmatch d return M (list (unit * goal)) with
        | [? T1 T2 f] @Dyn (forall x:T1, T2 x) f =>
          e <- M.evar T1;
          r <- app (Dyn (f e));
          mif M.is_evar e then M.ret ((tt, Goal e) :: r) else M.ret r
        | _ =>
          gT <- M.goal_type g;
          M.raise (CantApply T gT)
        end) (Dyn c)
  | _ => M.raise NotAGoal
  end.

Definition change (P : Type) : tactic := fun g =>
  gT <- M.goal_type g;
  M.unify_or_fail P gT;;
  e <- M.evar P;
  exact e g;;
  M.ret [mc:(tt, Goal e)].

Definition change_hyp {P Q} (H : P) (newH: Q) : tactic :=
  cclear H (bind (get_binder_name H) intro_simpl).

Inductive goal_pattern (B : Type) :=
  | gbase : forall {A}, A -> gtactic B -> goal_pattern B
  | gbase_context : forall {A}, A -> ((A -> Type) -> gtactic B) -> goal_pattern B
  | gtele : forall {C}, (C -> goal_pattern B) -> goal_pattern B
  | gtele_evar : forall {C}, (C -> goal_pattern B) -> goal_pattern B.
Arguments gbase {B A} _ _.
Arguments gbase_context {B A} _ _.
Arguments gtele {B C} _.
Arguments gtele_evar {B C} _.

Definition match_goal_context
    {C A} (x : A) : forall {B}, B -> ((A -> B) -> gtactic C) -> gtactic C :=
  mfix4 go (B : Type) (y : B) (t : (A -> B) -> gtactic C) (g : goal): M (list (C * goal)) :=
  let recur := fun {B} (y : B) (t : (A -> B) -> gtactic C) =>
    mmatch y with
    | [? A' (h : A' -> B) z] h z =n>
      mtry go _ z (fun C => t (fun a => h (C a))) g with
      | DoesNotMatchGoal => go _ h (fun C => t (fun a => C a z)) g
      end
    | _ => M.raise DoesNotMatchGoal
    end in
  oeqAB <- M.unify B A UniMatchNoRed;
  match oeqAB with
  | Some eqAB =>
    let 'eq_refl := eq_sym eqAB in fun (y : A) t =>
    mif M.unify_cumul x y UniMatchNoRed then
      let term := reduce (RedStrong [rl:RedBeta]) (t (fun a => a) g) in
      term
    else recur y t
  | None => recur
  end y t.

Fixpoint match_goal_pattern' {B}
    (u : Unification) (p : goal_pattern B) : list Hyp -> list Hyp -> gtactic B :=
  fix go l1 l2 g :=
  match p, l2 with
  | gbase P t, _ =>
    gT <- M.goal_type g;
    mif M.unify_cumul P gT u then t g
    else M.raise DoesNotMatchGoal
  | gbase_context x t, _ =>
    gT <- M.goal_type g;
    match_goal_context x gT t g
  | @gtele _ C f, (@ahyp A a d :: l2') =>
    oeqCA <- M.unify C A u;
    match oeqCA with
    | Some eqCA =>
      let a' := rcbv match eq_sym eqCA with eq_refl => a end in
      mtry match_goal_pattern' u (f a') [mc:] (MList.rev_append l1 l2')%list g
      with DoesNotMatchGoal =>
        go (ahyp a d :: l1) l2' g
      end
    | None => go (ahyp a d :: l1) l2' g end
  | @gtele_evar _ C f, _ =>
    e <- M.evar C;
    match_goal_pattern' u (f e) l1 l2 g
  | _, _ => M.raise DoesNotMatchGoal
  end.

Definition match_goal_pattern {B} (u : Unification)
    (p : goal_pattern B) : gtactic B := fun g=>
  r <- M.hyps; match_goal_pattern' u p [mc:] (MList.rev' r) g.

Fixpoint match_goal_base {B} (u : Unification)
    (ps : list (goal_pattern B)) : gtactic B := fun g =>
  match ps with
  | [mc:] => M.raise NoPatternMatchesGoal
  | p :: ps' =>
    mtry match_goal_pattern u p g
    with DoesNotMatchGoal => match_goal_base u ps' g end
  end.

Definition ltac (t : string) (args : list dyn) : tactic := fun g =>
  d <- M.goal_to_dyn g;
  let (ty, el) := d in
  v <- @M.call_ltac ty t args;
  let (v, l) := v in
  M.unify_or_fail v el;;
  b <- M.is_evar v;
  if b then
    M.ret [mc:(tt, Goal v)] (* it wasn't solved *)
  else
    let l' := dreduce (@MList.map) (map (pair tt) l) in
    M.ret l'.

Definition destruct_all (T : Type) : tactic := fun g=>
  l <- M.hyps;
  l <- M.filter (fun h : Hyp=>
    let (Th, _, _) := h in
    r <- M.unify Th T UniCoq;
    M.ret (option_to_bool r)) l;
  (fix f (l : list Hyp) : tactic :=
    match l with
    | [mc:] => idtac
    | ahyp x _ :: l => bind (destruct x) (fun _ => f l)
    end) l g.

Definition treduce (r : Reduction) : tactic := fun g=>
  T <- M.goal_type g;
  let T' := reduce r T in
  e <- M.evar T';
  b <- M.unify_cumul g (@Goal T e) UniMatch;
  match b with
  | true => M.ret [mc:(tt, Goal e)]
  | _ => M.failwith "It should never fail here"
  end.

Definition typed_intro (T : Type) : tactic := fun g =>
  U <- M.goal_type g;
  mmatch U with
  | [? P:T->Type] forall x:T, P x =>
    xn <- M.get_binder_name U;
    intro_simpl xn g
  | _ => M.raise NotThatType
  end.

Definition typed_intros (T : Type) : tactic := fun g =>
  (mfix1 f (g : goal) : M _ :=
    mtry bind (typed_intro T) (fun _ => f) g with
    | NotThatType => idtac g
    end) g.

Definition cpose_base {A B} (name : string) (t : A)
    (cont : A -> gtactic B) : gtactic B := fun g =>
  M.nu name (Some t) (fun x=>
    gT <- M.goal_type g;
    r <- M.evar gT;
    value <- M.abs_let x t r;
    exact value g;;
    cont x (Goal r) >>= let_close_goals x).

Definition cpose {A} (t: A) (cont : A -> tactic) : tactic := fun g =>
  n <- M.get_binder_name cont;
  cpose_base n t cont g.

Definition cassert_base {A} (name : string)
    (cont : A -> tactic) : tactic := fun g =>
  a <- M.evar A; (* [a] will be the goal to solve [A] *)
  M.nu name None (fun x =>
    gT <- M.goal_type g;
    r <- M.evar gT; (* The new goal now referring to n *)
    value <- M.abs_fun x r;
    exact (value a) g;; (* instantiate the old goal with the new one *)
    v <- cont x (Goal r) >>= close_goals x;
    M.ret ((tt,Goal a) :: v)). (* append the goal for a to the top of the goals *)

Definition cassert {A} (cont : A -> tactic) : tactic := fun g=>
  n <- M.get_binder_name cont;
  cassert_base n cont g.

(** [cut U] creates two goals with types [U -> T] and [U], where
    [T] is the type of the current goal. *)
Definition cut (U : Type) : tactic := fun g =>
  T <- M.goal_type g;
  ut <- M.evar (U -> T);
  u <- M.evar U;
  exact (ut u) g;;
  M.ret [mc:(tt,Goal ut); (tt,Goal u)].

(* performs simpl in each hypothesis and in the goal *)
Definition simpl_in_all : tactic := fun g =>
  l <- M.hyps;
  l <- M.fold_right (fun (hyp : Hyp) hyps =>
    let (A, x, ot) := hyp in
    let A := rsimpl A in
    M.ret (@ahyp A x ot :: hyps)
  ) [mc:] l;
  T <- M.goal_type g;
  let T := rsimpl T in
  e <- M.Cevar T l; (* create the new goal in the new context *)
  (* we need normal unification since g might be a compound value *)
  oeq <- M.unify g (Goal e) UniCoq;
  match oeq with
  | Some (eq_refl _) => M.ret [mc:(tt,Goal e)]
  | _ => M.raise exception (* should never happen *)
  end.

Definition reduce_in (r : Reduction) {P} (H : P) : tactic := fun g =>
  l <- M.hyps;
  l' <- M.map (fun hyp : Hyp =>
    let (T, v, def) := hyp in
    mif M.unify_cumul H v UniMatchNoRed then
      let T' := reduce r T in M.ret (@ahyp T' v def)
    else M.ret hyp) l;
  gT <- M.goal_type g;
  e <- M.Cevar gT l';
  oeq <- M.unify (Goal e) g UniCoq;
  match oeq with
  | Some (eq_refl _) => M.ret [mc:(tt,Goal e)]
  | _ => M.raise exception (* should never happen *)
  end.

Definition simpl_in {P} (H : P) : tactic :=
  reduce_in RedSimpl H.

(** exists tactic *)
Definition mexists {A} (x: A) : tactic := fun g =>
  P <- M.evar _;
  e <- M.evar _;
  oeq <- M.unify g (Goal (@ex_intro _ P x e)) UniCoq;
  match oeq with
  | Some (eq_refl _) => M.ret [mc:(tt,Goal e)]
  | _ => M.raise (NotUnifiable g (Goal (@ex_intro _ P x e)))
  end.

Definition print_goal : tactic := with_goal M.print_goal.

(** [n_etas n f] takes a function f with type [forall x1, ..., xn, T]
    and returns its eta-expansion: [fun x1, ..., xn=>f x1 .. xn].
    Raises [NotAProduct] if there aren't that many absractions. *)
Definition n_etas (n : nat) {A} (f : A) : M A :=
  (fix loop (n : nat) (d : dyn) : M (type d) :=
    match n with
    | 0 =>
      (* we remove the wrapper of the element in [d] *)
      M.unfold_projection (elem d)
    | S n' =>
       mmatch d with
       | [? B (T:B->Type) f] @Dyn (forall x:B, T x) f =>
         ty <- M.unfold_projection (type d);
         name <- M.get_binder_name ty;
         M.nu name None (fun x:B =>
           loop n' (Dyn (f x)) >>= M.abs_fun x
         )
       | _ => M.raise NotAProduct
       end
    end) n (Dyn f).

(** [fix_tac f n] is like Coq's [fix] tactic: it generates a fixpoint
    with a new goal as body, containing a variable named [f] with
    the current goal as type. The goal is expected to have at least
    [n] products. *)
Definition fix_tac (f : string) (n : N) : tactic := fun g =>
  gT <- M.goal_type g;
  r <- M.nu f None (fun f : gT =>
    (* We introduce the recursive definition f and create the new
       goal having it. *)
    new_goal <- M.evar gT;
    (* We need to enclose the body with n-abstractions as
     required by the fix operator. *)
    fixp <- n_etas (N.to_nat n) new_goal;
    fixp <- M.abs_fix f fixp n;
    (* fixp is now the fixpoint with the evar as body *)
    (* The new goal is enclosed with the definition of f *)
    new_goal <- M.abs_fun f (Goal new_goal);
    M.ret (fixp, AHyp None new_goal)
  );
  let (f, new_goal) := r in
  exact f g;;
  M.ret [mc:(tt,new_goal)].

Definition progress {A} (t : gtactic A) : gtactic A := fun g =>
  r <- t g;
  match r with
  | [mc:(x,g')] =>
    mmatch g with
    | g' => M.raise NoProgress
    | _ => M.ret [mc:(x,g')]
    end
  | _ => M.ret r
  end.

(** [repeat t] applies tactic [t] to the goal several times
    (it should only generate at most 1 subgoal), until no
    changes or no goal is left. *)
Definition repeat (t : tactic) : tactic :=
  fix0 _ (fun rec g =>
    r <- try t g; (* if it fails, the execution will stop below *)
    match r with
    | [mc:(_,g')] =>
      mmatch g with
      | g' => M.ret [mc:(tt,g)] (* the goal is the same, return *)
      | _ => rec g'
      end
    | _ => M.ret r
    end).

Definition map_term (f : forall d:dyn, M d.(type)) : forall d : dyn, M d.(type) :=
  mfix1 rec (d : dyn) : M d.(type) :=
    let (ty, el) := d in
    mmatch d as d return M d.(type) with
    | [? B A (b: B) (a: B -> A)] Dyn (a b) =n>
      d1 <- rec (Dyn a);
      d2 <- rec (Dyn b);
      M.ret (d1 d2)
    | [? B (A: B -> Type) (a: forall x, A x)] Dyn (fun x:B=>a x) =n>
      n <- M.get_binder_name el;
      M.nu n None (fun x : B =>
        d1 <- rec (Dyn (a x));
        M.abs_fun x d1)
    | [? B (A: B -> Type) a] Dyn (forall x:B, a x) =n>
      n <- M.get_binder_name el;
      M.nu n None (fun x : B =>
        d1 <- rec (Dyn (a x));
        M.abs_prod x d1)
    | [? d'] d' =n> f d'
    end.

Definition unfold_slow {A} (x : A) : tactic := fun g =>
  let def := rone_step x in
  gT <- M.goal_type g;
  gT' <- map_term (fun d =>
    let (ty, el) := d in
    mmatch d as d return M d.(type) with
    | Dyn x =n> M.ret def
    | [? A (d': A)] Dyn d' =n> M.ret d'
    end) (Dyn gT);
  e <- M.evar gT';
  exact e g;;
  M.ret [mc:(tt,Goal e)].

Definition unfold {A} (x : A) : tactic := fun g =>
  gT <- M.goal_type g;
  let gT' := dreduce (x) gT in
  ng <- M.evar gT';
  exact ng g;;
  M.ret [mc:(tt, Goal ng)].

Definition unfold_in {A B} (x : A) (h : B) : tactic :=
  reduce_in (RedStrong [rl:RedBeta; RedMatch; RedFix; RedDeltaOnly [rl:Dyn x]]) h.

Fixpoint intros_simpl (l : list string) : tactic :=
  match l with
  | [mc:] => idtac
  | n :: l => bind (intro_simpl n) (fun _ => intros_simpl l)
  end.

Fixpoint name_pattern (l : list (list string)) : list tactic :=
  match l with
  | [mc:] => [mc:]
  | ns :: l => intros_simpl ns :: name_pattern l
  end.

(** Type for goal manipulation primitives *)
Definition selector A := list (A * goal) -> M (list (A * goal)).

Instance tactic_selector A : Seq A A (selector A) := fun t s g =>
  l <- t g;
  filter_goals l >>= s.

Module S.
  Definition nth {A} (n : nat) (t : gtactic A) : selector A := fun l =>
    let (l1, l2) := dreduce (@nsplit) (nsplit n l) in
    match hd_error l2 with
    | None => M.raise NoGoalsLeft
    | Some (_, g) =>
      goals <- open_and_apply t g;
      let res := dreduce (app, tl) (l1 ++ goals ++ tl l2)%list in
      M.ret res
    end.

  Definition last {A} (t : gtactic A) : selector A := fun l =>
    let n := dreduce (pred, MList.length) (pred (MList.length l)) in
    nth n t l.

  Definition first {A} (t : gtactic A) : selector A := nth 0 t.

  Definition rev {A} : selector A := fun l =>
    let res := dreduce (rev', rev_append, app) (rev' l) in M.ret res.
End S.

Module notations.
  Open Scope tactic_scope.

  (* This notation makes sure that [t] is in [MC] scope ands casts the resulting
  lambda into a [tactic] to make sure that it can be ran. *)
  Notation "\tactic g => t" :=
    ((fun g => t%MC) : tactic) (at level 200, g at level 0, right associativity).

  Notation "r '<-' t1 ';' t2" := (bind t1 (fun r => t2%tactic))
    (at level 81, right associativity, format "'[' r  '<-'  '[' t1 ;  ']' ']' '/' t2 ") : tactic_scope.
  Notation "t >>= f" := (bind t f) (at level 70) : tactic_scope.

  Notation "t1 ';;' t2" := (seq t1 t2)
    (at level 81, right associativity, format "'[' '[' t1 ;;  ']' ']' '/' t2 ") : tactic_scope.

  Notation "'mif' b 'then' t 'else' u" :=
    (cond <- b; if cond then t else u) (at level 200) : tactic_scope.

  Notation "'mfix0' f : 'gtactic' T := b" :=
    (fix0 T%type (fun f => b%tactic))
    (at level 85, f at level 0, format
    "'[v  ' 'mfix0'  f  ':'  'gtactic'  T  ':=' '/  ' b ']'") : tactic_scope.

  Notation "'mfix1' f ( x : A ) : 'gtactic' T := b" :=
    (fix1 (fun x=>T%type) (fun f (x : A)=>b%tactic))
    (at level 85, f at level 0, x at next level, format
    "'[v  ' 'mfix1'  f  '(' x  ':'  A ')'  ':'  'gtactic'  T  ':=' '/  ' b ']'") : tactic_scope.

  Notation "'mfix2' f ( x : A ) ( y : B ) : 'gtactic' T := b" :=
    (fix2 (fun (x : A) (y : B)=>T%type) (fun f (x : A) (y : B)=>b%tactic))
    (at level 85, f at level 0, x at next level, y at next level, format
    "'[v  ' 'mfix2'  f  '(' x  ':'  A ')'  '(' y  ':'  B ')'  ':'  'gtactic'  T  ':=' '/  ' b ']'") : tactic_scope.

  Notation "'mfix3' f ( x : A ) ( y : B ) ( z : C ) : 'gtactic' T := b" :=
    (fix3 (fun (x : A) (y : B) (z : C)=>T%type) (fun f (x : A) (y : B) (z : C)=>b%tactic))
    (at level 85, f at level 0, x at next level, y at next level, z at next level, format
    "'[v  ' 'mfix3'  f  '(' x  ':'  A ')'  '(' y  ':'  B ')'  '(' z  ':'  C ')'  ':'  'gtactic'  T  ':=' '/  ' b ']'") : tactic_scope.

  Notation "'mfix4' f ( x1 : A1 ) ( x2 : A2 ) ( x3 : A3 ) ( x4 : A4 ) : 'gtactic' T := b" :=
    (fix4 (fun (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4)=>T%type) (fun f (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4) =>b%tactic))
    (at level 85, f at level 0, x1 at next level, x2 at next level, x3 at next level, x4 at next level, format
    "'[v  ' 'mfix4'  f  '(' x1  ':'  A1 ')'  '(' x2  ':'  A2 ')'  '(' x3  ':'  A3 ')'  '(' x4  ':'  A4 ')'  ':'  'gtactic'  T  ':=' '/  ' b ']'") : tactic_scope.

  Notation "'mmatch' x ls" :=
    (@mmatch' _ (fun _ => _) x ls%with_pattern)
    (at level 90, ls at level 91) : tactic_scope.
  Notation "'mmatch' x 'return' 'gtactic' p ls" :=
    (@mmatch' _ (fun x => p%type) x ls%with_pattern)
    (at level 90, ls at level 91) : tactic_scope.
  Notation "'mmatch' x 'as' y 'return' 'gtactic' p ls" :=
    (@mmatch' _ (fun y => p%type) x ls%with_pattern)
    (at level 90, ls at level 91) : tactic_scope.

  Notation "'mtry' a ls" :=
    (mtry' a (fun e =>
      (@mmatch' _ (fun _ => _) e
                   (app ls%with_pattern [mc:([? x] x => raise x)%pattern]))))
      (at level 82, a at level 100, ls at level 91, only parsing) : tactic_scope.

  Notation "t 'or' u" := (or t u) (at level 50) : tactic_scope.

  (* We need a fresh evar to be able to use intro with ;; *)
  Notation "'intro' x" :=
    (T <- M.evar Type; @intro_cont T _ (fun x=>idtac))
    (at level 40) : tactic_scope.
  Notation "'intros' x .. y" :=
    (intro_cont (fun x=>.. (intro_cont (fun y=>idtac)) ..))
    (at level 0, x binder, y binder, right associativity) : tactic_scope.
  Notation "'intros'" := intros_all : tactic_scope.

  Notation "'cintro' x '{-' t '-}'" :=
    (intro_cont (fun x=>t)) (at level 0, right associativity) : tactic_scope.
  Notation "'cintros' x .. y '{-' t '-}'" :=
    (intro_cont (fun x=>.. (intro_cont (fun y=>t)) ..))
    (at level 0, x binder, y binder, t at next level, right associativity) : tactic_scope.

  Notation "'simpl'" := (treduce RedSimpl) : tactic_scope.
  Notation "'hnf'" := (treduce RedHNF) : tactic_scope.
  Notation "'cbv'" := (treduce RedNF) : tactic_scope.

  Notation "'pose' ( x := t )" :=
    (cpose t (fun x=>idtac)) (at level 40, x at next level) : tactic_scope.
  Notation "'assert' ( x : T )" :=
    (cassert (fun x:T=>idtac)) (at level 40, x at next level) : tactic_scope.

  Notation "t 'asp' n" :=
    (seq_list t (name_pattern n)) (at level 40) : tactic_scope.

  Notation "[[ |- ps ] ] => t" :=
    (gbase ps t)
    (at level 202, ps at next level) : match_goal_pattern_scope.
  Notation "[[? a .. b | x .. y |- ps ] ] => t" :=
    (gtele_evar (fun a => .. (gtele_evar (fun b =>
       gtele (fun x => .. (gtele (fun y => gbase ps t)).. ))).. ))
    (at level 202, a binder, b binder,
     x binder, y binder, ps at next level) : match_goal_pattern_scope.
  Notation "[[? a .. b |- ps ] ] => t" :=
    (gtele_evar (fun a => .. (gtele_evar (fun b => gbase ps t)).. ))
    (at level 202, a binder, b binder, ps at next level) : match_goal_pattern_scope.
  Notation "[[ x .. y |- ps ] ] => t" :=
    (gtele (fun x => .. (gtele (fun y => gbase ps t)).. ))
    (at level 202, x binder, y binder, ps at next level) : match_goal_pattern_scope.

  Notation "[[ |- 'context' C [ ps ] ] ] => t" :=
    (gbase_context ps (fun C => t))
    (at level 202, C at level 0, ps at next level) : match_goal_pattern_scope.
  Notation "[[? a .. b | x .. y |- 'context' C [ ps ] ] ] => t" :=
    (gtele_evar (fun a => .. (gtele_evar (fun b =>
       gtele (fun x=> .. (gtele (fun y => gbase_context ps (fun C => t))).. ))).. ))
    (at level 202, a binder, b binder,
     x binder, y binder, C at level 0, ps at next level) : match_goal_pattern_scope.
  Notation "[[? a .. b |- 'context' C [ ps ] ] ] => t" :=
    (gtele_evar (fun a => .. (gtele_evar (fun b => gbase_context ps (fun C => t))).. ))
    (at level 202, a binder, b binder, C at level 0, ps at next level) : match_goal_pattern_scope.
  Notation "[[ x .. y |- 'context' C [ ps ] ] ] => t" :=
    (gtele (fun x=> .. (gtele (fun y => gbase_context ps (fun C => t))).. ))
    (at level 202, x binder, y binder, C at level 0, ps at next level) : match_goal_pattern_scope.

  Delimit Scope match_goal_pattern_scope with match_goal_pattern.

  Notation "'with' | p1 | .. | pn 'end'" :=
    ((@cons (goal_pattern _) p1%match_goal_pattern (.. (@cons (goal_pattern _) pn%match_goal_pattern nil) ..)))
      (at level 91, p1 at level 210, pn at level 210) : match_goal_with_scope.
  Notation "'with' p1 | .. | pn 'end'" :=
    ((@cons (goal_pattern _) p1%match_goal_pattern (.. (@cons (goal_pattern _) pn%match_goal_pattern nil) ..)))
      (at level 91, p1 at level 210, pn at level 210) : match_goal_with_scope.

  Delimit Scope match_goal_with_scope with match_goal_with.

  Notation "'match_goal' ls" := (match_goal_base UniCoq ls%match_goal_with)
    (at level 90, ls at level 91) : tactic_scope.
  Notation "'match_goal_nored' ls" := (match_goal_base UniMatchNoRed ls%match_goal_with)
    (at level 90, ls at level 91) : tactic_scope.

  (* Note that unlike the monadic ;; notation, this one is left associative.
  This is needed so that we can nest tactics accordingly, for example:

    split &> idtac &> [idtac; idtac] &> [idtac; idtac]

  *)
  Notation "t1 '&>' ts" :=
    (seq t1 ts) (at level 41, left associativity) : tactic_scope.

  Notation "t1 '|1>' t2" :=
    (t1 &> S.nth 0 t2)
    (at level 41, left associativity, t2 at level 100) : tactic_scope.
  Notation "t1 '|2>' t2" :=
    (t1 &> S.nth 1 t2)
    (at level 41, left associativity, t2 at level 100) : tactic_scope.
  Notation "t1 '|3>' t2" :=
    (t1 &> S.nth 2 t2)
    (at level 41, left associativity, t2 at level 100) : tactic_scope.
  Notation "t1 '|4>' t2" :=
    (t1 &> S.nth 3 t2)
    (at level 41, left associativity, t2 at level 100) : tactic_scope.
  Notation "t1 '|5>' t2" :=
    (t1 &> S.nth 4 t2)
    (at level 41, left associativity, t2 at level 100) : tactic_scope.
  Notation "t1 '|6>' t2" :=
    (t1 &> S.nth 5 t2)
    (at level 41, left associativity, t2 at level 100) : tactic_scope.

  Notation "t1 'l>' t2" :=
    (t1 &> S.last t2)
    (at level 41, left associativity, t2 at level 100) : tactic_scope.
End notations.

Import notations.

(* Some derived tactics *)
Definition apply_in {P Q} (c : P -> Q) (H : P) : tactic :=
  change_hyp H (c H).

Definition transitivity {B} (y : B) : tactic :=
  apply (fun x => @Coq.Init.Logic.eq_trans B x y).

Definition symmetry : tactic :=
  apply Coq.Init.Logic.eq_sym.

Definition exfalso : tactic :=
  apply Coq.Init.Logic.False_ind.

Definition constructor (n : nat) : tactic :=
  A <- goal_type;
  match n with
  | 0 => M.raise ConstructorsStartsFrom1
  | S n =>
    l <- M.constrs A;
    match nth_error (snd l) n with
    | Some (@Dyn A x) => apply x
    | None => raise CantFindConstructor
    end
  end.

Definition split : tactic :=
  A <- goal_type;
  l <- M.constrs A;
  match snd l with
  | [mc:_] => constructor 1
  | _ => raise Not1Constructor
  end.

Definition left : tactic :=
  A <- goal_type;
  l <- M.constrs A;
  match snd l with
  | [mc:Dyn x; _] => apply x
  | _ => raise Not2Constructor
  end.

Definition right : tactic :=
  A <- goal_type;
  l <- M.constrs A;
  match snd l with
  | [mc:_; Dyn x] => apply x
  | _ => raise Not2Constructor
  end.

Definition assumption : tactic :=
  A <- goal_type;
  match_goal with [[ x : A |- A ]] => exact x end.

(** Given a type [T] it searches for a hypothesis with that type and
    executes the [cont]inuation on it.  *)
Definition select (T : Type) (cont : T -> tactic) : tactic :=
  A <- goal_type;
  match_goal with [[ x : T |- A ]] => cont x end.

(** generalize with clear *)
Definition move_back {A} (x : A) (cont : tactic) : tactic :=
  generalize x ;; cclear x cont.
End T.

Coercion T.of_M : M >-> gtactic.
