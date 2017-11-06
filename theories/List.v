(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Setoid.
Require Import PeanoNat Le Gt Minus Bool Lt.
Require Export Mtac2.Datatypes.

Set Implicit Arguments.
(* Set Universe Polymorphism. *)

(******************************************************************)
(** * Basics: definition of polymorphic lists and some operations *)
(******************************************************************)

(** The definition of [list] is now in [mInit/Datatypes],
    as well as the definitions of [mlength] and [mapp] *)

Open Scope mlist_scope.

(** Standard notations for lists.
mIn a special module to avoid conflicts. *)
Module ListNotations.
Notation "[m: ]" := mnil (format "[m: ]") : mlist_scope.
Notation "[m: x ]" := (mcons x mnil) : mlist_scope.
Notation "[m: x | y | .. | z ]" :=
  (mcons x (mcons y .. (mcons z mnil) ..))
    (format "'[hv  ' [m:  x '//' |  y  '//' |  .. '//' |  z ']' ]") : mlist_scope.
End ListNotations.

Import ListNotations.

Section Lists.

  Variable A : Type.

  (** Head and tail *)

  Definition mhd (default:A) (l:mlist A) :=
    match l with
      | [m:] => default
      | x :m: _ => x
    end.

  Definition mhd_error (l:mlist A) :=
    match l with
      | [m:] => None
      | x :m: _ => Some x
    end.

  Definition mtl (l:mlist A) :=
    match l with
      | [m:] => mnil
      | a :m: m => m
    end.

  (** The [mIn] predicate *)
  Fixpoint mIn (a:A) (l:mlist A) : Prop :=
    match l with
      | [m:] => False
      | b :m: m => b = a \/ mIn a m
    end.

End Lists.

Section Facts.

  Variable A : Type.


  (** *** Generic facts *)

  (** DiscrimInation *)
  Theorem mnil_mcons : forall (x:A) (l:mlist A), [m:] <> x :m: l.
  Proof.
    intros; discriminate.
  Qed.


  (** Destruction *)

  Theorem destruct_mlist : forall l : mlist A, {x:A & {mtl:mlist A | l = x:m:mtl}}+{l = [m:]}.
  Proof.
    induction l as [|a tail].
    right; reflexivity.
    left; exists a, tail; reflexivity.
  Qed.

  Lemma mhd_error_mtl_repr : forall l (a:A) r,
    mhd_error l = Some a /\ mtl l = r <-> l = a :m: r.
  Proof. destruct l as [|x xs].
    - unfold mhd_error, mtl; intros a r. split; firstorder discriminate.
    - intros. simpl. split. * intros (H1, H2). inversion H1. rewrite H2. reflexivity.
      * inversion 1. subst. auto.
  Qed.

  Lemma mhd_error_some_mnil : forall l (a:A), mhd_error l = Some a -> l <> mnil.
  Proof. unfold mhd_error. destruct l; now discriminate. Qed.

  Theorem mlength_zero_iff_mnil (l : mlist A):
    mlength l = 0 <-> l=[m:].
  Proof.
    split; [now destruct l | now intros ->].
  Qed.

  (** *** Head and tail *)

  Theorem mhd_error_mnil : mhd_error (@mnil A) = None.
  Proof.
    simpl; reflexivity.
  Qed.

  Theorem mhd_error_mcons : forall (l : mlist A) (x : A), mhd_error (x:m:l) = Some x.
  Proof.
    intros; simpl; reflexivity.
  Qed.


  (************************)
  (** *** Facts about [mIn] *)
  (************************)


  (** Characterization of [mIn] *)

  Theorem mIn_eq : forall (a:A) (l:mlist A), mIn a (a :m: l).
  Proof.
    simpl; auto.
  Qed.

  Theorem mIn_mcons : forall (a b:A) (l:mlist A), mIn b l -> mIn b (a :m: l).
  Proof.
    simpl; auto.
  Qed.

  Theorem not_mIn_mcons (x a : A) (l : mlist A):
    ~ mIn x (a:m:l) <-> x<>a /\ ~ mIn x l.
  Proof.
    simpl. intuition.
  Qed.

  Theorem mIn_mnil : forall a:A, ~ mIn a [m:].
  Proof.
    unfold not; intros a H; inversion_clear H.
  Qed.

  Theorem mIn_msplit : forall x (l:mlist A), mIn x l -> exists l1 l2, l = l1+m+x:m:l2.
  Proof.
  induction l; simpl; destruct 1.
  subst a; auto.
  exists [m:], l; auto.
  destruct (IHl H) as (l1,(l2,H0)).
  exists (a:m:l1), l2; simpl. apply f_equal. auto.
  Qed.

  (** mInversion *)
  Lemma mIn_inv : forall (a b:A) (l:mlist A), mIn b (a :m: l) -> a = b \/ mIn b l.
  Proof.
    intros a b l H; inversion_clear H; auto.
  Qed.

  (** Decidability of [mIn] *)
  Theorem mIn_dec :
    (forall x y:A, {x = y} + {x <> y}) ->
    forall (a:A) (l:mlist A), {mIn a l} + {~ mIn a l}.
  Proof.
    intro H; induction l as [| a0 l IHl].
    right; apply mIn_mnil.
    destruct (H a0 a); simpl; auto.
    destruct IHl; simpl; auto.
    right; unfold not; intros [Hc1| Hc2]; auto.
  Defined.


  (**************************)
  (** *** Facts about [mapp] *)
  (**************************)

  (** DiscrimInation *)
  Theorem mapp_mcons_not_mnil : forall (x y:mlist A) (a:A), [m:] <> x +m+ a :m: y.
  Proof.
    unfold not.
    destruct x as [| a l]; simpl; intros.
    discriminate H.
    discriminate H.
  Qed.


  (** Concat with [mnil] *)
  Theorem mapp_mnil_l : forall l:mlist A, [m:] +m+ l = l.
  Proof.
    reflexivity.
  Qed.

  Theorem mapp_mnil_r : forall l:mlist A, l +m+ [m:] = l.
  Proof.
    induction l; simpl; f_equal; auto.
  Qed.

  (* begin hide *)
  (* Deprecated *)
  Theorem mapp_mnil_end : forall (l:mlist A), l = l +m+ [m:].
  Proof. symmetry; apply mapp_mnil_r. Qed.
  (* end hide *)

  (** [mapp] is associative *)
  Theorem mapp_assoc : forall l m n:mlist A, l +m+ m +m+ n = (l +m+ m) +m+ n.
  Proof.
    intros l m n; induction l; simpl; f_equal; auto.
  Qed.

  (* begin hide *)
  (* Deprecated *)
  Theorem mapp_assoc_mreverse : forall l m n:mlist A, (l +m+ m) +m+ n = l +m+ m +m+ n.
  Proof.
     auto using mapp_assoc.
  Qed.
  Hint Resolve mapp_assoc_mreverse.
  (* end hide *)

  (** [mapp] commutes with [mcons] *)
  Theorem mapp_comm_mcons : forall (x y:mlist A) (a:A), a :m: (x +m+ y) = (a :m: x) +m+ y.
  Proof.
    auto.
  Qed.

  (** Facts deduced from the result of a mconcatenation *)

  Theorem mapp_eq_mnil : forall l l':mlist A, l +m+ l' = [m:] -> l = [m:] /\ l' = [m:].
  Proof.
    destruct l as [| x l]; destruct l' as [| y l']; simpl; auto.
    intro; discriminate.
    intros H; discriminate H.
  Qed.

  Theorem mapp_eq_unit :
    forall (x y:mlist A) (a:A),
      x +m+ y = [m:a] -> x = [m:] /\ y = [m:a] \/ x = [m:a] /\ y = [m:].
  Proof.
    destruct x as [| a l]; [ destruct y as [| a l] | destruct y as [| a0 l0] ];
      simpl.
    intros a H; discriminate H.
    left; split; auto.
    right; split; auto.
    generalize H.
    generalize (mapp_mnil_r l); intros E.
    rewrite -> E; auto.
    intros.
    injection H as H H0.
    assert ([m:] = l +m+ a0 :m: l0) by auto.
    apply mapp_mcons_not_mnil in H1 as [].
  Qed.

  Lemma mapp_inj_tail :
    forall (x y:mlist A) (a b:A), x +m+ [m:a] = y +m+ [m:b] -> x = y /\ a = b.
  Proof.
    induction x as [| x l IHl];
      [ destruct y as [| a l] | destruct y as [| a l0] ];
      simpl; auto.
    - intros a b H.
      injection H.
      auto.
    - intros a0 b H.
      injection H as H1 H0.
      apply mapp_mcons_not_mnil in H0 as [].
    - intros a b H.
      injection H as H1 H0.
      assert ([m:] = l +m+ [m:a]) by auto.
      apply mapp_mcons_not_mnil in H as [].
    - intros a0 b H.
      injection H as <- H0.
      destruct (IHl l0 a0 b H0) as (<-,<-).
      split; auto.
  Qed.


  (** Compatibility with other operations *)

  Lemma mapp_mlength : forall l l' : mlist A, mlength (l+m+l') = mlength l + mlength l'.
  Proof.
    induction l; simpl; auto.
  Qed.

  Lemma mIn_mapp_or : forall (l m:mlist A) (a:A), mIn a (l +m+ m) -> mIn a l \/ mIn a m.
  Proof.
    intros l m a.
    elim l; simpl; auto.
    intros a0 y H H0.
    now_show ((a0 = a \/ mIn a y) \/ mIn a m).
    elim H0; auto.
    intro H1.
    now_show ((a0 = a \/ mIn a y) \/ mIn a m).
    elim (H H1); auto.
  Qed.

  Lemma mIn_or_mapp : forall (l m:mlist A) (a:A), mIn a l \/ mIn a m -> mIn a (l +m+ m).
  Proof.
    intros l m a.
    elim l; simpl; intro H.
    now_show (mIn a m).
    elim H; auto; intro H0.
    now_show (mIn a m).
    elim H0. (* subProof completed *)
    intros y H0 H1.
    now_show (H = a \/ mIn a (y +m+ m)).
    elim H1; auto 4.
    intro H2.
    now_show (H = a \/ mIn a (y +m+ m)).
    elim H2; auto.
  Qed.

  Lemma mIn_mapp_iff : forall l l' (a:A), mIn a (l+m+l') <-> mIn a l \/ mIn a l'.
  Proof.
    split; auto using mIn_mapp_or, mIn_or_mapp.
  Qed.

  Lemma mapp_inv_head:
   forall l l1 l2 : mlist A, l +m+ l1 = l +m+ l2 -> l1 = l2.
  Proof.
    induction l; simpl; auto; injection 1; auto.
  Qed.

  Lemma mapp_inv_tail:
    forall l l1 l2 : mlist A, l1 +m+ l = l2 +m+ l -> l1 = l2.
  Proof.
    intros l l1 l2; revert l1 l2 l.
    induction l1 as [ | x1 l1]; destruct l2 as [ | x2 l2];
     simpl; auto; intros l H.
    absurd (mlength (x2 :m: l2 +m+ l) <= mlength l).
    simpl; rewrite mapp_mlength; auto with arith.
    rewrite <- H; auto with arith.
    absurd (mlength (x1 :m: l1 +m+ l) <= mlength l).
    simpl; rewrite mapp_mlength; auto with arith.
    rewrite H; auto with arith.
    injection H as H H0; f_equal; eauto.
  Qed.

End Facts.

Hint Resolve mapp_assoc mapp_assoc_mreverse: datatypes.
Hint Resolve mapp_comm_mcons mapp_mcons_not_mnil: datatypes.
Hint Immediate mapp_eq_mnil: datatypes.
Hint Resolve mapp_eq_unit mapp_inj_tail: datatypes.
Hint Resolve mIn_eq mIn_mcons mIn_inv mIn_mnil mIn_mapp_or mIn_or_mapp: datatypes.



(*******************************************)
(** * Operations on the elements of a mlist *)
(*******************************************)

Section Elts.

  Variable A : Type.

  (*****************************)
  (** ** Nth element of a mlist *)
  (*****************************)

  Fixpoint mnth (n:nat) (l:mlist A) (default:A) {struct l} : A :=
    match n, l with
      | O, x :m: l' => x
      | O, other => default
      | S m, [m:] => default
      | S m, x :m: t => mnth m t default
    end.

  Fixpoint mnth_ok (n:nat) (l:mlist A) (default:A) {struct l} : bool :=
    match n, l with
      | O, x :m: l' => true
      | O, other => false
      | S m, [m:] => false
      | S m, x :m: t => mnth_ok m t default
    end.

  Lemma mnth_mIn_or_default :
    forall (n:nat) (l:mlist A) (d:A), {mIn (mnth n l d) l} + {mnth n l d = d}.
  Proof.
    intros n l d; revert n; induction l.
    - right; destruct n; trivial.
    - intros [|n]; simpl.
      * left; auto.
      * destruct (IHl n); auto.
  Qed.

  Lemma mnth_S_mcons :
    forall (n:nat) (l:mlist A) (d a:A),
      mIn (mnth n l d) l -> mIn (mnth (S n) (a :m: l) d) (a :m: l).
  Proof.
    simpl; auto.
  Qed.

  Fixpoint mnth_error (l:mlist A) (n:nat) {struct n} : option A :=
    match n, l with
      | O, x :m: _ => Some x
      | S n, _ :m: l => mnth_error l n
      | _, _ => None
    end.

  Definition mnth_default (default:A) (l:mlist A) (n:nat) : A :=
    match mnth_error l n with
      | Some x => x
      | None => default
    end.

  Lemma mnth_default_eq :
    forall n l (d:A), mnth_default d l n = mnth n l d.
  Proof.
    unfold mnth_default; induction n; intros [ | ] ?; simpl; auto.
  Qed.

  (** Results about [mnth] *)

  Lemma mnth_mIn :
    forall (n:nat) (l:mlist A) (d:A), n < mlength l -> mIn (mnth n l d) l.
  Proof.
    unfold lt; induction n as [| n hn]; simpl.
    - destruct l; simpl; [ inversion 2 | auto ].
    - destruct l; simpl.
      * inversion 2.
      * intros d ie; right; apply hn; auto with arith.
  Qed.

  Lemma mIn_mnth l x d : mIn x l ->
    exists n, n < mlength l /\ mnth n l d = x.
  Proof.
    induction l as [|a l IH].
    - easy.
    - intros [H|H].
      * subst; exists 0; simpl; auto with arith.
      * destruct (IH H) as (n & Hn & Hn').
        exists (S n); simpl; auto with arith.
  Qed.

  Lemma mnth_overflow : forall l n d, mlength l <= n -> mnth n l d = d.
  Proof.
    induction l; destruct n; simpl; intros; auto.
    - inversion H.
    - apply IHl; auto with arith.
  Qed.

  Lemma mnth_indep :
    forall l n d d', n < mlength l -> mnth n l d = mnth n l d'.
  Proof.
    induction l.
    - inversion 1.
    - intros [|n] d d'; simpl; auto with arith.
  Qed.

  Lemma mapp_mnth1 :
    forall l l' d n, n < mlength l -> mnth n (l+m+l') d = mnth n l d.
  Proof.
    induction l.
    - inversion 1.
    - intros l' d [|n]; simpl; auto with arith.
  Qed.

  Lemma mapp_mnth2 :
    forall l l' d n, n >= mlength l -> mnth n (l+m+l') d = mnth (n-mlength l) l' d.
  Proof.
    induction l; intros l' d [|n]; auto.
    - inversion 1.
    - intros; simpl; rewrite IHl; auto with arith.
  Qed.

  Lemma mnth_msplit n l d : n < mlength l ->
    exists l1, exists l2, l = l1 +m+ mnth n l d :m: l2 /\ mlength l1 = n.
  Proof.
    revert l.
    induction n as [|n IH]; intros [|a l] H; try easy.
    - exists mnil; exists l; now simpl.
    - destruct (IH l) as (l1 & l2 & Hl & Hl1); auto with arith.
      exists (a:m:l1); exists l2; simpl; split; now f_equal.
  Qed.

  (** Results about [mnth_error] *)

  Lemma mnth_error_mIn l n x : mnth_error l n = Some x -> mIn x l.
  Proof.
    revert n. induction l as [|a l IH]; intros [|n]; simpl; try easy.
    - injection 1; auto.
    - eauto.
  Qed.

  Lemma mIn_mnth_error l x : mIn x l -> exists n, mnth_error l n = Some x.
  Proof.
    induction l as [|a l IH].
    - easy.
    - intros [H|H].
      * subst; exists 0; simpl; auto with arith.
      * destruct (IH H) as (n,Hn).
        exists (S n); simpl; auto with arith.
  Qed.

  Lemma mnth_error_None l n : mnth_error l n = None <-> mlength l <= n.
  Proof.
    revert n. induction l; destruct n; simpl.
    - split; auto.
    - split; auto with arith.
    - split; now auto with arith.
    - rewrite IHl; split; auto with arith.
  Qed.

  Lemma mnth_error_Some l n : mnth_error l n <> None <-> n < mlength l.
  Proof.
   revert n. induction l; destruct n; simpl.
    - split; [now destruct 1 | inversion 1].
    - split; [now destruct 1 | inversion 1].
    - split; now auto with arith.
    - rewrite IHl; split; auto with arith.
  Qed.

  Lemma mnth_error_msplit l n a : mnth_error l n = Some a ->
    exists l1, exists l2, l = l1 +m+ a :m: l2 /\ mlength l1 = n.
  Proof.
    revert l.
    induction n as [|n IH]; intros [|x l] H; simpl in *; try easy.
    - exists mnil; exists l. now injection H as ->.
    - destruct (IH _ H) as (l1 & l2 & H1 & H2).
      exists (x:m:l1); exists l2; simpl; split; now f_equal.
  Qed.

  Lemma mnth_error_mapp1 l l' n : n < mlength l ->
    mnth_error (l+m+l') n = mnth_error l n.
  Proof.
    revert l.
    induction n; intros [|a l] H; auto; try solve [inversion H].
    simpl in *. apply IHn. auto with arith.
  Qed.

  Lemma mnth_error_mapp2 l l' n : mlength l <= n ->
    mnth_error (l+m+l') n = mnth_error l' (n-mlength l).
  Proof.
    revert l.
    induction n; intros [|a l] H; auto; try solve [inversion H].
    simpl in *. apply IHn. auto with arith.
  Qed.

  (*****************)
  (** ** Remove    *)
  (*****************)

  Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

  Fixpoint mremove (x : A) (l : mlist A) : mlist A :=
    match l with
      | [m:] => [m:]
      | y:m:mtl => if (eq_dec x y) then mremove x mtl else y:m:(mremove x mtl)
    end.

  Theorem mremove_mIn : forall (l : mlist A) (x : A), ~ mIn x (mremove x l).
  Proof.
    induction l as [|x l]; auto.
    intro y; simpl; destruct (eq_dec y x) as [yeqx | yneqx].
    apply IHl.
    unfold not; intro HF; simpl in HF; destruct HF; auto.
    apply (IHl y); assumption.
  Qed.


(******************************)
(** ** Last element of a mlist *)
(******************************)

  (** [mlast l d] returns the mlast element of the mlist [l],
    or the default value [d] if [l] is empty. *)

  Fixpoint mlast (l:mlist A) (d:A) : A :=
  match l with
    | [m:] => d
    | [m:a] => a
    | a :m: l => mlast l d
  end.

  (** [mremovemlast l] mremove the mlast element of [l] *)

  Fixpoint mremovemlast (l:mlist A) : mlist A :=
    match l with
      | [m:] =>  [m:]
      | [m:a] => [m:]
      | a :m: l => a :m: mremovemlast l
    end.

  Lemma mapp_mremovemlast_mlast :
    forall l d, l <> [m:] -> l = mremovemlast l +m+ [m:mlast l d].
  Proof.
    induction l.
    destruct 1; auto.
    intros d _.
    destruct l; auto.
    pattern (a0:m:l) at 1; rewrite IHl with d; auto; discriminate.
  Qed.

  Lemma exists_mlast :
    forall l, l <> [m:] -> { l' : (mlist A) & { a : A | l = l' +m+ [m:a]}}.
  Proof.
    induction l.
    destruct 1; auto.
    intros _.
    destruct l.
    exists [m:], a; auto.
    destruct IHl as [l' (a',H)]; try discriminate.
    rewrite H.
    exists (a:m:l'), a'; auto.
  Qed.

  Lemma mremovemlast_mapp :
    forall l l', l' <> [m:] -> mremovemlast (l+m+l') = l +m+ mremovemlast l'.
  Proof.
    induction l.
    simpl; auto.
    simpl; intros.
    assert (l+m+l' <> [m:]).
    destruct l.
    simpl; auto.
    simpl; discriminate.
    specialize (IHl l' H).
    destruct (l+m+l'); [elim H0; auto|f_equal; auto].
  Qed.


  (******************************************)
  (** ** Counting occurrences of an element *)
  (******************************************)

  Fixpoint count_occ (l : mlist A) (x : A) : nat :=
    match l with
      | [m:] => 0
      | y :m: mtl =>
        let n := count_occ mtl x in
        if eq_dec y x then S n else n
    end.

  (** Compatibility of count_occ with operations on mlist *)
  Theorem count_occ_mIn l x : mIn x l <-> count_occ l x > 0.
  Proof.
    induction l as [|y l]; simpl.
    - split; [destruct 1 | apply gt_irrefl].
    - destruct eq_dec as [->|Hneq]; rewrite IHl; intuition.
  Qed.

  Theorem count_occ_not_mIn l x : ~ mIn x l <-> count_occ l x = 0.
  Proof.
    rewrite count_occ_mIn. unfold gt. now rewrite Nat.nlt_ge, Nat.le_0_r.
  Qed.

  Lemma count_occ_mnil x : count_occ [m:] x = 0.
  Proof.
    reflexivity.
  Qed.

  Theorem count_occ_inv_mnil l :
    (forall x:A, count_occ l x = 0) <-> l = [m:].
  Proof.
    split. induction l as [|x l]; trivial.
      intros H. specialize (H x). simpl in H.
      destruct eq_dec as [_|NEQ]; [discriminate|now elim NEQ].
    - now intros ->.
  Qed.

  Lemma count_occ_mcons_eq l x y :
    x = y -> count_occ (x:m:l) y = S (count_occ l y).
  Proof.
    intros H. simpl. now destruct (eq_dec x y).
  Qed.

  Lemma count_occ_mcons_neq l x y :
    x <> y -> count_occ (x:m:l) y = count_occ l y.
  Proof.
    intros H. simpl. now destruct (eq_dec x y).
  Qed.

End Elts.

(*******************************)
(** * Manipulating whole mlists *)
(*******************************)

Section ListOps.

  Variable A : Type.

  (*************************)
  (** ** Reverse           *)
  (*************************)

  Fixpoint mrev (l:mlist A) : mlist A :=
    match l with
      | [m:] => [m:]
      | x :m: l' => mrev l' +m+ [m:x]
    end.

  Lemma mrev_mapp_distr : forall x y:mlist A, mrev (x +m+ y) = mrev y +m+ mrev x.
  Proof.
    induction x as [| a l IHl].
    destruct y as [| a l].
    simpl.
    auto.

    simpl.
    rewrite mapp_mnil_r; auto.

    intro y.
    simpl.
    rewrite (IHl y).
    rewrite mapp_assoc; trivial.
  Qed.

  Remark mrev_unit : forall (l:mlist A) (a:A), mrev (l +m+ [m:a]) = a :m: mrev l.
  Proof.
    intros.
    apply (mrev_mapp_distr l [m:a]); simpl; auto.
  Qed.

  Lemma mrev_involutive : forall l:mlist A, mrev (mrev l) = l.
  Proof.
    induction l as [| a l IHl].
    simpl; auto.

    simpl.
    rewrite (mrev_unit (mrev l) a).
    rewrite IHl; auto.
  Qed.


  (** Compatibility with other operations *)

  Lemma mIn_mrev : forall l x, mIn x l <-> mIn x (mrev l).
  Proof.
    induction l.
    simpl; intuition.
    intros.
    simpl.
    intuition.
    subst.
    apply mIn_or_mapp; right; simpl; auto.
    apply mIn_or_mapp; left; firstorder.
    destruct (mIn_mapp_or _ _ _ H); firstorder.
  Qed.

  Lemma mrev_mlength : forall l, mlength (mrev l) = mlength l.
  Proof.
    induction l;simpl; auto.
    rewrite mapp_mlength.
    rewrite IHl.
    simpl.
    elim (mlength l); simpl; auto.
  Qed.

  Lemma mrev_mnth : forall l d n,  n < mlength l ->
    mnth n (mrev l) d = mnth (mlength l - S n) l d.
  Proof.
    induction l.
    intros; inversion H.
    intros.
    simpl in H.
    simpl (mrev (a :m: l)).
    simpl (mlength (a :m: l) - S n).
    inversion H.
    rewrite <- minus_n_n; simpl.
    rewrite <- mrev_mlength.
    rewrite mapp_mnth2; auto.
    rewrite <- minus_n_n; auto.
    rewrite mapp_mnth1; auto.
    rewrite (minus_plus_simpl_l_reverse (mlength l) n 1).
    replace (1 + mlength l) with (S (mlength l)); auto with arith.
    rewrite <- minus_Sn_m; auto with arith.
    apply IHl ; auto with arith.
    rewrite mrev_mlength; auto.
  Qed.


  (**  An alternative tail-recursive definition for mreverse *)

  Fixpoint mrev_append (l l': mlist A) : mlist A :=
    match l with
      | [m:] => l'
      | a:m:l => mrev_append l (a:m:l')
    end.

  Definition mrev' l : mlist A := mrev_append l [m:].

  Lemma mrev_append_mrev : forall l l', mrev_append l l' = mrev l +m+ l'.
  Proof.
    induction l; simpl; auto; intros.
    rewrite <- mapp_assoc; firstorder.
  Qed.

  Lemma mrev_alt : forall l, mrev l = mrev_append l [m:].
  Proof.
    intros; rewrite mrev_append_mrev.
    rewrite mapp_mnil_r; trivial.
  Qed.


(*********************************************)
(** Reverse mInduction Principle on Lists  *)
(*********************************************)

  Section Reverse_mInduction.

    Lemma mrev_mlist_ind :
      forall P:mlist A-> Prop,
	P [m:] ->
	(forall (a:A) (l:mlist A), P (mrev l) -> P (mrev (a :m: l))) ->
	forall l:mlist A, P (mrev l).
    Proof.
      induction l; auto.
    Qed.

    Theorem mrev_ind :
      forall P:mlist A -> Prop,
	P [m:] ->
	(forall (x:A) (l:mlist A), P l -> P (l +m+ [m:x])) -> forall l:mlist A, P l.
    Proof.
      intros.
      generalize (mrev_involutive l).
      intros E; rewrite <- E.
      apply (mrev_mlist_ind P).
      auto.

      simpl.
      intros.
      apply (H0 a (mrev l0)).
      auto.
    Qed.

  End Reverse_mInduction.

  (*************************)
  (** ** Concatenation     *)
  (*************************)

  Fixpoint mconcat (l : mlist (mlist A)) : mlist A :=
  match l with
  | mnil => mnil
  | mcons x l => x +m+ mconcat l
  end.

  Lemma mconcat_mnil : mconcat mnil = mnil.
  Proof.
  reflexivity.
  Qed.

  Lemma mconcat_mcons : forall x l, mconcat (mcons x l) = x +m+ mconcat l.
  Proof.
  reflexivity.
  Qed.

  Lemma mconcat_mapp : forall l1 l2, mconcat (l1 +m+ l2) = mconcat l1 +m+ mconcat l2.
  Proof.
  intros l1; induction l1 as [|x l1 IH]; intros l2; simpl.
  + reflexivity.
  + rewrite IH; apply mapp_assoc.
  Qed.

  (***********************************)
  (** ** Decidable equality on mlists *)
  (***********************************)

  Hypothesis eq_dec : forall (x y : A), {x = y}+{x <> y}.

  Lemma mlist_eq_dec : forall l l':mlist A, {l = l'} + {l <> l'}.
  Proof. decide equality. Defined.

End ListOps.

(***************************************************)
(** * Applying functions to the elements of a mlist *)
(***************************************************)

(************)
(** ** Map  *)
(************)

Section Map.
  Variables (A : Type) (B : Type).
  Variable f : A -> B.

  Fixpoint mmap (l:mlist A) : mlist B :=
    match l with
      | [m:] => [m:]
      | a :m: t => (f a) :m: (mmap t)
    end.

  Lemma mmap_mcons (x:A)(l:mlist A) : mmap (x:m:l) = (f x) :m: (mmap l).
  Proof.
    reflexivity.
  Qed.

  Lemma mIn_mmap :
    forall (l:mlist A) (x:A), mIn x l -> mIn (f x) (mmap l).
  Proof.
    induction l; firstorder (subst; auto).
  Qed.

  Lemma mIn_mmap_iff : forall l y, mIn y (mmap l) <-> exists x, f x = y /\ mIn x l.
  Proof.
    induction l; firstorder (subst; auto).
  Qed.

  Lemma mmap_mlength : forall l, mlength (mmap l) = mlength l.
  Proof.
    induction l; simpl; auto.
  Qed.

  Lemma mmap_mnth : forall l d n,
    mnth n (mmap l) (f d) = f (mnth n l d).
  Proof.
    induction l; simpl mmap; destruct n; firstorder.
  Qed.

  Lemma mmap_mnth_error : forall n l d,
    mnth_error l n = Some d -> mnth_error (mmap l) n = Some (f d).
  Proof.
    induction n; intros [ | ] ? Heq; simpl in *; inversion Heq; auto.
  Qed.

  Lemma mmap_mapp : forall l l',
    mmap (l+m+l') = (mmap l)+m+(mmap l').
  Proof.
    induction l; simpl; auto.
    intros; rewrite IHl; auto.
  Qed.

  Lemma mmap_mrev : forall l, mmap (mrev l) = mrev (mmap l).
  Proof.
    induction l; simpl; auto.
    rewrite mmap_mapp.
    rewrite IHl; auto.
  Qed.

  Lemma mmap_eq_mnil : forall l, mmap l = [m:] -> l = [m:].
  Proof.
    destruct l; simpl; reflexivity || discriminate.
  Qed.

  (** [mmap] and count of occurrences *)

  Hypothesis decA: forall x1 x2 : A, {x1 = x2} + {x1 <> x2}.
  Hypothesis decB: forall y1 y2 : B, {y1 = y2} + {y1 <> y2}.
  Hypothesis Hfinjective: forall x1 x2: A, (f x1) = (f x2) -> x1 = x2.

  Theorem count_occ_mmap x l:
    count_occ decA l x = count_occ decB (mmap l) (f x).
  Proof.
    revert x. induction l as [| a l' Hrec]; intro x; simpl.
    - reflexivity.
    - specialize (Hrec x).
      destruct (decA a x) as [H1|H1], (decB (f a) (f x)) as [H2|H2].
      * rewrite Hrec. reflexivity.
      * contradiction H2. rewrite H1. reflexivity.
      * specialize (Hfinjective H2). contradiction H1.
      * assumption.
  Qed.

  (** [mflat_mmap] *)

  Definition mflat_mmap (f:A -> mlist B) :=
    fix mflat_mmap (l:mlist A) : mlist B :=
    match l with
      | mnil => mnil
      | mcons x t => (f x)+m+(mflat_mmap t)
    end.

  Lemma mIn_mflat_mmap : forall (f:A->mlist B)(l:mlist A)(y:B),
    mIn y (mflat_mmap f l) <-> exists x, mIn x l /\ mIn y (f x).
  Proof using A B.
    clear Hfinjective.
    induction l; simpl; split; intros.
    contradiction.
    destruct H as (x,(H,_)); contradiction.
    destruct (mIn_mapp_or _ _ _ H).
    exists a; auto.
    destruct (IHl y) as (H1,_); destruct (H1 H0) as (x,(H2,H3)).
    exists x; auto.
    apply mIn_or_mapp.
    destruct H as (x,(H0,H1)); destruct H0.
    subst; auto.
    right; destruct (IHl y) as (_,H2); apply H2.
    exists x; auto.
  Qed.

End Map.

Lemma mflat_mmap_mconcat_mmap : forall A B (f : A -> mlist B) l,
  mflat_mmap f l = mconcat (mmap f l).
Proof.
intros A B f l; induction l as [|x l IH]; simpl.
+ reflexivity.
+ rewrite IH; reflexivity.
Qed.

Lemma mconcat_mmap : forall A B (f : A -> B) l, mmap f (mconcat l) = mconcat (mmap (mmap f) l).
Proof.
intros A B f l; induction l as [|x l IH]; simpl.
+ reflexivity.
+ rewrite mmap_mapp, IH; reflexivity.
Qed.

Lemma mmap_id : forall (A :Type) (l : mlist A),
  mmap (fun x => x) l = l.
Proof.
  induction l; simpl; auto; rewrite IHl; auto.
Qed.

Lemma mmap_mmap : forall (A B C:Type)(f:A->B)(g:B->C) l,
  mmap g (mmap f l) = mmap (fun x => g (f x)) l.
Proof.
  induction l; simpl; auto.
  rewrite IHl; auto.
Qed.

Lemma mmap_ext_in :
  forall (A B : Type)(f g:A->B) l, (forall a, mIn a l -> f a = g a) -> mmap f l = mmap g l.
Proof.
  induction l; simpl; auto.
  intros; rewrite H by intuition; rewrite IHl; auto.
Qed.

Lemma mmap_ext :
  forall (A B : Type)(f g:A->B), (forall a, f a = g a) -> forall l, mmap f l = mmap g l.
Proof.
  intros; apply mmap_ext_in; auto.
Qed.


(************************************)
(** Left-to-right iterator on mlists *)
(************************************)

Section Fold_Left_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : A -> B -> A.

  Fixpoint mfold_left (l:mlist B) (a0:A) : A :=
    match l with
      | mnil => a0
      | mcons b t => mfold_left t (f a0 b)
    end.

  Lemma mfold_left_mapp : forall (l l':mlist B)(i:A),
    mfold_left (l+m+l') i = mfold_left l' (mfold_left l i).
  Proof.
    induction l.
    simpl; auto.
    intros.
    simpl.
    auto.
  Qed.

End Fold_Left_Recursor.

Lemma mfold_left_mlength :
  forall (A:Type)(l:mlist A), mfold_left (fun x _ => S x) l 0 = mlength l.
Proof.
  intros A l.
  enough (H : forall n, mfold_left (fun x _ => S x) l n = n + mlength l) by exact (H 0).
  induction l; simpl; auto.
  intros; rewrite IHl.
  simpl; auto with arith.
Qed.

(************************************)
(** Right-to-left iterator on mlists *)
(************************************)

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

  Lemma mfold_right_mapp : forall (A B:Type)(f:A->B->B) l l' i,
    mfold_right f i (l+m+l') = mfold_right f (mfold_right f i l') l.
  Proof.
    induction l.
    simpl; auto.
    simpl; intros.
    f_equal; auto.
  Qed.

  Lemma mfold_left_mrev_right : forall (A B:Type)(f:A->B->B) l i,
    mfold_right f i (mrev l) = mfold_left (fun x y => f y x) l i.
  Proof.
    induction l.
    simpl; auto.
    intros.
    simpl.
    rewrite mfold_right_mapp; simpl; auto.
  Qed.

  Theorem fold_symmetric :
    forall (A : Type) (f : A -> A -> A),
    (forall x y z : A, f x (f y z) = f (f x y) z) ->
    forall (a0 : A), (forall y : A, f a0 y = f y a0) ->
    forall (l : mlist A), mfold_left f l a0 = mfold_right f a0 l.
  Proof.
    intros A f assoc a0 comma0 l.
    induction l as [ | a1 l ]; [ simpl; reflexivity | ].
    simpl. rewrite <- IHl. clear IHl. revert a1. induction l; [ auto | ].
    simpl. intro. rewrite <- assoc. rewrite IHl. rewrite IHl. auto.
  Qed.

  (** [(mlist_power x y)] is [y^x], or the set of sequences of elts of [y]
      indexed by elts of [x], sorted in lexicographic order. *)

  Fixpoint mlist_power (A B:Type)(l:mlist A) (l':mlist B) :
    mlist (mlist (A * B)) :=
    match l with
      | mnil => mcons mnil mnil
      | mcons x t =>
	mflat_mmap (fun f:mlist (A * B) => mmap (fun y:B => mcons (x, y) f) l')
        (mlist_power t l')
    end.


  (*************************************)
  (** ** Boolean operations over mlists *)
  (*************************************)

  Section Bool.
    Variable A : Type.
    Variable f : A -> bool.

  (** mfind whether a boolean function can be satisfied by an
       elements of the mlist. *)

    Fixpoint mexistsb (l:mlist A) : bool :=
      match l with
	| mnil => false
	| a:m:l => f a || mexistsb l
      end.

    Lemma mexistsb_exists :
      forall l, mexistsb l = true <-> exists x, mIn x l /\ f x = true.
    Proof.
      induction l; simpl; intuition.
      inversion H.
      firstorder.
      destruct (orb_prop _ _ H1); firstorder.
      firstorder.
      subst.
      rewrite H2; auto.
    Qed.

    Lemma mexistsb_mnth : forall l n d, n < mlength l ->
      mexistsb l = false -> f (mnth n l d) = false.
    Proof.
      induction l.
      inversion 1.
      simpl; intros.
      destruct (orb_false_elim _ _ H0); clear H0; auto.
      destruct n ; auto.
      rewrite IHl; auto with arith.
    Qed.

    Lemma mexistsb_mapp : forall l1 l2,
      mexistsb (l1+m+l2) = mexistsb l1 || mexistsb l2.
    Proof.
      induction l1; intros l2; simpl.
        solve[auto].
      case (f a); simpl; solve[auto].
    Qed.

  (** mfind whether a boolean function is satisfied by
    all the elements of a mlist. *)

    Fixpoint mforallb (l:mlist A) : bool :=
      match l with
	| mnil => true
	| a:m:l => f a && mforallb l
      end.

    Lemma mforallb_forall :
      forall l, mforallb l = true <-> (forall x, mIn x l -> f x = true).
    Proof.
      induction l; simpl; intuition.
      destruct (andb_prop _ _ H1).
      congruence.
      destruct (andb_prop _ _ H1); auto.
      assert (mforallb l = true).
      apply H0; intuition.
      rewrite H1; auto.
    Qed.

    Lemma mforallb_mapp :
      forall l1 l2, mforallb (l1+m+l2) = mforallb l1 && mforallb l2.
    Proof.
      induction l1; simpl.
        solve[auto].
      case (f a); simpl; solve[auto].
    Qed.
  (** [mfilter] *)

    Fixpoint mfilter (l:mlist A) : mlist A :=
      match l with
	| mnil => mnil
	| x :m: l => if f x then x:m:(mfilter l) else mfilter l
      end.

    Lemma mfilter_mIn : forall x l, mIn x (mfilter l) <-> mIn x l /\ f x = true.
    Proof.
      induction l; simpl.
      intuition.
      intros.
      case_eq (f a); intros; simpl; intuition congruence.
    Qed.

  (** [mfind] *)

    Fixpoint mfind (l:mlist A) : option A :=
      match l with
	| mnil => None
	| x :m: mtl => if f x then Some x else mfind mtl
      end.

    Lemma mfind_some l x : mfind l = Some x -> mIn x l /\ f x = true.
    Proof.
     induction l as [|a l IH]; simpl; [easy| ].
     case_eq (f a); intros Ha Eq.
     * injection Eq as ->; auto.
     * destruct (IH Eq); auto.
    Qed.

    Lemma mfind_none l : mfind l = None -> forall x, mIn x l -> f x = false.
    Proof.
     induction l as [|a l IH]; simpl; [easy|].
     case_eq (f a); intros Ha Eq x IN; [easy|].
     destruct IN as [<-|IN]; auto.
    Qed.

  (** [mpartition] *)

    Fixpoint mpartition (l:mlist A) : mlist A * mlist A :=
      match l with
	| mnil => (mnil, mnil)
	| x :m: mtl => let (g,d) := mpartition mtl in
	  if f x then (x:m:g,d) else (g,x:m:d)
      end.

  Theorem mpartition_mcons1 a l l1 l2:
    mpartition l = (l1, l2) ->
    f a = true ->
    mpartition (a:m:l) = (a:m:l1, l2).
  Proof.
    simpl. now intros -> ->.
  Qed.

  Theorem mpartition_mcons2 a l l1 l2:
    mpartition l = (l1, l2) ->
    f a=false ->
    mpartition (a:m:l) = (l1, a:m:l2).
  Proof.
    simpl. now intros -> ->.
  Qed.

  Theorem mpartition_mlength l l1 l2:
    mpartition l = (l1, l2) ->
    mlength l = mlength l1 + mlength l2.
  Proof.
    revert l1 l2. induction l as [ | a l' Hrec]; intros l1 l2.
    - now intros [= <- <- ].
    - simpl. destruct (f a), (mpartition l') as (left, right);
      intros [= <- <- ]; simpl; rewrite (Hrec left right); auto.
  Qed.

  Theorem mpartition_inv_mnil (l : mlist A):
    mpartition l = ([m:], [m:]) <-> l = [m:].
  Proof.
    split.
    - destruct l as [|a l'].
      * intuition.
      * simpl. destruct (f a), (mpartition l'); now intros [= -> ->].
    - now intros ->.
  Qed.

  Theorem elements_mIn_mpartition l l1 l2:
    mpartition l = (l1, l2) ->
    forall x:A, mIn x l <-> mIn x l1 \/ mIn x l2.
  Proof.
    revert l1 l2. induction l as [| a l' Hrec]; simpl; intros l1 l2 Eq x.
    - injection Eq as <- <-. tauto.
    - destruct (mpartition l') as (left, right).
      specialize (Hrec left right eq_refl x).
      destruct (f a); injection Eq as <- <-; simpl; tauto.
  Qed.

  End Bool.




  (******************************************************)
  (** ** Operations on mlists of pairs or mlists of mlists *)
  (******************************************************)

  Section ListPairs.
    Variables (A : Type) (B : Type).

  (** [msplit] derives two mlists from a mlist of pairs *)

    Fixpoint msplit (l:mlist (A*B)) : mlist A * mlist B :=
      match l with
	| [m:] => ([m:], [m:])
	| (x,y) :m: mtl => let (left,right) := msplit mtl in (x:m:left, y:m:right)
      end.

    Lemma mIn_msplit_l : forall (l:mlist (A*B))(p:A*B),
      mIn p l -> mIn (fst p) (fst (msplit l)).
    Proof.
      induction l; simpl; intros; auto.
      destruct p; destruct a; destruct (msplit l); simpl in *.
      destruct H.
      injection H; auto.
      right; apply (IHl (a0,b) H).
    Qed.

    Lemma mIn_msplit_r : forall (l:mlist (A*B))(p:A*B),
      mIn p l -> mIn (snd p) (snd (msplit l)).
    Proof.
      induction l; simpl; intros; auto.
      destruct p; destruct a; destruct (msplit l); simpl in *.
      destruct H.
      injection H; auto.
      right; apply (IHl (a0,b) H).
    Qed.

    Lemma msplit_mnth : forall (l:mlist (A*B))(n:nat)(d:A*B),
      mnth n l d = (mnth n (fst (msplit l)) (fst d), mnth n (snd (msplit l)) (snd d)).
    Proof.
      induction l.
      destruct n; destruct d; simpl; auto.
      destruct n; destruct d; simpl; auto.
      destruct a; destruct (msplit l); simpl; auto.
      destruct a; destruct (msplit l); simpl in *; auto.
      apply IHl.
    Qed.

    Lemma msplit_mlength_l : forall (l:mlist (A*B)),
      mlength (fst (msplit l)) = mlength l.
    Proof.
      induction l; simpl; auto.
      destruct a; destruct (msplit l); simpl; auto.
    Qed.

    Lemma msplit_mlength_r : forall (l:mlist (A*B)),
      mlength (snd (msplit l)) = mlength l.
    Proof.
      induction l; simpl; auto.
      destruct a; destruct (msplit l); simpl; auto.
    Qed.

  (** [mcombine] is the opposite of [msplit].
      Lists given to [mcombine] are meant to be of same mlength.
      If not, [mcombine] stops on the shorter mlist *)

    Fixpoint mcombine (l : mlist A) (l' : mlist B) : mlist (A*B) :=
      match l,l' with
	| x:m:mtl, y:m:mtl' => (x,y):m:(mcombine mtl mtl')
	| _, _ => mnil
      end.

    Lemma msplit_mcombine : forall (l: mlist (A*B)),
      let (l1,l2) := msplit l in mcombine l1 l2 = l.
    Proof.
      induction l.
      simpl; auto.
      destruct a; simpl.
      destruct (msplit l); simpl in *.
      f_equal; auto.
    Qed.

    Lemma mcombine_msplit : forall (l:mlist A)(l':mlist B), mlength l = mlength l' ->
      msplit (mcombine l l') = (l,l').
    Proof.
      induction l, l'; simpl; trivial; try discriminate.
      now intros [= ->%IHl].
    Qed.

    Lemma mIn_mcombine_l : forall (l:mlist A)(l':mlist B)(x:A)(y:B),
      mIn (x,y) (mcombine l l') -> mIn x l.
    Proof.
      induction l.
      simpl; auto.
      destruct l'; simpl; auto; intros.
      contradiction.
      destruct H.
      injection H; auto.
      right; apply IHl with l' y; auto.
    Qed.

    Lemma mIn_mcombine_r : forall (l:mlist A)(l':mlist B)(x:A)(y:B),
      mIn (x,y) (mcombine l l') -> mIn y l'.
    Proof.
      induction l.
      simpl; intros; contradiction.
      destruct l'; simpl; auto; intros.
      destruct H.
      injection H; auto.
      right; apply IHl with x; auto.
    Qed.

    Lemma mcombine_mlength : forall (l:mlist A)(l':mlist B),
      mlength (mcombine l l') = min (mlength l) (mlength l').
    Proof.
      induction l.
      simpl; auto.
      destruct l'; simpl; auto.
    Qed.

    Lemma mcombine_mnth : forall (l:mlist A)(l':mlist B)(n:nat)(x:A)(y:B),
      mlength l = mlength l' ->
      mnth n (mcombine l l') (x,y) = (mnth n l x, mnth n l' y).
    Proof.
      induction l; destruct l'; intros; try discriminate.
      destruct n; simpl; auto.
      destruct n; simpl in *; auto.
    Qed.

  (** [mlist_prod] has the same signature as [mcombine], but unlike
     [mcombine], it adds every possible pairs, not only those at the
     same position. *)

    Fixpoint mlist_prod (l:mlist A) (l':mlist B) :
      mlist (A * B) :=
      match l with
	| mnil => mnil
	| mcons x t => (mmap (fun y:B => (x, y)) l')+m+(mlist_prod t l')
      end.

    Lemma mIn_prod_aux :
      forall (x:A) (y:B) (l:mlist B),
	mIn y l -> mIn (x, y) (mmap (fun y0:B => (x, y0)) l).
    Proof.
      induction l;
	[ simpl; auto
	  | simpl; destruct 1 as [H1| ];
	    [ left; rewrite H1; trivial | right; auto ] ].
    Qed.

    Lemma mIn_prod :
      forall (l:mlist A) (l':mlist B) (x:A) (y:B),
	mIn x l -> mIn y l' -> mIn (x, y) (mlist_prod l l').
    Proof.
      induction l;
	[ simpl; tauto
	  | simpl; intros; apply mIn_or_mapp; destruct H;
	    [ left; rewrite H; apply mIn_prod_aux; assumption | right; auto ] ].
    Qed.

    Lemma mIn_prod_iff :
      forall (l:mlist A)(l':mlist B)(x:A)(y:B),
	mIn (x,y) (mlist_prod l l') <-> mIn x l /\ mIn y l'.
    Proof.
      split; [ | intros; apply mIn_prod; intuition ].
      induction l; simpl; intros.
      intuition.
      destruct (mIn_mapp_or _ _ _ H); clear H.
      destruct (mIn_mmap_iff (fun y : B => (a, y)) l' (x,y)) as (H1,_).
      destruct (H1 H0) as (z,(H2,H3)); clear H0 H1.
      injection H2 as -> ->; intuition.
      intuition.
    Qed.

    Lemma prod_mlength : forall (l:mlist A)(l':mlist B),
      mlength (mlist_prod l l') = (mlength l) * (mlength l').
    Proof.
      induction l; simpl; auto.
      intros.
      rewrite mapp_mlength.
      rewrite mmap_mlength.
      auto.
    Qed.

  End ListPairs.




(*****************************************)
(** * Miscellaneous operations on mlists  *)
(*****************************************)



(******************************)
(** ** Length order of mlists  *)
(******************************)

Section mlength_order.
  Variable A : Type.

  Definition mlel (l m:mlist A) := mlength l <= mlength m.

  Variables a b : A.
  Variables l m n : mlist A.

  Lemma mlel_refl : mlel l l.
  Proof.
    unfold mlel; auto with arith.
  Qed.

  Lemma mlel_trans : mlel l m -> mlel m n -> mlel l n.
  Proof.
    unfold mlel; intros.
    now_show (mlength l <= mlength n).
    apply le_trans with (mlength m); auto with arith.
  Qed.

  Lemma mlel_mcons_mcons : mlel l m -> mlel (a :m: l) (b :m: m).
  Proof.
    unfold mlel; simpl; auto with arith.
  Qed.

  Lemma mlel_mcons : mlel l m -> mlel l (b :m: m).
  Proof.
    unfold mlel; simpl; auto with arith.
  Qed.

  Lemma mlel_tail : mlel (a :m: l) (b :m: m) -> mlel l m.
  Proof.
    unfold mlel; simpl; auto with arith.
  Qed.

  Lemma mlel_mnil : forall l':mlist A, mlel l' mnil -> mnil = l'.
  Proof.
    intro l'; elim l'; auto with arith.
    intros a' y H H0.
    now_show (mnil = a' :m: y).
    absurd (S (mlength y) <= 0); auto with arith.
  Qed.
End mlength_order.

Hint Resolve mlel_refl mlel_mcons_mcons mlel_mcons mlel_mnil mlel_mnil mnil_mcons:
  datatypes.


(******************************)
(** ** Set minclusion on mlist  *)
(******************************)

Section SetmIncl.

  Variable A : Type.

  Definition mincl (l m:mlist A) := forall a:A, mIn a l -> mIn a m.
  Hint Unfold mincl.

  Lemma mincl_refl : forall l:mlist A, mincl l l.
  Proof.
    auto.
  Qed.
  Hint Resolve mincl_refl.

  Lemma mincl_mtl : forall (a:A) (l m:mlist A), mincl l m -> mincl l (a :m: m).
  Proof.
    auto with datatypes.
  Qed.
  Hint Immediate mincl_mtl.

  Lemma mincl_tran : forall l m n:mlist A, mincl l m -> mincl m n -> mincl l n.
  Proof.
    auto.
  Qed.

  Lemma mincl_mappl : forall l m n:mlist A, mincl l n -> mincl l (n +m+ m).
  Proof.
    auto with datatypes.
  Qed.
  Hint Immediate mincl_mappl.

  Lemma mincl_mappr : forall l m n:mlist A, mincl l n -> mincl l (m +m+ n).
  Proof.
    auto with datatypes.
  Qed.
  Hint Immediate mincl_mappr.

  Lemma mincl_mcons :
    forall (a:A) (l m:mlist A), mIn a m -> mincl l m -> mincl (a :m: l) m.
  Proof.
    unfold mincl; simpl; intros a l m H H0 a0 H1.
    now_show (mIn a0 m).
    elim H1.
    now_show (a = a0 -> mIn a0 m).
    elim H1; auto; intro H2.
    now_show (a = a0 -> mIn a0 m).
    elim H2; auto. (* solves subgoal *)
    now_show (mIn a0 l -> mIn a0 m).
    auto.
  Qed.
  Hint Resolve mincl_mcons.

  Lemma mincl_mapp : forall l m n:mlist A, mincl l n -> mincl m n -> mincl (l +m+ m) n.
  Proof.
    unfold mincl; simpl; intros l m n H H0 a H1.
    now_show (mIn a n).
    elim (mIn_mapp_or _ _ _ H1); auto.
  Qed.
  Hint Resolve mincl_mapp.

End SetmIncl.

Hint Resolve mincl_refl mincl_mtl mincl_tran mincl_mappl mincl_mappr mincl_mcons
  mincl_mapp: datatypes.


(**************************************)
(** * Cutting a mlist at some position *)
(**************************************)

Section Cutting.

  Variable A : Type.

  Fixpoint mfirstn (n:nat)(l:mlist A) : mlist A :=
    match n with
      | 0 => mnil
      | S n => match l with
		 | mnil => mnil
		 | a:m:l => a:m:(mfirstn n l)
	       end
    end.

  Lemma mfirstn_mnil n: mfirstn n [m:] = [m:].
  Proof. induction n; now simpl. Qed.

  Lemma mfirstn_mcons n a l: mfirstn (S n) (a:m:l) = a :m: (mfirstn n l).
  Proof. now simpl. Qed.

  Lemma mfirstn_all l: mfirstn (mlength l) l = l.
  Proof. induction l as [| ? ? H]; simpl; [reflexivity | now rewrite H]. Qed.

  Lemma mfirstn_all2 n: forall (l:mlist A), (mlength l) <= n -> mfirstn n l = l.
  Proof. induction n as [|k iHk].
    - intro. inversion 1 as [H1|?].
      rewrite (mlength_zero_iff_mnil l) in H1. subst. now simpl.
    - destruct l as [|x xs]; simpl.
      * now reflexivity.
      * simpl. intro H. apply Peano.le_S_n in H. f_equal. apply iHk, H.
  Qed.

  Lemma mfirstn_O l: mfirstn 0 l = [m:].
  Proof. now simpl. Qed.

  Lemma mfirstn_le_mlength n: forall l:mlist A, mlength (mfirstn n l) <= n.
  Proof.
    induction n as [|k iHk]; simpl; [auto | destruct l as [|x xs]; simpl].
    - auto with arith.
    - apply Peano.le_n_S, iHk.
  Qed.

  Lemma mfirstn_mlength_le: forall l:mlist A, forall n:nat,
    n <= mlength l -> mlength (mfirstn n l) = n.
  Proof. induction l as [|x xs Hrec].
    - simpl. intros n H. apply le_n_0_eq in H. rewrite <- H. now simpl.
    - destruct n.
      * now simpl.
      * simpl. intro H. apply le_S_n in H. now rewrite (Hrec n H).
  Qed.

  Lemma mfirstn_mapp n:
    forall l1 l2,
    mfirstn n (l1 +m+ l2) = (mfirstn n l1) +m+ (mfirstn (n - mlength l1) l2).
  Proof. induction n as [|k iHk]; intros l1 l2.
    - now simpl.
    - destruct l1 as [|x xs].
      * unfold mfirstn at 2, mlength. now rewrite 2!mapp_mnil_l, <- minus_n_O.
      * rewrite <- mapp_comm_mcons. simpl. f_equal. apply iHk.
  Qed.

  Lemma mfirstn_mapp_2 n:
    forall l1 l2,
    mfirstn ((mlength l1) + n) (l1 +m+ l2) = l1 +m+ mfirstn n l2.
  Proof. induction n as [| k iHk];intros l1 l2.
    - unfold mfirstn at 2. rewrite <- plus_n_O, mapp_mnil_r.
      rewrite mfirstn_mapp. rewrite <- minus_diag_reverse.
      unfold mfirstn at 2. rewrite mapp_mnil_r. apply mfirstn_all.
    - destruct l2 as [|x xs].
      * simpl. rewrite mapp_mnil_r. apply mfirstn_all2. auto with arith.
      * rewrite mfirstn_mapp. assert (H0 : (mlength l1 + S k - mlength l1) = S k).
        auto with arith.
        rewrite H0, mfirstn_all2; [reflexivity | auto with arith].
  Qed.

  Lemma mfirstn_mfirstn:
    forall l:mlist A,
    forall i j : nat,
    mfirstn i (mfirstn j l) = mfirstn (min i j) l.
  Proof. induction l as [|x xs Hl].
    - intros. simpl. now rewrite ?mfirstn_mnil.
    - destruct i.
      * intro. now simpl.
      * destruct j.
        + now simpl.
        + simpl. f_equal. apply Hl.
  Qed.

  Fixpoint skipn (n:nat)(l:mlist A) : mlist A :=
    match n with
      | 0 => l
      | S n => match l with
		 | mnil => mnil
		 | a:m:l => skipn n l
	       end
    end.

  Lemma mfirstn_skipn : forall n l, mfirstn n l +m+ skipn n l = l.
  Proof.
    induction n.
    simpl; auto.
    destruct l; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma mfirstn_mlength : forall n l, mlength (mfirstn n l) = min n (mlength l).
  Proof.
    induction n; destruct l; simpl; auto.
  Qed.

   Lemma mremovemlast_mfirstn : forall n l, n < mlength l ->
     mremovemlast (mfirstn (S n) l) = mfirstn n l.
   Proof.
     induction n; destruct l.
     simpl; auto.
     simpl; auto.
     simpl; auto.
     intros.
     simpl in H.
     change (mfirstn (S (S n)) (a:m:l)) with ((a:m:mnil)+m+mfirstn (S n) l).
     change (mfirstn (S n) (a:m:l)) with (a:m:mfirstn n l).
     rewrite mremovemlast_mapp.
     rewrite IHn; auto with arith.

     clear IHn; destruct l; simpl in *; try discriminate.
     inversion_clear H.
     inversion_clear H0.
   Qed.

   Lemma mfirstn_mremovemlast : forall n l, n < mlength l ->
     mfirstn n (mremovemlast l) = mfirstn n l.
   Proof.
     induction n; destruct l.
     simpl; auto.
     simpl; auto.
     simpl; auto.
     intros.
     simpl in H.
     change (mremovemlast (a :m: l)) with (mremovemlast ((a:m:mnil)+m+l)).
     rewrite mremovemlast_mapp.
     simpl; f_equal; auto with arith.
     intro H0; rewrite H0 in H; inversion_clear H; inversion_clear H1.
   Qed.

End Cutting.

(**********************************************************************)
(** ** Predicate for List addition/removal (no need for decidability) *)
(**********************************************************************)

Section mAdd.

  Variable A : Type.

  (* [mAdd a l l'] means that [l'] is exacmtly [l], with [a] added
     once somewhere *)
  Inductive mAdd (a:A) : mlist A -> mlist A -> Prop :=
    | mAdd_head l : mAdd a l (a:m:l)
    | mAdd_mcons x l l' : mAdd a l l' -> mAdd a (x:m:l) (x:m:l').

  Lemma mAdd_mapp a l1 l2 : mAdd a (l1+m+l2) (l1+m+a:m:l2).
  Proof.
   induction l1; simpl; now constructor.
  Qed.

  Lemma mAdd_msplit a l l' :
    mAdd a l l' -> exists l1 l2, l = l1+m+l2 /\ l' = l1+m+a:m:l2.
  Proof.
   induction 1.
   - exists mnil; exists l; split; trivial.
   - destruct IHmAdd as (l1 & l2 & Hl & Hl').
     exists (x:m:l1); exists l2; split; simpl; f_equal; trivial.
  Qed.

  Lemma mAdd_in a l l' : mAdd a l l' ->
   forall x, mIn x l' <-> mIn x (a:m:l).
  Proof.
   induction 1; intros; simpl in *; rewrite ?IHmAdd; tauto.
  Qed.

  Lemma mAdd_mlength a l l' : mAdd a l l' -> mlength l' = S (mlength l).
  Proof.
   induction 1; simpl; auto with arith.
  Qed.

  Lemma mAdd_inv a l : mIn a l -> exists l', mAdd a l' l.
  Proof.
   intro Ha. destruct (mIn_msplit _ _ Ha) as (l1 & l2 & ->).
   exists (l1 +m+ l2). apply mAdd_mapp.
  Qed.

  Lemma mincl_mAdd_inv a l u v :
    ~mIn a l -> mincl (a:m:l) v -> mAdd a u v -> mincl l u.
  Proof.
   intros Ha H AD y Hy.
   assert (Hy' : mIn y (a:m:u)).
   { rewrite <- (mAdd_in AD). apply H; simpl; auto. }
   destruct Hy'; [ subst; now elim Ha | trivial ].
  Qed.

End mAdd.

(********************************)
(** ** Lists without redundancy *)
(********************************)

Section ReDun.

  Variable A : Type.

  Inductive mNoDup : mlist A -> Prop :=
    | mNoDup_mnil : mNoDup mnil
    | mNoDup_mcons : forall x l, ~ mIn x l -> mNoDup l -> mNoDup (x:m:l).

  Lemma mNoDup_mAdd a l l' : mAdd a l l' -> (mNoDup l' <-> mNoDup l /\ ~mIn a l).
  Proof.
   induction 1 as [l|x l l' AD IH].
   - split; [ inversion_clear 1; now split | now constructor ].
   - split.
     + inversion_clear 1. rewrite IH in *. rewrite (mAdd_in AD) in *.
       simpl in *; split; try constructor; intuition.
     + intros (N,IN). inversion_clear N. constructor.
       * rewrite (mAdd_in AD); simpl in *; intuition.
       * apply IH. split; trivial. simpl in *; intuition.
  Qed.

  Lemma mNoDup_mremove l l' a :
    mNoDup (l+m+a:m:l') -> mNoDup (l+m+l') /\ ~mIn a (l+m+l').
  Proof.
  apply mNoDup_mAdd. apply mAdd_mapp.
  Qed.

  Lemma mNoDup_mremove_1 l l' a : mNoDup (l+m+a:m:l') -> mNoDup (l+m+l').
  Proof.
  intros. now apply mNoDup_mremove with a.
  Qed.

  Lemma mNoDup_mremove_2 l l' a : mNoDup (l+m+a:m:l') -> ~mIn a (l+m+l').
  Proof.
  intros. now apply mNoDup_mremove.
  Qed.

  Theorem mNoDup_mcons_iff a l:
    mNoDup (a:m:l) <-> ~ mIn a l /\ mNoDup l.
  Proof.
    split.
    + inversion_clear 1. now split.
    + now constructor.
  Qed.

  (** Effective computation of a mlist without duplicates *)

  Hypothesis decA: forall x y : A, {x = y} + {x <> y}.

  Fixpoint nodup (l : mlist A) : mlist A :=
    match l with
      | [m:] => [m:]
      | x:m:xs => if mIn_dec decA x xs then nodup xs else x:m:(nodup xs)
    end.

  Lemma nodup_mIn l x : mIn x (nodup l) <-> mIn x l.
  Proof.
    induction l as [|a l' Hrec]; simpl.
    - reflexivity.
    - destruct (mIn_dec decA a l'); simpl; rewrite Hrec.
      * intuition; now subst.
      * reflexivity.
  Qed.

  Lemma mNoDup_nodup l: mNoDup (nodup l).
  Proof.
    induction l as [|a l' Hrec]; simpl.
    - constructor.
    - destruct (mIn_dec decA a l'); simpl.
      * assumption.
      * constructor; [ now rewrite nodup_mIn | assumption].
  Qed.

  Lemma nodup_inv k l a : nodup k = a :m: l -> ~ mIn a l.
  Proof.
    intros H.
    assert (H' : mNoDup (a:m:l)).
    { rewrite <- H. apply mNoDup_nodup. }
    now inversion_clear H'.
  Qed.

  Theorem mNoDup_count_occ l:
    mNoDup l <-> (forall x:A, count_occ decA l x <= 1).
  Proof.
    induction l as [| a l' Hrec].
    - simpl; split; auto. constructor.
    - rewrite mNoDup_mcons_iff, Hrec, (count_occ_not_mIn decA). clear Hrec. split.
      + intros (Ha, H) x. simpl. destruct (decA a x); auto.
        subst; now rewrite Ha.
      + split.
        * specialize (H a). rewrite count_occ_mcons_eq in H; trivial.
          now inversion H.
        * intros x. specialize (H x). simpl in *. destruct (decA a x); auto.
          now apply Nat.lt_le_incl.
  Qed.

  Theorem mNoDup_count_occ' l:
    mNoDup l <-> (forall x:A, mIn x l -> count_occ decA l x = 1).
  Proof.
    rewrite mNoDup_count_occ.
    setoid_rewrite (count_occ_mIn decA). unfold gt, lt in *.
    split; intros H x; specialize (H x);
    set (n := count_occ decA l x) in *; clearbody n.
    (* the rest would be solved by omega if we had it here... *)
    - now apply Nat.le_antisymm.
    - destruct (Nat.le_gt_cases 1 n); trivial.
      + rewrite H; trivial.
      + now apply Nat.lt_le_incl.
  Qed.

  (** Alternative characterisations of being without duplicates,
      thanks to [mnth_error] and [mnth] *)

  Lemma mNoDup_mnth_error l :
    mNoDup l <->
    (forall i j, i<mlength l -> mnth_error l i = mnth_error l j -> i = j).
  Proof.
    split.
    { intros H; induction H as [|a l Hal Hl IH]; intros i j Hi E.
      - inversion Hi.
      - destruct i, j; simpl in *; auto.
        * elim Hal. eapply mnth_error_mIn; eauto.
        * elim Hal. eapply mnth_error_mIn; eauto.
        * f_equal. apply IH; auto with arith. }
    { induction l as [|a l]; intros H; constructor.
      * intro Ha. apply mIn_mnth_error in Ha. destruct Ha as (n,Hn).
        assert (n < mlength l) by (now rewrite <- mnth_error_Some, Hn).
        specialize (H 0 (S n)). simpl in H. discriminate H; auto with arith.
      * apply IHl.
        intros i j Hi E. apply eq_add_S, H; simpl; auto with arith. }
  Qed.

  Lemma mNoDup_mnth l d :
    mNoDup l <->
    (forall i j, i<mlength l -> j<mlength l ->
       mnth i l d = mnth j l d -> i = j).
  Proof.
    split.
    { intros H; induction H as [|a l Hal Hl IH]; intros i j Hi Hj E.
      - inversion Hi.
      - destruct i, j; simpl in *; auto.
        * elim Hal. subst a. apply mnth_mIn; auto with arith.
        * elim Hal. subst a. apply mnth_mIn; auto with arith.
        * f_equal. apply IH; auto with arith. }
    { induction l as [|a l]; intros H; constructor.
      * intro Ha. eapply mIn_mnth in Ha. destruct Ha as (n & Hn & Hn').
        specialize (H 0 (S n)). simpl in H. discriminate H; eauto with arith.
      * apply IHl.
        intros i j Hi Hj E. apply eq_add_S, H; simpl; auto with arith. }
  Qed.

  (** Having [mNoDup] hypotheses bring more precise facts about [mincl]. *)

  Lemma mNoDup_mincl_mlength l l' :
    mNoDup l -> mincl l l' -> mlength l <= mlength l'.
  Proof.
   intros N. revert l'. induction N as [|a l Hal N IH]; simpl.
   - auto with arith.
   - intros l' H.
     destruct (mAdd_inv a l') as (l'', AD). { apply H; simpl; auto. }
     rewrite (mAdd_mlength AD). apply le_n_S. apply IH.
     now apply mincl_mAdd_inv with a l'.
  Qed.

  Lemma mNoDup_mlength_mincl l l' :
    mNoDup l -> mlength l' <= mlength l -> mincl l l' -> mincl l' l.
  Proof.
   intros N. revert l'. induction N as [|a l Hal N IH].
   - destruct l'; easy.
   - intros l' E H x Hx.
     destruct (mAdd_inv a l') as (l'', AD). { apply H; simpl; auto. }
     rewrite (mAdd_in AD) in Hx. simpl in Hx.
     destruct Hx as [Hx|Hx]; [left; trivial|right].
     revert x Hx. apply (IH l''); trivial.
     * apply le_S_n. now rewrite <- (mAdd_mlength AD).
     * now apply mincl_mAdd_inv with a l'.
  Qed.

End ReDun.

(** mNoDup and mmap *)

(** NB: the reciprocal result holds only for injective functions,
    see FinFun.v *)

Lemma mNoDup_mmap_inv A B (f:A->B) l : mNoDup (mmap f l) -> mNoDup l.
Proof.
 induction l; simpl; inversion_clear 1; subst; constructor; auto.
 intro H. now apply (mIn_mmap f) in H.
Qed.

(***********************************)
(** ** Sequence of natural numbers *)
(***********************************)

Section NatSeq.

  (** [mseq] computes the sequence of [len] contiguous integers
      that starts at [start]. For instance, [mseq 2 3] is [2:m:3:m:4:m:mnil]. *)

  Fixpoint mseq (start len:nat) : mlist nat :=
    match len with
      | 0 => mnil
      | S len => start :m: mseq (S start) len
    end.

  Lemma mseq_mlength : forall len start, mlength (mseq start len) = len.
  Proof.
    induction len; simpl; auto.
  Qed.

  Lemma mseq_mnth : forall len start n d,
    n < len -> mnth n (mseq start len) d = start+n.
  Proof.
    induction len; intros.
    inversion H.
    simpl mseq.
    destruct n; simpl.
    auto with arith.
    rewrite IHlen;simpl; auto with arith.
  Qed.

  Lemma mseq_shift : forall len start,
    mmap S (mseq start len) = mseq (S start) len.
  Proof.
    induction len; simpl; auto.
    intros.
    rewrite IHlen.
    auto with arith.
  Qed.

  Lemma mIn_mseq len start n :
    mIn n (mseq start len) <-> start <= n < start+len.
  Proof.
   revert start. induction len; simpl; intros.
   - rewrite <- plus_n_O. split;[easy|].
     intros (H,H'). apply (Lt.lt_irrefl _ (Lt.le_lt_trans _ _ _ H H')).
   - rewrite IHlen, <- plus_n_Sm; simpl; split.
     * intros [H|H]; subst; intuition auto with arith.
     * intros (H,H'). destruct (Lt.le_lt_or_eq _ _ H); intuition.
  Qed.

  Lemma mseq_mNoDup len start : mNoDup (mseq start len).
  Proof.
   revert start; induction len; simpl; constructor; trivial.
   rewrite mIn_mseq. intros (H,_). apply (Lt.lt_irrefl _ H).
  Qed.

End NatSeq.

Section mExists_mForall.

  (** * Existential and universal predicates over mlists *)

  Variable A:Type.

  Section One_predicate.

    Variable P:A->Prop.

    Inductive mExists : mlist A -> Prop :=
      | mExists_mcons_mhd : forall x l, P x -> mExists (x:m:l)
      | mExists_mcons_mtl : forall x l, mExists l -> mExists (x:m:l).

    Hint Constructors mExists.

    Lemma mExists_exists (l:mlist A) :
      mExists l <-> (exists x, mIn x l /\ P x).
    Proof.
      split.
      - induction 1; firstorder.
      - induction l; firstorder; subst; auto.
    Qed.

    Lemma mExists_mnil : mExists mnil <-> False.
    Proof. split; inversion 1. Qed.

    Lemma mExists_mcons x l:
      mExists (x:m:l) <-> P x \/ mExists l.
    Proof. split; inversion 1; auto. Qed.

    Lemma mExists_dec l:
      (forall x:A, {P x} + { ~ P x }) ->
      {mExists l} + {~ mExists l}.
    Proof.
      intro Pdec. induction l as [|a l' Hrec].
      - right. now rewrite mExists_mnil.
      - destruct Hrec as [Hl'|Hl'].
        * left. now apply mExists_mcons_mtl.
        * destruct (Pdec a) as [Ha|Ha].
          + left. now apply mExists_mcons_mhd.
          + right. now inversion_clear 1.
    Qed.

    Inductive mForall : mlist A -> Prop :=
      | mForall_mnil : mForall mnil
      | mForall_mcons : forall x l, P x -> mForall l -> mForall (x:m:l).

    Hint Constructors mForall.

    Lemma mForall_forall (l:mlist A):
      mForall l <-> (forall x, mIn x l -> P x).
    Proof.
      split.
      - induction 1; firstorder; subst; auto.
      - induction l; firstorder.
    Qed.

    Lemma mForall_inv : forall (a:A) l, mForall (a :m: l) -> P a.
    Proof.
      intros; inversion H; trivial.
    Qed.

    Lemma mForall_rect : forall (Q : mlist A -> Type),
      Q [m:] -> (forall b l, P b -> Q (b :m: l)) -> forall l, mForall l -> Q l.
    Proof.
      intros Q H H'; induction l; intro; [|eapply H', mForall_inv]; eassumption.
    Qed.

    Lemma mForall_dec :
      (forall x:A, {P x} + { ~ P x }) ->
      forall l:mlist A, {mForall l} + {~ mForall l}.
    Proof.
      intro Pdec. induction l as [|a l' Hrec].
      - left. apply mForall_mnil.
      - destruct Hrec as [Hl'|Hl'].
        + destruct (Pdec a) as [Ha|Ha].
          * left. now apply mForall_mcons.
          * right. now inversion_clear 1.
        + right. now inversion_clear 1.
    Qed.

  End One_predicate.

  Lemma mForall_mExists_neg (P:A->Prop)(l:mlist A) :
   mForall (fun x => ~ P x) l <-> ~(mExists P l).
  Proof.
   rewrite mForall_forall, mExists_exists. firstorder.
  Qed.

  Lemma mExists_mForall_neg (P:A->Prop)(l:mlist A) :
    (forall x, P x \/ ~P x) ->
    mExists (fun x => ~ P x) l <-> ~(mForall P l).
  Proof.
   intro Dec.
   split.
   - rewrite mForall_forall, mExists_exists; firstorder.
   - intros NF.
     induction l as [|a l IH].
     + destruct NF. constructor.
     + destruct (Dec a) as [Ha|Ha].
       * apply mExists_mcons_mtl, IH. contradict NF. now constructor.
       * now apply mExists_mcons_mhd.
  Qed.

  Lemma mForall_mExists_dec (P:A->Prop) :
    (forall x:A, {P x} + { ~ P x }) ->
    forall l:mlist A,
    {mForall P l} + {mExists (fun x => ~ P x) l}.
  Proof.
    intros Pdec l.
    destruct (mForall_dec P Pdec l); [left|right]; trivial.
    apply mExists_mForall_neg; trivial.
    intro x. destruct (Pdec x); [now left|now right].
  Qed.

  Lemma mForall_impl : forall (P Q : A -> Prop), (forall a, P a -> Q a) ->
    forall l, mForall P l -> mForall Q l.
  Proof.
    intros P Q H l. rewrite !mForall_forall. firstorder.
  Qed.

End mExists_mForall.

Hint Constructors mExists.
Hint Constructors mForall.

Section mForall2.

  (** [mForall2]: stating that elements of two mlists are pairwise related. *)

  Variables A B : Type.
  Variable R : A -> B -> Prop.

  Inductive mForall2 : mlist A -> mlist B -> Prop :=
    | mForall2_mnil : mForall2 [m:] [m:]
    | mForall2_mcons : forall x y l l',
      R x y -> mForall2 l l' -> mForall2 (x:m:l) (y:m:l').

  Hint Constructors mForall2.

  Theorem mForall2_refl : mForall2 [m:] [m:].
  Proof. intros; apply mForall2_mnil. Qed.

  Theorem mForall2_mapp_inv_l : forall l1 l2 l',
    mForall2 (l1 +m+ l2) l' ->
    exists l1' l2', mForall2 l1 l1' /\ mForall2 l2 l2' /\ l' = l1' +m+ l2'.
  Proof.
    induction l1; intros.
      exists [m:], l'; auto.
      simpl in H; inversion H; subst; clear H.
      apply IHl1 in H4 as (l1' & l2' & Hl1 & Hl2 & ->).
      exists (y:m:l1'), l2'; simpl; auto.
  Qed.

  Theorem mForall2_mapp_inv_r : forall l1' l2' l,
    mForall2 l (l1' +m+ l2') ->
    exists l1 l2, mForall2 l1 l1' /\ mForall2 l2 l2' /\ l = l1 +m+ l2.
  Proof.
    induction l1'; intros.
      exists [m:], l; auto.
      simpl in H; inversion H; subst; clear H.
      apply IHl1' in H4 as (l1 & l2 & Hl1 & Hl2 & ->).
      exists (x:m:l1), l2; simpl; auto.
  Qed.

  Theorem mForall2_mapp : forall l1 l2 l1' l2',
    mForall2 l1 l1' -> mForall2 l2 l2' -> mForall2 (l1 +m+ l2) (l1' +m+ l2').
  Proof.
    intros. induction l1 in l1', H, H0 |- *; inversion H; subst; simpl; auto.
  Qed.
End mForall2.

Hint Constructors mForall2.

Section mForallPairs.

  (** [mForallPairs] : specifies that a certain relation should
    always hold when inspecting all possible pairs of elements of a mlist. *)

  Variable A : Type.
  Variable R : A -> A -> Prop.

  Definition mForallPairs l :=
    forall a b, mIn a l -> mIn b l -> R a b.

  (** [mForallOrdPairs] : we still check a relation over all pairs
     of elements of a mlist, but now the order of elements matters. *)

  Inductive mForallOrdPairs : mlist A -> Prop :=
    | FOP_mnil : mForallOrdPairs mnil
    | FOP_mcons : forall a l,
      mForall (R a) l -> mForallOrdPairs l -> mForallOrdPairs (a:m:l).

  Hint Constructors mForallOrdPairs.

  Lemma mForallOrdPairs_mIn : forall l,
    mForallOrdPairs l ->
    forall x y, mIn x l -> mIn y l -> x=y \/ R x y \/ R y x.
  Proof.
    induction 1.
    inversion 1.
    simpl; destruct 1; destruct 1; subst; auto.
    right; left. apply -> mForall_forall; eauto.
    right; right. apply -> mForall_forall; eauto.
  Qed.

  (** [mForallPairs] implies [mForallOrdPairs]. The mreverse implication is true
    only when [R] is symmetric and reflexive. *)

  Lemma mForallPairs_mForallOrdPairs l: mForallPairs l -> mForallOrdPairs l.
  Proof.
    induction l; auto. intros H.
    constructor.
    apply <- mForall_forall. intros; apply H; simpl; auto.
    apply IHl. red; intros; apply H; simpl; auto.
  Qed.

  Lemma mForallOrdPairs_mForallPairs :
    (forall x, R x x) ->
    (forall x y, R x y -> R y x) ->
    forall l, mForallOrdPairs l -> mForallPairs l.
  Proof.
    intros Refl Sym l Hl x y Hx Hy.
    destruct (mForallOrdPairs_mIn Hl _ _ Hx Hy); subst; intuition.
  Qed.
End mForallPairs.

(** * mInversion of predicates over mlists based on head symbol *)

Ltac is_mlist_mconstr c :=
 match c with
  | mnil => idtac
  | (_:m:_) => idtac
  | _ => fail
 end.

Ltac invmlist f :=
 match goal with
  | H:f ?l |- _ => is_mlist_mconstr l; inversion_clear H; invmlist f
  | H:f _ ?l |- _ => is_mlist_mconstr l; inversion_clear H; invmlist f
  | H:f _ _ ?l |- _ => is_mlist_mconstr l; inversion_clear H; invmlist f
  | H:f _ _ _ ?l |- _ => is_mlist_mconstr l; inversion_clear H; invmlist f
  | H:f _ _ _ _ ?l |- _ => is_mlist_mconstr l; inversion_clear H; invmlist f
  | _ => idtac
 end.



(** * Exporting hints and tactics *)


Hint Rewrite
  mrev_involutive (* mrev (mrev l) = l *)
  mrev_unit (* mrev (l +m+ a :m: mnil) = a :m: mrev l *)
  mmap_mnth (* mnth n (mmap f l) (f d) = f (mnth n l d) *)
  mmap_mlength (* mlength (mmap f l) = mlength l *)
  mseq_mlength (* mlength (mseq start len) = len *)
  mapp_mlength (* mlength (l +m+ l') = mlength l + mlength l' *)
  mrev_mlength (* mlength (mrev l) = mlength l *)
  mapp_mnil_r (* l +m+ mnil = l *)
  : mlist.

Ltac simpl_mlist := autorewrite with mlist.
Ltac ssimpl_mlist := autorewrite with mlist using simpl.

Hint Resolve mapp_mnil_end : datatypes.
(* end hide *)

Section Repeat.

  Variable A : Type.
  Fixpoint mrepeat (x : A) (n: nat ) :=
    match n with
      | O => [m:]
      | S k => x:m:(mrepeat x k)
    end.

  Theorem mrepeat_mlength x n:
    mlength (mrepeat x n) = n.
  Proof.
    induction n as [| k Hrec]; simpl; rewrite ?Hrec; reflexivity.
  Qed.

  Theorem mrepeat_spec n x y:
    mIn y (mrepeat x n) -> y=x.
  Proof.
    induction n as [|k Hrec]; simpl; destruct 1; auto.
  Qed.

End Repeat.

(* Unset Universe Polymorphism. *)
