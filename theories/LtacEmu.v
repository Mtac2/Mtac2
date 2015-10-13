Require Import MetaCoq.MetaCoq.
Import MetaCoqNotations.

Definition exact {A : Type} (x : A) : M A :=
  ret x.

Definition refine : forall {A : Type}, A -> M A := @exact.

Lemma test1 : forall P, P -> P.
MProof.
  exact (fun P x => x).
Qed.

Definition reflexivity {A : Type} {x : A} : M (x = x) :=
  ret (eq_refl : x = x).

Definition apply {B C : Type} (l : B -> C) : M C :=
  h <- evar B;
  ret (l h).

Lemma test2 : True.
MProof.
   apply (fun (x : True) => x).
   exact I.
Qed.

Lemma test3 : O = O.
MProof.
  reflexivity.
Qed.

Require Import Omega.

Goal forall n : nat, n = 0 \/ n = 1 \/ n > 1.
Proof.
  intro n.
  omega.
Qed.

Lemma bar : forall x y : nat, x = y -> y = x.
Proof.
  intros x y H.
  apply sym_eq.
  exact H.
Qed.

Definition intro {A : Type} {q} (s : forall x : A, M (q x))
: M (forall x : A, q x) :=
  nu x,
  p <- s x;
  abs x p.

Lemma test4 : forall (p : Prop), p = p.
MProof.
  intro (fun x => reflexivity).
Qed.

Definition symmetry {A : Type} {t u : A} {p : t = u} : M (u = t) :=
  ret (eq_sym p).

Definition idtac {A : Type} {x : A} : M A := ret x.

Notation "'intros' x .. y" := (intro (fun x => .. (intro (fun y => idtac)) ..)) (at level 99, x binder).
Notation "'intro' x" := (intro (fun x => idtac)) (at level 99).

Definition NotFound : Exception.
  exact exception.
Qed.

Definition lookup (A : Type) :=
  mfix1 f (hyps : list Hyp) : M A :=
    mmatch hyps return M A with
    | nil => raise NotFound
    | [? a b xs] cons (@ahyp A a b) xs => ret a
    | [? a xs] cons a xs => f xs
    end.

Definition assumption {A : Type} : M A :=
  hyps <- hypotheses;
  lookup A hyps.

Lemma test5 : forall n m : nat, n = m -> m = n.
MProof.
  intros n m H.
  idtac. (* TODO: Remove this. Necessary to see the reduced term *)
  symmetry.
  assumption.
Qed.

Definition transitivity {A : Type} (y : A) {x z : A} {f : x = y} {g : y = z} : M (x = z) :=
  ret (eq_trans f g).

Lemma test6 : forall (x y z : Prop), x = y -> y = z -> x = z.
MProof.
  intros x y z H G.
  idtac. (* TODO: Remove this. Necessary to see the reduced term *)
  transitivity y.
  exact H.
  exact G.
Qed.

Definition absurd {A : Type} (p : Prop) {y : ~p} {x : p} : M A :=
  ret (match y x with end).

Require Import Coq.Lists.List.
Import ListNotations.

Definition mmap {A B : Type} (f : A -> M B) :=
  mfix1 rec (l : list A) : M (list B) :=
    match l with
    | [] =>
        ret []
    | (x :: xs) =>
        x <- f x;
        xs <- rec xs;
        ret (x :: xs)
    end.

Definition CantCoerce : Exception. exact exception. Qed.

Definition coerce {A B : Type} (x : A) : M B :=
  mmatch A with
  | B => [H] ret (eq_rect_r _ (fun x0 : B => x0) H x)
  | _ => raise CantCoerce
  end.

Program Definition copy_ctx {A} (B : A -> Type) :=
  mfix1 rec (d : dyn) : M Type :=
    mmatch d with
    | [? C (D : C -> Type) (E : forall y:C, D y)] {| elem := fun x : C => E x |} =>
        nu y : C,
        r <- rec (Dyn _ (E y));
        pabs y r
    | [? c : A] {| elem := c |} =>
        ret (B c)
    end.

Definition destruct {A : Type} (n : A) {P : A -> Prop} : M (P n) :=
  l <- constrs A;
  l <- mmap (fun d : dyn =>
               t' <- copy_ctx P d;
               e <- evar t';
               ret {| elem := e |}) l;
  let c := {| case_ind := A;
              case_val := n;
              case_type := P n;
              case_return := {| elem := fun n : A => P n |};
              case_branches := l
           |} in
  d <- makecase c;
  d <- coerce (elem d);
  ret d.
