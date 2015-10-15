Require Import MetaCoq.MetaCoq.
Import MetaCoqNotations.

Definition exact {A : Type} (x : A) : M A :=
  ret x.

Definition refine : forall {A : Type}, A -> M A := @exact.

Definition reflexivity {A : Type} {x : A} : M (x = x) :=
  ret (eq_refl : x = x).

Definition apply {A B : Type} (f : A -> B) {x : A} : M B :=
  ret (f x).

Definition intro {A : Type} {q : A -> Type} (s : forall x : A, M (q x))
: M (forall x : A, q x) :=
  nu x,
  p <- s x;
  abs x p.

Definition symmetry {A : Type} {t u : A} {p : t = u} : M (u = t) :=
  ret (eq_sym p).

Definition idtac {A : Type} {x : A} : M A := ret x.

Definition NotFound : Exception. exact exception. Qed.

Definition lookup (A : Type) :=
  mfix1 f (hyps : list Hyp) : M A :=
    mmatch hyps with
    | nil => raise NotFound
    | [? a b xs] cons (@ahyp A a b) xs => ret a
    | [? a xs] cons a xs => f xs
    end.

Definition assumption {A : Type} : M A :=
  hyps <- hypotheses;
  lookup A hyps.

Definition transitivity {A : Type} (y : A) {x z : A} {f : x = y} {g : y = z} : M (x = z) :=
  ret (eq_trans f g).

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
  | B => [H] ret (eq_rect_r (fun T=>T) x H)
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

Inductive goal_pattern : Type :=
| gbase : forall (B : Type), M B -> goal_pattern
| gtele : forall {C}, (forall (x : C), goal_pattern) -> goal_pattern.

Arguments gbase _ _.
Arguments gtele {C} _.

Module LtacEmuNotations.

Notation "'intros' x .. y" :=
  (intro (fun x => .. (intro (fun y => idtac)) ..))
    (at level 99, x binder).
Notation "'intro' x" :=
  (intro (fun x => idtac))
    (at level 99).

Notation "[[ x .. y |- ps ]] => t" := (gtele (fun x=> .. (gtele (fun y=>gbase ps t)).. ))
  (at level 202, x binder, y binder, ps at next level) : goal_match_scope.

Delimit Scope goal_match_scope with goal_match.

End LtacEmuNotations.

Import LtacEmuNotations.

(** Given a pattern of the form [[? a b c] p a b c => t a b c] it returns
    the pattern with evars for each pattern variable: [p ?a ?b ?c => t ?a ?b ?c] *)
Definition open_pattern :=
  mfix1 op (p : goal_pattern) : M (goal_pattern) :=
    match p return M _ with
    | gbase _ _ => ret p
    | @gtele C f =>
      e <- evar C; op (f e)
    end.

Import ListNotations.


Notation "[[ x .. y |- ps ]] => t" := (gtele (fun x=> .. (gtele (fun y=>gbase ps t)).. ))
  (at level 202, x binder, y binder, ps at next level) : goal_match_scope.

Delimit Scope goal_match_scope with goal_match.

Fixpoint match_goal' {P} (p : goal_pattern) (l : list Hyp) : M P :=
  match p, l with
  | gbase g t, _ =>
    peq <- munify g P;
    match peq in (_ = P) return M P with
    | eq_refl => t
    end
  | @gtele C f, (@ahyp A a None :: l) =>
    mtry
      e <- evar C;
      teq <- munify C A;
      let e' := match teq with eq_refl => e end in
      veq <- munify e' a;
      match_goal' (f e) l
    with _ => match_goal' p l end
  | _, _ => raise exception
  end.

Definition match_goal {P} p : M P := hypotheses >> match_goal' p.
Arguments match_goal {P} p%goal_match.

Definition assump {P} : M P := match_goal ([[ x:P |- P ]] => exact x).

Definition split {P Q : Prop} {x:P} {y : Q} : M (P /\ Q)
  := ret (conj x y).
