Require Import MetaCoq.MetaCoq.
Require Import Strings.String.
Import MetaCoqNotations.

Definition coerce_ind {A : Prop} (B : Prop) (H : A = B) (x : A) : B :=
  eq_ind A (fun T => T) x B H.

Definition coerce_rect {A : Type} (B : Type) (H : A = B) (x : A) : B :=
  eq_rect A (fun T => T) x B H.

Definition coerce_rec {A : Set} (B : Set) (H : A = B) (x : A) : B :=
  eq_rec A (fun T => T) x B H.

Definition coerce_ind_r {A : Prop} (B : Prop) (H : B = A) (x : A) : B :=
  eq_ind_r (fun T => T) x H.

Definition coerce_rect_r {A : Type} (B : Type) (H : B = A) (x : A) : B :=
  eq_rect_r (fun T => T) x H.

Definition coerce_rec_r {A : Set} (B : Set) (H : B = A) (x : A) : B :=
  eq_rec_r (fun T => T) x H.

Definition exact {A : Type} (x : A) : M A := ret x.

Definition refine : forall {A : Type}, A -> M A := @exact.

Definition intro {A : Type} {q : A -> Type} (s : string) (f : forall x : A, M (q x))
: M (forall x : A, q x) :=
  tnu s (fun x=>
  p <- f x;
  abs x p).

Definition idtac {A : Type} {x : A} : M A := ret x.

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
  | B => [H] ret (coerce_rect_r B H x)
  | _ => raise CantCoerce
  end.

Definition reduceGoal {A : Type} : M A :=
  let A' := simpl A in
  evar A'.

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
Open Scope string.
Notation "'hid_intro' x , f" := (intro "x" (fun x=>f)) (at level 0).
Notation "'mintros' x .. y" :=
  (hid_intro x, .. (hid_intro y, idtac)..)
    (at level 99, x binder, y binder).
Notation "'mintro' x" :=
  (hid_intro x , idtac)
    (at level 99).

Notation "[[ x .. y |- ps ] ] => t" := (gtele (fun x=> .. (gtele (fun y=>gbase ps t)).. ))
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

Definition assumption {P : Type} : M P := match_goal ([[ x:P |- P ]] => exact x).

Definition CantApply {T1 T2} (x:T1) (y:T2) : Exception. exact exception. Qed.

Definition apply {P T : Prop} (l : T) : M P :=
  (mfix2 app (T : Prop) (l' : T) : M P :=
    mtry
      p <- munify P T;
      ret (coerce_ind_r P p l')
    with [? A (a b : A)] NotUnifiableException a b =>
      mmatch T with
      | [? (T1 : Type) (T2 : T1 -> Prop)] (forall x:T1, T2 x) => [H]
          e <- evar T1;
          l' <- retS (eq_ind (forall x : T1, T2 x) (fun T => T -> T2 e)
            (fun l : forall x : T1, T2 x => l e) _ H l');
          app (T2 e) l'
      | _ =>
          (raise (CantApply a b) : M P)
      end
    end) _ l.

Definition apply_type {P T : Type} (l : T) : M P :=
  (mfix2 app (T : Type) (l' : T) : M P :=
    mtry
      p <- munify P T;
      ret (eq_rect_r (fun T => T) l' p)
    with [? A (a b : A)] NotUnifiableException a b =>
      mmatch T with
      | [? (T1 : Type) (T2 : T1 -> Type)] (forall x:T1, T2 x) => [H]
          e <- evar T1;
          l' <- retS (eq_rect (forall x : T1, T2 x) (fun T => T -> T2 e)
            (fun l : forall x : T1, T2 x => l e) _ H l');
          app (T2 e) l'
      | _ =>
          (raise (CantApply a b) : M P)
      end
    end) _ l.

Definition reflexivity {A : Prop} : M A :=
  apply (@eq_refl).

Definition transitivity {A : Prop} {B : Type} (y : B) : M A :=
  apply (fun x => @eq_trans B x y).

Definition symmetry {A : Prop} : M A :=
  apply (@eq_sym).

Definition coerce_applied {A B : Type} :=
  (mfix2 rec (A : Type) (l : A) : M B :=
     mmatch A with
     | [? T1 T2] (forall x : T1, T2 x) => [H]
         e <- evar T1;
         l <- retS (eq_rect (forall x : T1, T2 x) (fun T => T -> T2 e)
           (fun l : forall x : T1, T2 x => l e) _ H l);
         rec (T2 e) l
     | B => [H] ret (eq_rect_r (fun T=>T) l H)
     | _ => raise CantCoerce
     end
  ) A.

Definition CantFindConstructor : Exception. exact exception. Qed.
Definition ConstructorsStartingFrom1 : Exception. exact exception. Qed.

Definition constructor {A : Type} (n : nat) : M A :=
  match n with
  | 0 => raise ConstructorsStartingFrom1
  | S n =>
      l <- constrs A;
      match nth_error l n with
        | Some x => coerce_applied (elem x)
        | None => raise CantFindConstructor
      end
  end.

Definition constructor0 {A : Type} : M A :=
  l <- constrs A;
  (mfix1 rec (l : list dyn) : M A :=
     match l with
     | [] => raise CantFindConstructor
     | x::xs => mtry coerce_applied (elem x) with CantCoerce => rec xs end
     end
  ) l.

Definition Not1Constructor : Exception. exact exception. Qed.

Definition split {A : Type} : M A :=
  l <- constrs A;
  match l with
  | [x] => coerce_applied (elem x)
  | _ => raise Not1Constructor
  end.

Definition Not2Constructor : Exception. exact exception. Qed.

Definition left {A : Type} : M A :=
  l <- constrs A;
  match l with
  | [x; _] => coerce_applied (elem x)
  | _ => raise Not2Constructor
  end.

Definition right {A : Type} : M A :=
  l <- constrs A;
  match l with
  | [_; x] => coerce_applied (elem x)
  | _ => raise Not2Constructor
  end.

Definition auto {A : Prop} : M A :=
  mmatch A with
  | True => [H] ret (coerce_ind A H I)
  | [? B (x : B)] @eq B x x => [H] ret (coerce_ind A H eq_refl)
  | _ => evar A
  end.
