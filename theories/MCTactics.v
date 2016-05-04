Require Export MetaCoq.MetaCoq.
Require Import MetaCoq.MCListUtils.
Import MetaCoqNotations.

Require Import Strings.String.

Require Import Lists.List.
Import ListNotations.

Definition metaCoqReduceGoal {A : Type} : M A :=
  let A' := simpl A in
  evar A'.

Definition coerce_rect {A : Type} (B : Type) (H : A = B) (x : A) : B :=
  eq_rect A (fun T => T) x B H.

Definition CantCoerce : Exception. exact exception. Qed.

Definition coerce {A B : Type} (x : A) : M B :=
  mtry
    H <- munify A B;
    retS (coerce_rect B H x)
  with _ => raise CantCoerce
  end.

Inductive goal :=
| TheGoal : forall {A}, A -> goal
| AHyp : forall {A}, (A -> goal) -> goal.

Definition tactic := (goal -> M (list goal)).

Definition run_tac {P} (t : tactic) : M P :=
  e <- evar P;
  t (TheGoal e);;
  ret e.

Definition NotAGoal : Exception. exact exception. Qed.
Definition goal_type g : M Type :=
  match g with
    | @TheGoal A _ => ret A
    | _ => raise NotAGoal
  end.

Definition dyn_to_goal d :=
  match d with
  | Dyn _ x => TheGoal x
  end.

Definition goal_to_dyn : goal -> M dyn := fun g =>
  match g with
  | TheGoal d => ret (Dyn _ d)
  | _ => raise NotAGoal
  end.

Definition idtac : tactic := fun g=>ret [g].

Definition exact {A} (x:A) : tactic := fun g=>
  munify g (TheGoal x);; ret nil.

Definition reflexivity : tactic := fun g=>
  A <- evar Type;
  x <- evar A;
  munify g (TheGoal (eq_refl x));; ret nil.

Definition tryt (t:tactic) := fun g=>
  mtry t g with _ => ret [g] end.

Definition OR (t u : tactic) := fun g => mtry t g with _ => u g end.

Definition close_goals {A} (x:A) : list goal -> M (list goal) :=
  mmap (fun g'=>r <- abs x g'; ret (@AHyp A r)).

Definition NotAProduct : Exception. exact exception. Qed.
(* Program Definition intro (n : string) : tactic := fun g=>
  mmatch g return M list goal with
  | [? (A:Type) (P:A -> Type) e] @TheGoal (forall x:A, P x) e =>
    tnu n (fun x=>
      e' <- evar _;
      g <- abs x e';
      munify e g;;
      new_goal <- abs x (TheGoal e');
      ret [(AHyp new_goal)])
  | _ => raise NotAProduct
  end.
*)
Program Definition intro_cont {A} (t: A->tactic) : tactic := fun g=>
  mmatch g return M list goal with
  | [? B (P:B -> Type) e] @TheGoal (forall x:B, P x) e =>
    munify B A;;
    n <- get_name t;
    tnu n (fun x=>
      e' <- evar _;
      g <- abs x e';
      munify e g;;
      x <- coerce x;
      let x := hnf x in
      t x (TheGoal e') >> close_goals x)
  | _ => raise NotAProduct
  end.


Fixpoint is_open (g : goal) : M bool :=
  match g with
  | TheGoal e => is_evar e
  | @AHyp C f => nu x:C, is_open (f x)
  end.

Definition filter_goals : list goal -> M (list goal) := mfilter is_open.

Definition open_and_apply (t : tactic) : tactic := fix open g :=
    match g return M _ with
    | TheGoal _ => t g
    | @AHyp C f =>
      x <- get_name f;
      tnu x (fun x : C=>
        open (f x) >> close_goals x)
    end.


Definition NotSameSize : Exception. exact exception. Qed.
Fixpoint gmap (funs : list tactic) (ass : list goal) : M (list (list goal)) :=
  match funs, ass with
  | nil, nil => ret nil
  | f::funs', g::ass' =>
    fa <- open_and_apply f g;
    rest <- gmap funs' ass';
    ret (fa :: rest)
  | _, _ => raise NotSameSize
  end.

Definition bbind (t:tactic) (l:list tactic) : tactic := fun g=>
  l' <- t g;
  l' <- filter_goals l';
  ls <- gmap l l';
  ret (concat ls).

Definition bindb (t u:tactic) : tactic := fun g=>
  l <- t g;
  l <- filter_goals l;
  r <- mmap (open_and_apply u) l;
  let r := hnf List.concat _ r in
  ret r.

Class semicolon {A} {B} {C} (t:A) (u:B) := SemiColon { the_value : C }.
Arguments SemiColon {A} {B} {C} t u the_value.

Instance i_bbind (t:tactic) (l:list tactic) : semicolon t l | 100 :=
  SemiColon _ _ (bbind t l).

Instance i_bindb (t:tactic) (u:tactic) : semicolon t u | 100:=
  SemiColon _ _ (bindb t u).

Instance i_mtac A B (t:M A) (u:M B) : semicolon t u | 100 :=
  SemiColon _ _ (_ <- t; u).


Program Definition copy_ctx {A} (B : A -> Type) :=
  mfix1 rec (d : dyn) : M Type :=
    mmatch d with
    | [? c : A] {| elem := c |} =>
        ret (B c)
    | [? C (D : C -> Type) (c : forall y:C, D y)] {| elem := c |} =>
        nu y : C,
        r <- rec (Dyn _ (c y));
        pabs y r
    | [? C D (c : C->D)] {| elem := c |} =>
        nu y : C,
        r <- rec (Dyn _ (c y));
        pabs y r
    | _ => raise NotAGoal
    end.

Program Definition hyps_except {A} (x : A) :=
  l <- hypotheses;
  mfilter (fun y=>mmatch y with
    | [? b] ahyp x b => ret false
    | _ => ret true
    end) l.

Definition NotAVariable : Exception. exact exception. Qed.
Definition destruct {A : Type} (n : A) : tactic := fun g=>
  b <- is_var n;
  if negb b then raise NotAVariable
  else
    ctx <- hyps_except n;
    P <- Cevar (A->Type) ctx;
    let Pn := P n in
    gT <- goal_type g;
    munify Pn gT;;
    l <- constrs A;
    l <- mmap (fun d : dyn =>
      (* a constructor c has type (forall x, ... y, A) and we return
         (forall x, ... y, P (c x .. y)) *)
      t' <- copy_ctx P d;
      e <- evar t';
      ret {| elem := e |}) l;
    let c := {| case_ind := A;
                case_val := n;
                case_type := Pn;
                case_return := {| elem := P |};
                case_branches := l
             |} in
    d <- makecase c;
    d <- coerce (elem d);
    let d := hnf d in
    munify (@TheGoal Pn d) g;;
    let l := hnf (List.map dyn_to_goal l) in
    ret l.

Definition type_of {A} (x:A) := A.

Local Obligation Tactic := idtac.

Definition CantApply {T1 T2} (x:T1) (y:T2) : Exception. exact exception. Qed.
Program Definition apply {T} (c : T) : tactic := fun g=>
  (mfix2 app (U : Type) (d : U) : M (list goal) :=
    ttry (
      munify (TheGoal d) g;;
      ret []
    )
    (fun e=> (* should check if e is NotUnifiable *)
      mmatch U return M (list goal) with
      | [? (T1 : Type) (T2 : T1 -> Prop)] (forall x:T1, T2 x) => [H]
          e <- evar T1;
          r <- app (T2 e) (eq_rect_r (fun U=>U) d H e);
          ret (TheGoal e :: r)
      | _ =>
          g <- goal_to_dyn g;
          let g := hnf g in
          raise (CantApply c g)
      end
    )) _ c.

Definition left : tactic := apply or_introl.

Definition ltac (t : string) (args : list Sig) : tactic := fun g=>
  d <- goal_to_dyn g;
  let ty := simpl (type d) in
  v <- @call_ltac ty t args;
  munify v (elem d);;
  ret [].

Require Import Coq.omega.Omega.
Definition omega := ltac "Coq.omega.Omega.omega" nil.

Module MCTacticsNotations.

Notation "t || u" := (OR t u).

Notation "'intro' x" := (intro_cont (fun x=>idtac)) (at level 40).
Notation "'intros' x .. y" :=
  (intro_cont (fun x=>.. (intro_cont (fun y=>idtac)) ..))
    (at level 0, x binder, y binder, right associativity).

Notation "'cintro' x '{-' t '-}'" := (intro_cont (fun x=>t)) (at level 0, right associativity).
Notation "'cintros' x .. y '{-' t '-}'" :=
  (intro_cont (fun x=>.. (intro_cont (fun y=>t)) ..))
    (at level 0, x binder, y binder, t at next level, right associativity).

Notation "a ;; b" := (@the_value _ _ _ a b _).

End MCTacticsNotations.