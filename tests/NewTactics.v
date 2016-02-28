Require Import MetaCoq.MetaCoq.
Import MetaCoqNotations.

Require Import MetaCoq.LtacEmu.
Import LtacEmuNotations.

Require Import Strings.String.

Require Import Lists.List.
Import ListNotations.

Inductive goal :=
| TheGoal : forall {A}, A -> goal
| AHyp : forall {A}, (A -> goal) -> goal.


Notation tactic := (goal -> M (list goal)).

Definition exact {A} (x:A) : tactic := fun g=>
  munify g (TheGoal x);; ret nil.

Definition run_tac {P} (t : tactic) : M P :=
  e <- evar P;
  t (TheGoal e);;
  ret e.

Goal True.
MProof.
  run_tac (exact I).
Qed.

Goal False.
MProof.
  Fail run_tac (exact I).
Abort.

Definition close_goals {A} (x:A) : list goal -> M (list goal) :=
  mmap (fun g'=>r <- abs x g'; ret (@AHyp A r)).

Definition mfilter {A} (b : A -> M bool) : list A -> M (list A) :=
  fix f l :=
    match l with
    | [] => ret []
    | x :: xs => bx <- b x; r <- f xs;
                 if bx then ret (x::r) else ret r
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

Definition CantCoerce : Exception. exact exception. Qed.

Definition to_goal d :=
  match d with
  | Dyn _ x => TheGoal x
  end.

Definition NotAVariable : Exception. exact exception. Qed.
Definition destruct {A : Type} (n : A) : tactic := fun g=>
  b <- is_var n;
  if negb b then raise NotAVariable
  else
    P <- evar (A->Type);
    let Pn := P n in
    l <- constrs A;
    l <- LtacEmu.mmap (fun d : dyn =>
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
    let l := hnf (List.map to_goal l) in
    ret l.

Definition reflexivity : tactic := fun g=>
  A <- evar Type;
  x <- evar A;
  munify g (TheGoal (eq_refl x));; ret nil.

Example fail_not_var : 0 = 0.
MProof.
  Fail run_tac (destruct 0).
Abort.

Require Import Unicoq.Unicoq.
Goal forall b : bool, b = b.
MProof.
  mintro b.
  run_tac (bbind (destruct b) [reflexivity; reflexivity]).
Qed.

Definition NotAProduct : Exception. exact exception. Qed.
Program Definition intro (n : string) : tactic := fun g=>
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

Require Import Bool.Bool.
Goal forall b1 : bool, b1 = b1.
MProof.
  run_tac (bbind (intro "b1") [reflexivity]).
Qed.

Definition idtac : tactic := fun g=>ret [g].

Definition bindb (t u:tactic) : tactic := fun g=>
  l <- t g;
  l <- filter_goals l;
  r <- mmap (open_and_apply u) l;
  let r := hnf List.concat _ r in
  ret r.


Goal forall b1 b2 b3 : bool, b1 && b2 && b3 = b3 && b2 && b1.
MProof.
  run_tac (bindb (intro "b1") (bindb (intro "b2") (intro "b3"))).
  (* something funky with the name of b1 is happening *)
  run_tac (bindb (destruct b1) (bindb (destruct b2) ((bindb (destruct b3) reflexivity)))).
Qed.


Program Definition intro_cont {A} (t: A->tactic) : tactic := fun g=>
  mmatch g return M list goal with
  | [? (P:A -> Type) e] @TheGoal (forall x:A, P x) e =>
    n <- get_name t;
    tnu n (fun x=>
      e' <- evar _;
      g <- abs x e';
      munify e g;;
      t x (TheGoal e') >> close_goals x)
  | _ => raise NotAProduct
  end.


Class semicolon {A} {B} {C} (t:A) (u:B) := SemiColon { the_value : C }.
Arguments SemiColon {A} {B} {C} t u the_value.
(*
Instance i_intro_cont A s t :
  semicolon (intro_cont (fun x:A=>idtac)) t | 0 :=
  SemiColon _ _ (intro_cont s t).
*)
Instance i_bbind (t:tactic) (l:list tactic) : semicolon t l | 100 :=
  SemiColon _ _ (bbind t l).

Instance i_bindb (t:tactic) (u:tactic) : semicolon t u | 100:=
  SemiColon _ _ (bindb t u).

Instance i_mtac A B (t:M A) (u:M B) : semicolon t u | 100 :=
  SemiColon _ _ (_ <- t; u).

Notation "a ;; b" := (@the_value _ _ _ a b _).
(* ;; is in right associativity, but it should be left, right? *)

Notation "'intro' x" := (intro_cont (fun x=>idtac)) (at level 40).
Goal forall b1 b2 b3 : bool, b1 && b2 && b3 = b3 && b2 && b1.
MProof.
  run_tac (intro b1 ;; intro b2 ;; intro b3).
  run_tac (destruct b1 ;; destruct b2 ;; destruct b3 ;; reflexivity).
Qed.

Notation "'cintro' x '{-' t '-}'" := (intro_cont (fun x=>t)) (at level 0, right associativity).

Notation "'cintros' x .. y '{-' t '-}'" := (intro_cont (fun x=>.. (intro_cont (fun y=>t)) ..))
(at level 0, x binder, y binder, t at next level, right associativity).

Goal forall b1 b2 b3 : bool, b1 && b2 && b3 = b3 && b2 && b1.
MProof.
  run_tac (cintros b1 b2 {-
    destruct b1 ;; destruct b2 ;;
    cintro b3 {- destruct b3 ;; reflexivity -}
   -}).
Qed.

Print Unnamed_thm4.

Goal forall b1 b2 b3 : bool, b1 && b2 && b3 = b3 && b2 && b1.
Proof.
  intro b1; intro b2; destruct b1; destruct b2; intro b3; destruct b3; reflexivity.
Qed.
Print Unnamed_thm5.

Definition NotAGoal : Exception. exact exception. Qed.
Definition get_goal : goal -> M dyn := fun g =>
  match g with
  | TheGoal d => ret (Dyn _ d)
  | _ => raise NotAGoal
  end.

Obligation Tactic := idtac.
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
          g <- get_goal g;
          let g := hnf g in
          raise (CantApply c g)
      end
    )) _ c.

Goal (forall x, x > 0) -> 3 > 0.
MProof.
  run_tac (intro H).
  run_tac (apply H).
Qed.

Goal (forall x, x > 0) -> 3 > 0.
MProof.
  run_tac (cintro H {- apply H -}).
Qed.

Definition NotAnOr : Exception. exact exception. Qed.
Definition left : tactic := apply or_introl.

Require Import Coq.omega.Omega.

Ltac omega' := omega.

Definition ltac (t : string) (args : list Sig) : tactic := fun g=>
  d <- get_goal g;
  let ty := simpl (type d) in
  v <- @call_ltac ty t args;
  munify v (elem d);;
  ret [].

Definition omega {A} := @call_ltac A "Top.omega'" nil.

Definition gomega := ltac "Coq.omega.Omega.omega" nil.

Goal (forall x y, x > y \/ y < x -> x <> y) -> 3 <> 0.
MProof.
  run_tac (cintro H {- apply H;; (left;; gomega) -}).
Qed.
