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
  oH <- munify A B;
  match oH with
  | Some H => retS (coerce_rect B H x)
  | _ => raise CantCoerce
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
  | Dyn x => TheGoal x
  end.

Definition goal_to_dyn : goal -> M dyn := fun g =>
  match g with
  | TheGoal d => ret (Dyn d)
  | _ => raise NotAGoal
  end.

Definition idtac : tactic := fun g=>ret [g].

Definition fail (e : Exception) : tactic := fun g=>raise e.

Definition unify_or_fail {A} (x y : A) : M (x = y) :=
  oeq <- munify x y;
  match oeq with
  | None => raise (NotUnifiable x y)
  | Some eq=> ret eq
  end.

Definition exact {A} (x:A) : tactic := fun g=>
  unify_or_fail (TheGoal x) g;; ret nil.

Definition reflexivity : tactic := fun g=>
  A <- evar Type;
  x <- evar A;
  unify_or_fail g (TheGoal (eq_refl x));; ret nil.

Definition tryt (t:tactic) : tactic := fun g=>
  mtry t g with _ => ret [g] end.

Definition OR (t u : tactic) : tactic := fun g=>
  mtry t g with _ => u g end.

Definition close_goals {A} (x:A) : list goal -> M (list goal) :=
  mmap (fun g'=>r <- abs x g'; ret (@AHyp A r)).

Definition NotAProduct : Exception. exact exception. Qed.


Definition intro_cont {A} (t: A->tactic) : tactic := fun g=>
  mmatch g return M list goal with
  | [? B (P:B -> Type) e] @TheGoal (forall x:B, P x) e =>
    unify_or_fail B A;; (* A might be an evar, so it will fail to match. therefore, we have to unify it later *)
    n <- get_binder_name t;
    tnu n None (fun x=>
      e' <- evar _;
      g <- abs x e';
      unify_or_fail e g;;
      x <- coerce x;
      let x := hnf x in
      t x (TheGoal e') >> close_goals x)
  | _ => raise NotAProduct
  end.

Definition intro_simpl (var: string) : tactic := fun g=>
  mmatch g with
  | [? B (P:B -> Type) e] @TheGoal (forall x:B, P x) e =>
    tnu var None (fun x=>
      e' <- evar _;
      g <- abs x e';
      unify_or_fail e g;;
      g' <- abs x (TheGoal e');
      ret [AHyp g'])
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
      x <- get_binder_name f;
      tnu x None (fun x : C=>
        open (f x) >> close_goals x)
    end.

Definition intros_all : tactic :=
  mfix1 f (g : goal) : M (list goal) :=
    open_and_apply (fun g =>
      mmatch g return M list goal with
      | [? T e] @TheGoal T e =>
        mtry
          xn <- get_binder_name T;
          r <- intro_simpl xn g;
          g <- hd_exception r;
          f g
        with _ =>
          ret [g]
        end
      end) g.

Definition NotSameSize (l : list tactic) (l' : list goal) : Exception. exact exception. Qed.
Fixpoint gmap (funs : list tactic) (ass : list goal) : M (list (list goal)) :=
  match funs, ass with
  | nil, nil => ret nil
  | f::funs', g::ass' =>
    fa <- open_and_apply f g;
    rest <- gmap funs' ass';
    ret (fa :: rest)
  | l, l' => raise (NotSameSize l l')
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


Definition SomethingNotRight {A} (t : A) : Exception. exact exception. Qed.
Definition copy_ctx {A} (B : A -> Type) :=
  mfix1 rec (d : dyn) : M Type :=
    mmatch d with
    | [? c : A] {| elem := c |} =>
        ret (B c)
    | [? C (D : C -> Type) (c : forall y:C, D y)] {| elem := c |} =>
        nu y : C,
        r <- rec (Dyn (c y));
        pabs y r
    | [? C D (c : C->D)] {| elem := c |} =>
        nu y : C,
        r <- rec (Dyn (c y));
        pabs y r
    | _ => print_term A;; raise (SomethingNotRight d)
    end.

Definition hyps_except {A} (x : A) :=
  l <- hypotheses;
  mfilter (fun y=>mmatch y with
    | [? b] ahyp x b => ret false
    | _ => ret true
    end) l.

Definition find_hyp_index {A} (x : A) :=
  l <- hypotheses;
  mindex_of (fun y=>mmatch y with
    | [? b] ahyp x b => ret true
    | _ => ret false
    end) l.

Definition type_of {A} (x:A) := A.

Fixpoint but_last {A} (l : list A) :=
  match l with
  | [] => []
  | [a] => []
  | (a :: ls) => a :: but_last ls
  end.

Definition generalize1 (cont: tactic) : tactic := fun g=>
  P <- goal_type g;
  l <- hypotheses;
  ft <- hd_exception l;
  let (A, x, _) := ft in
  aP <- pabs x P; (* aP = (forall x:A, P) *)
  e <- Cevar aP (List.tl l);
  mmatch aP with
  | [? Q : A -> Type] (forall z:A, Q z) => [H]
    let e' := match H in _ = Q return Q with
      | eq_refl => e
      end
    in
    oeq <- munify g (@TheGoal (Q x) (e' x));
    match oeq with
    | Some _ => MetaCoq.remove x (cont (TheGoal e))
    | _ => raise exception
    end
  | _ => raise exception
  end.

(* if I have a goal (P; ?e) and a number n, I want to
   create a new goal (forall x_1, ..., x_n=>P; ?e')
   so ?e should be instantiated with ?e' x_1 ... x_n *)
(*
Definition abstract_up_to n : tactic := fun g=>
  l <- hypotheses;
  P <- goal_type g;
  pP <- productify_up_to (Dyn P) n l;
  let l' := hnf (skipn n l) in
  e <- Cevar pP l';
*)


Definition NotAVariable : Exception. exact exception. Qed.
Definition destruct {A : Type} (n : A) : tactic := fun g=>
  b <- is_var n;
  if negb b then raise NotAVariable
  else
    ctx <- hyps_except n;
    P <- Cevar (A->Type) ctx;
    let Pn := P n in
    gT <- goal_type g;
    unify_or_fail Pn gT;;
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
    unify_or_fail (@TheGoal Pn d) g;;
    let l := hnf (List.map dyn_to_goal l) in
    ret l.

Local Obligation Tactic := idtac.

Definition CantApply {T1 T2} (x:T1) (y:T2) : Exception. exact exception. Qed.

Definition apply {T} (c : T) : tactic := fun g=>
  (mfix2 app (U : Type) (d : U) : M (list goal) :=
    oeq <- munify (TheGoal d) g;
    match oeq with
    | Some _ => ret []
    | None =>
      mmatch U return M (list goal) with
      | [? (T1 : Type) (T2 : T1 -> Type)] (forall x:T1, T2 x) => [H]
          e <- evar T1;
          let d := match H in (_ = x) return x with
          | eq_refl => d
          end in
          r <- app (T2 e) (d e);
          ret (TheGoal e :: r)
      | _ =>
          g <- goal_type g;
          raise (CantApply c g)
      end
    end
    ) _ c.

Definition transitivity {B : Type} (y : B) : tactic :=
  apply (fun x => @eq_trans B x y).

Definition symmetry : tactic :=
  apply eq_sym.

Definition CantFindConstructor : Exception. exact exception. Qed.
Definition ConstructorsStartsFrom1 : Exception. exact exception. Qed.

Definition constructor (n : nat) : tactic := fun g=>
  A <- goal_type g;
  match n with
  | 0 => raise ConstructorsStartsFrom1
  | S n =>
      l <- constrs A;
      match nth_error l n with
        | Some x => apply (elem x) g
        | None => fail CantFindConstructor g
      end
  end.

Definition Not1Constructor : Exception. exact exception. Qed.

Definition split : tactic := fun g=>
  A <- goal_type g;
  l <- constrs A;
  match l with
  | [_] =>  constructor 1 g
  | _ => raise Not1Constructor
  end.

Definition Not2Constructor : Exception. exact exception. Qed.

Definition left : tactic := fun g=>
  A <- goal_type g;
  l <- constrs A;
  match l with
  | [x; _] => apply (elem x) g
  | _ => raise Not2Constructor
  end.

Definition right : tactic := fun g=>
  A <- goal_type g;
  l <- constrs A;
  match l with
  | [_; x] => apply (elem x) g
  | _ => raise Not2Constructor
  end.

Inductive goal_pattern : Type :=
| gbase : forall {A}, A -> tactic -> goal_pattern
| gtele : forall {C}, (C -> goal_pattern) -> goal_pattern.

Notation "[[ x .. y |- ps ] ] => t" :=
  (gtele (fun x=> .. (gtele (fun y=>gbase ps t)).. ))
  (at level 202, x binder, y binder, ps at next level) : goal_match_scope.
Delimit Scope goal_match_scope with goal_match.

Definition jmeq {A} {B} (x:A) (y:B) : M bool :=
  teq <- munify A B;
  match teq with
  | Some e =>
    let x := match e in _ = B with eq_refl => x end in
    veq <- munify x y;
    match veq with
    | Some _ => ret true
    | None => ret false
    end
  | None => ret false
  end.

Definition DoesNotMatchGoal : Exception. exact exception. Qed.

Fixpoint match_goal' (p : goal_pattern) (l : list Hyp) : tactic := fun g=>
  match p, l with
  | gbase P t, _ =>
    gty <- goal_type g;
    beq <- jmeq P gty;  (* actually, we want a match with reduction here *)
    if beq then t g
    else fail DoesNotMatchGoal g
  | @gtele C f, (@ahyp A a None :: l) =>
    teq <- munify C A; (* same here *)
    match teq with
    | Some eq =>
      e <- evar C;
      let e' := match eq with eq_refl => e end in
      munify e' a;;
      mtry match_goal' (f e) l g
      with DoesNotMatchGoal =>
        match_goal' p l g
      end
    | None => match_goal' p l g end
  | _, _ => raise DoesNotMatchGoal
  end.

Definition match_goal p : tactic := fun g=>
  r <- hypotheses; let r := simpl (List.rev r) in match_goal' p r g.
Arguments match_goal p%goal_match _.


Definition assumption : tactic := fun g=>
  P <- goal_type g;
  match_goal ([[ x:P |- P ]] => exact x) g.

Definition ltac (t : string) (args : list dyn) : tactic := fun g=>
  d <- goal_to_dyn g;
  let ty := simpl (type d) in
  v <- @call_ltac ty t args;
  let (v, l) := v in
  unify_or_fail v (elem d);;
  b <- is_evar v;
  if b then
    ret [TheGoal v] (* it wasn't solved *)
  else
    ret (List.map dyn_to_goal l).

Require Import Coq.omega.Omega.
Definition omega := ltac "Coq.omega.Omega.omega" nil.

Definition option_to_bool {A} (ox : option A) :=
  match ox with Some _ => true | _ => false end.

Definition destruct_all (T : Type) : tactic := fun g=>
  l <- hypotheses;
  l <- mfilter (fun h:Hyp=>
    let (Th, _, _) := h in
    r <- munify Th T;
    ret (option_to_bool r)) l;
  (fix f (l : list Hyp) : tactic :=
    match l with
    | [] => idtac
    | (ahyp x _ :: l) => @the_value _ _ _ (destruct x) (f l) _
    end) l g.


Definition treduce (r : Reduction) : tactic := fun g=>
  T <- goal_type g;
  let T := reduce r T in
  e <- evar T;
  let e := TheGoal e in
  munify g e;;
  ret [e].

Definition NotThatType : Exception. exact exception. Qed.
Definition typed_intro (T : Type) : tactic := fun g=>
  U <- goal_type g;
  mmatch U with
  | [? P:T->Type] forall x:T, P x =>
    xn <- get_binder_name U;
    intro_simpl xn g
  | _ => raise NotThatType
  end.

Definition typed_intros (T : Type) : tactic := fun g=>
  (mfix1 f (g : goal) : M _ :=
    mtry
      (bindb (typed_intro T) f) g
    with NotThatType =>
      idtac g
    end) g.
(*
Definition pose {A} (t: A) (cont: A -> tactic) : tactic := fun g=>
  n <- get_binder_name cont;
  tnu_let t (fun x=>
    r <- cont x g;
    abs_let x
*)
Module MCTacticsNotations.

Notation "t || u" := (OR t u).

(* We need a fresh evar to be able to use intro with ;; *)
Notation "'intro' x" :=
  ((fun g=>T <- evar Type; @intro_cont T (fun x=>idtac) g) : tactic) (at level 40).
Notation "'intros' x .. y" :=
  (intro_cont (fun x=>.. (intro_cont (fun y=>idtac)) ..))
    (at level 0, x binder, y binder, right associativity).
Notation "'intros'" := (intros_all).

Notation "'cintro' x '{-' t '-}'" := (intro_cont (fun x=>t)) (at level 0, right associativity).
Notation "'cintros' x .. y '{-' t '-}'" :=
  (intro_cont (fun x=>.. (intro_cont (fun y=>t)) ..))
    (at level 0, x binder, y binder, t at next level, right associativity).

Notation "a ;; b" := (@the_value _ _ _ a b _).

Notation "'simpl'" := (treduce RedSimpl).
Notation "'hnf'" := (treduce RedWhd).
End MCTacticsNotations.
