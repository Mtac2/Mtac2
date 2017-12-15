Require Import Strings.String.
From Mtac2 Require Export Base.
From Mtac2 Require Import Logic Datatypes List Utils Logic Abstract.
Import M.notations.
Import Mtac2.List.ListNotations.

Require Import Strings.String.
Require Import NArith.BinNat.
Require Import NArith.BinNatDef.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

(** Exceptions *)
Eval hnf in new exception NoGoalsLeft.
Eval hnf in new exception NotSameSize.
Eval hnf in new exception NotAProduct.
Eval hnf in new exception CantFindConstructor.
Eval hnf in new exception ConstructorsStartsFrom1.
Eval hnf in new exception Not1Constructor.
Eval hnf in new exception Not2Constructor.
Eval hnf in new exception DoesNotMatchGoal.
Eval hnf in new exception NoPatternMatchesGoal.
Eval hnf in new exception NotThatType.
Eval hnf in new exception NoProgress.

Definition SomethingNotRight {A} (t : A) : Exception. exact exception. Qed.

Definition CantApply {T1 T2} (x:T1) (y:T2) : Exception. exact exception. Qed.

Set Printing Universes.
Import ProdNotations.
Set Printing All.
(** The type for tactics *)
Definition gtactic@{H I J L1 L2 M M1 M2} (A : Type@{I}) := goal@{L1 L2} -> M@{H I J} (mlist@{I} (mprod@{I M} A goal@{M1 M2})).
Definition tactic := gtactic unit.

Delimit Scope tactic_scope with tactic.
Bind Scope tactic_scope with gtactic.

Module T.
Definition with_goal {A} (f : goal -> M A) := fun g =>
  y <- f g; M.ret [m: (m: y,g)].

Coercion of_M {A} (x : M A) : gtactic A := with_goal (fun _ => x).

Definition mtry' {A} (t : gtactic A)
    (f : Exception -> gtactic A) : gtactic A := fun g =>
  M.mtry' (t g) (fun e => f e g).

Definition raise {A} (e : Exception) : gtactic A := M.raise e.

Definition fix0 (B : Type) : (gtactic B -> gtactic B) -> gtactic B :=
  @M.fix1 goal (fun _ => mlist (B *m goal)).

Definition fix1 {A} (B : A -> Type) :
    ((forall x : A, gtactic (B x)) -> (forall x : A, gtactic (B x))) ->
    forall x : A, gtactic (B x) :=
  @M.fix2 A (fun _ => goal) (fun x _ => mlist (B x *m goal)).

Definition fix2 {A1} {A2 : A1 -> Type} (B : forall a1 : A1, A2 a1 -> Type) :
    ((forall (x1 : A1) (x2 : A2 x1), gtactic (B x1 x2)) ->
      forall (x1 : A1) (x2 : A2 x1), gtactic (B x1 x2)) ->
    forall (x1 : A1) (x2 : A2 x1), gtactic (B x1 x2) :=
  @M.fix3 A1 A2 (fun _ _ => goal) (fun x y _ => mlist (B x y *m goal)).

Definition fix3 {A1} {A2 : A1 -> Type} {A3 : forall a1 : A1, A2 a1 -> Type}
  (B : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type) :
    ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), gtactic (B x1 x2 x3)) ->
      forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), gtactic (B x1 x2 x3)) ->
    forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), gtactic (B x1 x2 x3) :=
  @M.fix4 A1 A2 A3 (fun _ _ _ => goal) (fun x y z _ => mlist (B x y z *m goal)).

Definition fix4 {A1} {A2 : A1 -> Type} {A3 : forall a1 : A1, A2 a1 -> Type}
    {A4 : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type}
    (B : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2), A4 a1 a2 a3 -> Type) :
    ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), gtactic (B x1 x2 x3 x4)) ->
      forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), gtactic (B x1 x2 x3 x4)) ->
    forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), gtactic (B x1 x2 x3 x4) :=
  @M.fix5 A1 A2 A3 A4 (fun _ _ _ _ => goal) (fun x y z z' _ => mlist (B x y z z' *m goal)).

Fixpoint pattern_map {A} {B : A -> Type} (g : goal) (y : A)
    (p : pattern gtactic A B y) : pattern M A (fun y => mlist (B y *m goal)) y :=
  match p with
  | pbase x f r => pbase x (fun Heq => f Heq g) r
  | ptele f => ptele (fun x => pattern_map g y (f x))
  end.

Definition mmatch' {A P} (y : A)
    (ps : mlist (pattern gtactic A P y)) : gtactic (P y) := fun g =>
  M.mmatch' y (mmap (pattern_map g y) ps).

Definition ret {A} (x : A) : gtactic A := fun g => M.ret [m:(m: x,g)].
Definition idtac : tactic := ret tt.

Definition try (t : tactic) : tactic := fun g=>
  mtry t g with _ => M.ret [m:(m: tt, g)] end.

Definition or {A} (t u : gtactic A) : gtactic A := fun g=>
  mtry t g with _ => u g end.

Definition get_binder_name {A} (x : A) : gtactic string := fun g =>
  s <- M.get_binder_name x; M.ret [m:(m: s,g)].

(** [close_goals x l] takes the list of goals [l] and appends
    hypothesis [x] to each of them. *)
Definition close_goals {A B} (y : B) : mlist (A *m goal) -> M (mlist (A *m goal)) :=
  M.map (fun '(m: x,g') => r <- M.abs_fun y g'; M.ret (m: x, @AHyp B mNone r)).

(** [let_close_goals x l] takes the list of goals [l] and appends
    hypothesis [x] with its definition to each of them (it assumes it is defined). *)
Definition let_close_goals {A B} (y : B) : mlist (A *m goal) -> M (mlist (A *m goal)) :=
  let t := rone_step y in (* to obtain x's definition *)
  M.map (fun '(m: x,g') => r <- M.abs_fun y g'; M.ret (m: x, @AHyp B (mSome t) r)).

(** [rem_hyp x l] "removes" hypothesis [x] from the list of goals [l]. *)
Definition rem_hyp {A B} (x : B) (l: mlist (A *m goal)) : M (mlist (A *m goal)) :=
  let v := dreduce (@mmap) (mmap (fun '(m: y,g) => (m: y, HypRem x g)) l) in M.ret v.

(** Returns if a goal is open, i.e., a meta-variable. *)
Fixpoint is_open (g : goal) : M bool :=
  match g with
  | Goal e => M.is_evar e
  | @AHyp C _ f =>
    x <- M.fresh_binder_name f;
    (* we get the name in order to avoid inserting existing names
      (nu will raise an exception otherwise) *)
    M.nu x mNone (fun x : C => is_open (f x))
  | HypRem _ g => is_open g (* we don't care about the variable *)
  end.

(** removes the goals that were solved *)
Definition filter_goals {A} : mlist (A *m goal) -> M (mlist (A *m goal)) :=
  M.filter (fun '(m: x,g) => is_open g).

(** [open_and_apply t] is a tactic that "opens" the current goal
    (pushes all the hypotheses in the context) and applies tactic [t]
    to the so-opened goal. The result is "closed" back. *)
Definition open_and_apply {A} (t : gtactic A) : gtactic A :=
  fix open g :=
    match g return M _ with
    | Goal _ => t g
    | @AHyp C mNone f =>
      x <- M.fresh_binder_name f;
      M.nu x mNone (fun x : C =>
        open (f x) >>= close_goals x)
    | @AHyp C (mSome t) f =>
      x <- M.fresh_binder_name f;
      M.nu x (mSome t) (fun x : C =>
        open (f x) >>= let_close_goals x)
    | HypRem x f =>
      M.remove x (open f) >>= rem_hyp x
    end.

Definition bind {A B} (t : gtactic A) (f : A -> gtactic B) : gtactic B := fun g =>
  r <- M.map (fun '(m: x,g') => open_and_apply (f x) g') =<< t g;
  let res := dreduce (@mconcat, mapp) (mconcat r) in
  filter_goals res.

Definition fmap {A B} (f : A -> B) (x : gtactic A) : gtactic B :=
  bind x (fun a => ret (f a)).
Definition fapp {A B} (f : gtactic (A -> B)) (x : gtactic A) : gtactic B :=
  bind f (fun g => fmap g x).

Class Seq (A B C : Type) :=
  seq : gtactic A -> C -> gtactic B.
Arguments seq {A B C _} _%tactic _%tactic.

Instance seq_one {A B} : Seq A B (gtactic B) := fun t1 t2 => bind t1 (fun _ => t2).

Fixpoint gmap {A} (tacs : mlist (gtactic A)) (gs : mlist goal) : M (mlist (mlist (A *m goal))) :=
  match tacs, gs with
  | [m:], [m:] => M.ret [m:]
  | tac :m: tacs', g :m: gs' => mcons <$> open_and_apply tac g <*> gmap tacs' gs'
  | l, l' => M.raise NotSameSize
  end.

Instance seq_list {A B} : Seq A B (mlist (gtactic B)) := fun t f g =>
  gs <- filter_goals =<< t g;
  ls <- gmap f (mmap msnd gs);
  let res := dreduce (@mconcat, mapp) (mconcat ls) in
  filter_goals res.

Definition exact {A} (x:A) : tactic := fun g =>
  match g with
  | Goal g => M.cumul_or_fail UniCoq x g;; M.ret [m:]
  | _ => M.raise NotAGoal
  end.

Definition eexact {A} (x:A) : tactic := fun g =>
  match g with
  | Goal g =>
    M.cumul_or_fail UniCoq x g;;
    l <- M.collect_evars g;
    let red := dreduce (@mmap, M.dyn_to_goal) (mmap (fun d => (m: tt, M.dyn_to_goal d)) l) in
    M.ret red
  | _ => M.raise NotAGoal
  end.

Definition goal_type : gtactic Type := with_goal M.goal_type.

(** [intro_base n t] introduces variable or definition named [n]
    in the context and executes [t n].
    Raises [NotAProduct] if the goal is not a product or a let-binding. *)
Definition intro_base {A B} (var : string) (t : A -> gtactic B) : gtactic B := fun g =>
  mmatch g return M (mlist (B *m goal)) with
  | [? B (def: B) P e] @Goal (let x := def in P x) e =n>
    (* normal match will not instantiate meta-variables from the scrutinee, so we do the inification here*)
    eqBA <- M.unify_or_fail UniCoq B A;
    M.nu var (mSome def) (fun x=>
      let Px := reduce (RedWhd [rl:RedBeta]) (P x) in
      e' <- M.evar Px;
      nG <- M.abs_let (P:=P) x def e';
      exact nG g;;
      let x := reduce (RedWhd [rl:RedMatch]) (match eqBA with meq_refl => x end) in
      t x (Goal e') >>= let_close_goals x)
  | [? P e] @Goal (forall x:A, P x) e =u>
    M.nu var mNone (fun x=>
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
  M.ret (msnd res).

(** Introduces all hypotheses. Does not fail if there are 0. *)
Definition intros_all : tactic :=
  mfix1 f (g : goal) : M (mlist (unit *m goal)) :=
    open_and_apply (fun g =>
      match g return M (mlist (unit *m goal)) with
      | @Goal T e =>
        mtry intro_anonymous T M.ret g >>= f with
        | WrongTerm => M.ret [m:(m: tt,g)]
        | NotAProduct => M.ret [m:(m: tt,g)]
        | [? s] NameExistsInContext s => intro_anonymous T M.fresh_name g >>= f
        end
      | _ => M.raise NotAGoal
      end) g.

(** Introduces up to n binders. Throws [NotAProduct] if there
    aren't enough products in the goal.  *)
Definition introsn : nat -> tactic :=
  mfix2 f (n : nat) (g : goal) : M (mlist (unit *m goal)) :=
    open_and_apply (fun g =>
      match n, g with
      | 0, g => M.ret [m:(m: tt,g)]
      | S n', @Goal T e =>
        mtry intro_anonymous T M.ret g >>= f n' with
        | WrongTerm => M.raise NotAProduct
        | [? s] NameExistsInContext s => intro_anonymous T M.fresh_name g >>= f n'
        end
      | _, _ => M.failwith "introsn"
      end) g.

(** Applies reflexivity *)
Definition prim_reflexivity : tactic := fun g =>
  A <- M.evar Type;
  x <- M.evar A;
  M.unify_or_fail UniCoq g (Goal (Coq.Init.Logic.eq_refl x));; M.ret [m:].

(** Fist introduces the hypotheses and then applies reflexivity *)
Definition reflexivity : tactic := fun g =>
  l <- intros_all g;
  g <- M.hd l;
  open_and_apply prim_reflexivity (msnd g).

(** Overloaded binding *)
Definition copy_ctx {A} (B : A -> Type) : dyn -> M Type :=
  mfix1 rec (d : dyn) : M Type :=
    mmatch d with
    | [? c : A] Dyn c =>
      let Bc := reduce (RedWhd [rl:RedBeta]) (B c) in
      M.ret Bc
    | [? C (D : C -> Type) (c : forall y:C, D y)] Dyn c =>
      n <- M.fresh_binder_name c;
      M.nu n mNone (fun y=>
        r <- rec (Dyn (c y));
        M.abs_prod y r)
    | [? C D (c : C->D)] Dyn c =>
      n <- M.fresh_binder_name c;
      M.nu n mNone (fun y=>
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
      rcbv match H in _ =m= Q return Q with meq_refl _ => e end in
    exact (e' x) g;;
    M.ret [m:(m: tt, Goal e)]
  | _ => M.failwith "generalize"
  end.

(** Clear hypothesis [x] and continues the execution on [cont] *)
Definition cclear {A B} (x:A) (cont : gtactic B) : gtactic B := fun g=>
  gT <- M.goal_type g;
  ''(e,l) <- M.remove x (
    e <- M.evar gT;
    l <- cont (Goal e);
    M.ret (e, l));
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
  M.unify_or_fail UniCoq Pn gT;;
  l <- M.constrs A;
  l <- M.map (fun d : dyn =>
    (* a constructor c has type (forall x, ... y, A) and we return
       (forall x, ... y, P (c x .. y)) *)
    t' <- copy_ctx P d;
    e <- M.Cevar t' ctx;
    M.ret {| elem := e |}) (msnd l);
  let c := {| case_ind := A;
              case_val := n;
              case_return := {| elem := P |};
              case_branches := l
           |} in
  case <- M.makecase c;
  case <- M.unfold_projection (elem case);
  exact case g;;
  let res := dreduce (@mmap, M.dyn_to_goal)
                     (mmap (fun d => (m: tt, M.dyn_to_goal d)) l) in
  M.ret res.

(** Destructs the n-th hypotheses in the goal (counting from 0) *)
Definition destructn (n : nat) : tactic :=
  bind (introsn n) (fun _ g =>
    A <- M.evar Type;
    n <- M.fresh_name "tmp";
    @intro_base A _ n destruct g).

(** [apply t] applies theorem t to the current goal.
    It generates a subgoal for each hypothesis in the theorem.
    If the hypothesis is introduced by a dependent product (a forall),
    then no subgoal is generated. If it isn't dependent (a ->), then
    it is included in the list of next subgoals. *)
Definition apply {T} (c : T) : tactic := fun g=>
  match g with Goal eg =>
    (mfix1 go (d : dyn) : M (mlist (unit *m goal)) :=
      let (_, el) := d in
      mif M.cumul UniCoq el eg then M.ret [m:] else
        mmatch d return M (mlist (unit *m goal)) with
        | [? T1 T2 f] @Dyn (T1 -> T2) f =>
          e <- M.evar T1;
          r <- go (Dyn (f e));
          M.ret ((m: tt, Goal e) :m: r)
        | [? T1 T2 f] @Dyn (forall x:T1, T2 x) f =>
          e <- M.evar T1;
          r <- go (Dyn (f e));
          M.ret r
        | _ =>
          gT <- M.goal_type g;
          M.raise (CantApply T gT)
        end) (Dyn c)
  | _ => M.raise NotAGoal
  end.

Definition apply_ : tactic := fun g =>
  match g with
  | @Goal G g =>
     x <- M.solve_typeclass_or_fail G; M.cumul_or_fail UniCoq x g;; M.ret [m:]
  | _ => M.raise NotAGoal
  end.

(** Given a list of dyn's, it applies each of them until one
succeeds. Throws NoProgress if none apply *)
Definition apply_one_of (l : mlist dyn) : tactic :=
  mfold_left (fun a '(Dyn e) => or a (apply e)) l (T.raise NoProgress).

(** Tries to apply each constructor of the goal type *)
Definition constructor : tactic := fun g=>
  ''(m: _, l) <- M.constrs =<< M.goal_type g;
  apply_one_of l g.


Definition change (P : Type) : tactic := fun g =>
  gT <- M.goal_type g;
  e <- M.evar P;
  exact e g;;
  M.ret [m:(m: tt, Goal e)].

Inductive goal_pattern (B : Type) : Prop :=
  | gbase : forall {A}, A -> gtactic B -> goal_pattern B
  | gbase_context : forall {A}, A -> ((A -> Type) -> gtactic B) -> goal_pattern B
  | gtele : forall {C}, (C -> goal_pattern B) -> goal_pattern B
  | gtele_evar : forall {C}, (C -> goal_pattern B) -> goal_pattern B.
Arguments gbase {B A} _ _.
Arguments gbase_context {B A} _ _.
Arguments gtele {B C} _.
Arguments gtele_evar {B C} _.

Definition match_goal_context
    {C A B} (x: A) (y: B) (cont: (A -> B) -> gtactic C) : gtactic C := fun g=>
  r <- abstract x y;
  let reduced := dreduce (fu) (fu r) in
  cont reduced g.

Fixpoint match_goal_pattern' {B}
    (u : Unification) (p : goal_pattern B) : mlist Hyp -> mlist Hyp -> gtactic B :=
  fix go l1 l2 g :=
  match p, l2 with
  | gbase P t, _ =>
    gT <- M.goal_type g;
    mif M.cumul u P gT then t g
    else M.raise DoesNotMatchGoal
  | gbase_context x t, _ =>
    gT <- M.goal_type g;
    match_goal_context x gT t g
  | @gtele _ C f, @ahyp A a d :m: l2' =>
    oeqCA <- M.unify C A u;
    match oeqCA with
    | mSome eqCA =>
      let a' := rcbv match meq_sym eqCA with meq_refl => a end in
      mtry match_goal_pattern' u (f a') [m:] (mrev_append l1 l2') g
      with DoesNotMatchGoal =>
        go (ahyp a d :m: l1) l2' g
      end
    | mNone => go (ahyp a d :m: l1) l2' g end
  | @gtele_evar _ C f, _ =>
    e <- M.evar C;
    match_goal_pattern' u (f e) l1 l2 g
  | _, _ => M.raise DoesNotMatchGoal
  end.

Definition match_goal_pattern {B} (u : Unification)
    (p : goal_pattern B) : gtactic B := fun g=>
  r <- M.hyps; match_goal_pattern' u p [m:] (mrev' r) g.

Fixpoint match_goal_base {B} (u : Unification)
    (ps : mlist (goal_pattern B)) : gtactic B := fun g =>
  match ps with
  | [m:] => M.raise NoPatternMatchesGoal
  | p :m: ps' =>
    mtry match_goal_pattern u p g
    with DoesNotMatchGoal => match_goal_base u ps' g end
  end.

Definition ltac (t : string) (args : mlist dyn) : tactic := fun g =>
  ''(@Dyn ty el) <- M.goal_to_dyn g;
  ''(m: v, l) <- @M.call_ltac ty t args;
  M.unify_or_fail UniCoq v el;;
  mif M.is_evar v then
    M.ret [m:(m: tt, Goal v)] (* it wasn't solved *)
  else
    let l' := dreduce (@mmap) (mmap (mpair tt) l) in
    M.ret l'.

Definition destruct_all (T : Type) : tactic := fun g=>
  l <- M.filter (fun '(@ahyp Th _ _) =>
    r <- M.unify Th T UniCoq;
    M.ret (option_to_bool r)) =<< M.hyps;
  (fix f (l : mlist Hyp) : tactic :=
    match l with
    | [m:] => idtac
    | ahyp x _ :m: l => bind (destruct x) (fun _ => f l)
    end) l g.

Definition treduce (r : Reduction) : tactic := fun g=>
  T <- M.goal_type g;
  let T' := reduce r T in
  e <- M.evar T';
  mif M.cumul UniMatch g (@Goal T e) then M.ret [m:(m: tt, Goal e)]
  else M.failwith "treduce".

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

(** changes a hypothesis H with one of type Q and the same name *)
Definition change_hyp {P Q} (H : P) (newH: Q) : tactic := fun g=>
  name <- M.get_binder_name H;
  gT <- M.goal_type g;
  ''(m: gabs, abs) <- M.remove H (M.nu name mNone (fun nH: Q=>
     r <- M.evar gT;
     abs <- M.abs_fun nH r;
     gabs <- M.abs_fun nH (Goal r);
     M.ret (m: AHyp mNone gabs, abs)));
  exact (abs newH) g;;
  M.ret [m:(m: tt, gabs)].

Definition cassert_with_base {A B} (name : string) (t : A)
    (cont : A -> gtactic B) : gtactic B := fun g =>
  M.nu name (mSome t) (fun x=>
    gT <- M.goal_type g;
    r <- M.evar gT;
    value <- M.abs_fun x r;
    exact (value t) g;;
    close_goals x =<< cont x (Goal r)).

Definition cpose_base {A B} (name : string) (t : A)
    (cont : A -> gtactic B) : gtactic B := fun g =>
  M.nu name (mSome t) (fun x=>
    gT <- M.goal_type g;
    r <- M.evar gT;
    value <- M.abs_let x t r;
    exact value g;;
    let_close_goals x =<< cont x (Goal r)).

Definition cpose {A} (t: A) (cont : A -> tactic) : tactic := fun g =>
  n <- M.get_binder_name cont;
  cpose_base n t cont g.

Definition cassert_base {A} (name : string)
    (cont : A -> tactic) : tactic := fun g =>
  a <- M.evar A; (* [a] will be the goal to solve [A] *)
  M.nu name mNone (fun x =>
    gT <- M.goal_type g;
    r <- M.evar gT; (* The new goal now referring to n *)
    value <- M.abs_fun x r;
    exact (value a) g;; (* instantiate the old goal with the new one *)
    v <- cont x (Goal r) >>= close_goals x;
    M.ret ((m: tt,Goal a) :m: v)). (* append the goal for a to the top of the goals *)

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
  M.ret [m:(m: tt,Goal ut)| (m: tt,Goal u)].

(* performs simpl in each hypothesis and in the goal *)
Definition simpl_in_all : tactic := fun g =>
  l <- M.fold_right (fun (hyp : Hyp) hyps =>
    let (A, x, ot) := hyp in
    let A := rsimpl A in
    M.ret (@ahyp A x ot :m: hyps)
  ) [m:] =<< M.hyps;
  T <- M.goal_type g;
  let T := rsimpl T in
  e <- M.Cevar T l; (* create the new goal in the new context *)
  (* we need normal unification since g might be a compound value *)
  oeq <- M.unify g (Goal e) UniCoq;
  match oeq with
  | mSome (meq_refl _) => M.ret [m:(m: tt,Goal e)]
  | _ => M.raise exception (* should never happen *)
  end.

Definition reduce_in (r : Reduction) {P} (H : P) : tactic := fun g =>
  l' <- M.map (fun '(@ahyp T v def) =>
    mif M.cumul UniMatchNoRed H v then
      let T' := reduce r T in M.ret (@ahyp T' v def)
    else M.ret (ahyp v def)) =<< M.hyps;
  gT <- M.goal_type g;
  e <- M.Cevar gT l';
  oeq <- M.unify (Goal e) g UniCoq;
  match oeq with
  | mSome (meq_refl _) => M.ret [m:(m: tt,Goal e)]
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
  | mSome (meq_refl _) => M.ret [m:(m: tt,Goal e)]
  | _ => M.raise (NotUnifiable g (Goal (@ex_intro _ P x e)))
  end.

Definition eexists: tactic := fun g=>
  T <- M.evar Type;
  e <- M.evar T;
  l <- mexists e g;
  let res := dreduce (@mapp) (l +m+ [m:(m: tt, Goal e)]) in
  M.ret res.

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
         M.nu name mNone (fun x:B =>
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
  ''(f, new_goal) <- M.nu f mNone (fun f : gT =>
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
    M.ret (fixp, AHyp mNone new_goal)
  );
  exact f g;;
  M.ret [m:(m: tt,new_goal)].

Definition progress {A} (t : gtactic A) : gtactic A := fun g =>
  r <- t g;
  match r with
  | [m:(m: x,g')] =>
    mmatch g with
    | g' => M.raise NoProgress
    | _ => M.ret [m:(m: x,g')]
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
    | [m:(m: _,g')] =>
      mmatch g with
      | g' => M.ret [m:(m: tt,g)] (* the goal is the same, return *)
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
      M.nu n mNone (fun x : B =>
        d1 <- rec (Dyn (a x));
        M.abs_fun x d1)
    | [? B (A: B -> Type) a] Dyn (forall x:B, a x) =n>
      n <- M.get_binder_name el;
      M.nu n mNone (fun x : B =>
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
  M.ret [m:(m: tt,Goal e)].

Definition unfold {A} (x : A) : tactic := fun g =>
  gT <- M.goal_type g;
  let gT' := dreduce (x) gT in
  ng <- M.evar gT';
  exact ng g;;
  M.ret [m:(m: tt, Goal ng)].

Definition unfold_in {A B} (x : A) (h : B) : tactic :=
  reduce_in (RedStrong [rl:RedBeta; RedMatch; RedFix; RedDeltaOnly [rl:Dyn x]]) h.

Fixpoint intros_simpl (l : list string) : tactic :=
  match l with
  | nil => idtac
  | n :: l => bind (intro_simpl n) (fun _ => intros_simpl l)
  end%list.

Fixpoint name_pattern (l : list (list string)) : mlist tactic :=
  match l with
  | nil => [m:]
  | ns :: l => intros_simpl ns :m: name_pattern l
  end%list.

(** Type for goal manipulation primitives *)
Definition selector A := mlist (A *m goal) -> M (mlist (A *m goal)).

Instance tactic_selector A : Seq A A (selector A) := fun t s g =>
  l <- t g;
  filter_goals l >>= s.

Module S.
  Definition nth {A} (n : nat) (t : gtactic A) : selector A := fun l =>
    let (l1, l2) := dreduce (@nsplit) (nsplit n l) in
    match mhd_error l2 with
    | mNone => M.raise NoGoalsLeft
    | mSome (m: _, g) =>
      goals <- open_and_apply t g;
      let res := dreduce (@mapp, @mtl) (l1 +m+ goals +m+ mtl l2) in
      filter_goals res
    end.

  Definition last {A} (t : gtactic A) : selector A := fun l =>
    let n := dreduce (pred, mlength) (pred (mlength l)) in
    nth n t l.

  Definition first {A} (t : gtactic A) : selector A := nth 0 t.

  Definition rev {A} : selector A := fun l =>
    let res := dreduce (@mrev', @mrev_append, @mapp) (mrev' l) in M.ret res.
End S.

Module notations.
  Open Scope tactic_scope.

  (* This notation makes sure that [t] is in [MC] scope ands casts the resulting
  lambda into a [tactic] to make sure that it can be ran. *)
  Notation "\tactic g => t" :=
    ((fun g => t%MC) : tactic) (at level 200, g at level 0, right associativity).

  Notation "r '<-' t1 ';' t2" := (bind t1 (fun r => t2%tactic))
    (at level 20, t1 at level 100, t2 at level 200,
     format "'[' r  '<-'  '[' t1 ;  ']' ']' '/' t2 ") : tactic_scope.
  Notation "' r1 .. rn '<-' t1 ';' t2" := (bind t1 (fun r1 => .. (fun rn => t2%tactic) ..))
    (at level 20, r1 binder, rn binder, t1 at level 100, t2 at level 200,
     format "'[' ''' r1 .. rn  '<-'  '[' t1 ;  ']' ']' '/' t2 ") : tactic_scope.

  Notation "f =<< t" := (bind t f) (at level 70, only parsing) : tactic_scope.
  Notation "t >>= f" := (bind t f) (at level 70) : tactic_scope.

  Infix "<$>" := fmap (at level 61, left associativity) : tactic_scope.
  Infix "<*>" := fapp (at level 61, left associativity) : tactic_scope.

  Notation "t1 ';;' t2" := (seq t1 t2)
    (at level 100, t2 at level 200,
     right associativity, format "'[' '[' t1 ;;  ']' ']' '/' t2 ") : tactic_scope.

  Notation "'mif' b 'then' t 'else' u" :=
    (cond <- b; if cond then t else u) (at level 200) : tactic_scope.

  Notation "'mfix0' f : 'gtactic' T := b" :=
    (fix0 T%type (fun f => b%tactic))
    (at level 200, f ident, format
    "'[v  ' 'mfix0'  f  ':'  'gtactic'  T  ':=' '/  ' b ']'") : tactic_scope.

  Notation "'mfix1' f x .. y : 'gtactic' T := b" :=
    (fix1 (fun x => .. (fun y => T%type) ..) (fun f x => .. (fun y => b%tactic) ..))
    (at level 200, f ident, x binder, y binder, format
    "'[v  ' 'mfix1'  f  x  ..  y  ':'  'gtactic'  T  ':=' '/  ' b ']'") : tactic_scope.

  Notation "'mfix2' f x .. y : 'gtactic' T := b" :=
    (fix2 (fun x => .. (fun y => T%type) ..) (fun f x => .. (fun y => b%tactic) ..))
    (at level 200, f ident, x binder, y binder, format
    "'[v  ' 'mfix2'  f  x  ..  y  ':'  'gtactic'  T  ':=' '/  ' b ']'") : tactic_scope.

  Notation "'mfix3' f x .. y : 'gtactic' T := b" :=
    (fix3 (fun x => .. (fun y => T%type) ..) (fun f x => .. (fun y => b%tactic) ..))
    (at level 200, f ident, x binder, y binder, format
    "'[v  ' 'mfix3'  f  x  ..  y  ':'  'gtactic'  T  ':=' '/  ' b ']'") : tactic_scope.

  Notation "'mfix4' f x .. y : 'gtactic' T := b" :=
    (fix4 (fun x => .. (fun y => T%type) ..) (fun f x => .. (fun y => b%tactic) ..))
    (at level 200, f ident, x binder, y binder, format
    "'[v  ' 'mfix4'  f  x  ..  y  ':'  'gtactic'  T  ':=' '/  ' b ']'") : tactic_scope.

  Notation "'mmatch' x ls" :=
    (@mmatch' _ (fun _ => _) x ls%with_pattern)
    (at level 200, ls at level 91) : tactic_scope.
  Notation "'mmatch' x 'return' 'gtactic' p ls" :=
    (@mmatch' _ (fun x => p%type) x ls%with_pattern)
    (at level 200, ls at level 91) : tactic_scope.
  Notation "'mmatch' x 'as' y 'return' 'gtactic' p ls" :=
    (@mmatch' _ (fun y => p%type) x ls%with_pattern)
    (at level 200, ls at level 91) : tactic_scope.

  Notation "'mtry' a ls" :=
    (mtry' a (fun e =>
      (@mmatch' _ (fun _ => _) e
                   (mapp ls%with_pattern [m:([? x] x => raise x)%pattern]))))
      (at level 200, a at level 100, ls at level 91, only parsing) : tactic_scope.

  Notation "t || u" := (or t u) : tactic_scope.

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
    (seq_list t (name_pattern n%list)) (at level 40) : tactic_scope.

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
    ((@mcons (goal_pattern _) p1%match_goal_pattern (.. (@mcons (goal_pattern _) pn%match_goal_pattern [m:]) ..)))
      (at level 91, p1 at level 210, pn at level 210) : match_goal_with_scope.
  Notation "'with' p1 | .. | pn 'end'" :=
    ((@mcons (goal_pattern _) p1%match_goal_pattern (.. (@mcons (goal_pattern _) pn%match_goal_pattern [m:]) ..)))
      (at level 91, p1 at level 210, pn at level 210) : match_goal_with_scope.

  Delimit Scope match_goal_with_scope with match_goal_with.

  Notation "'match_goal' ls" := (match_goal_base UniCoq ls%match_goal_with)
    (at level 200, ls at level 91) : tactic_scope.
  Notation "'match_goal_nored' ls" := (match_goal_base UniMatchNoRed ls%match_goal_with)
    (at level 200, ls at level 91) : tactic_scope.

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

Definition symmetry_in {T} {x y: T} (H: x = y) : tactic :=
  apply_in (@Coq.Init.Logic.eq_sym _ _ _) H.

Definition exfalso : tactic :=
  apply Coq.Init.Logic.False_ind.

Definition nconstructor (n : nat) : tactic :=
  A <- goal_type;
  match n with
  | 0 => M.raise ConstructorsStartsFrom1
  | S n =>
    l <- M.constrs A;
    match mnth_error (msnd l) n with
    | mSome (@Dyn A x) => apply x
    | mNone => raise CantFindConstructor
    end
  end.

Definition split : tactic :=
  A <- goal_type;
  l <- M.constrs A;
  match msnd l with
  | [m:_] => nconstructor 1
  | _ => raise Not1Constructor
  end.

Definition left : tactic :=
  A <- goal_type;
  l <- M.constrs A;
  match msnd l with
  | Dyn x :m: [m: _ ] => apply x
  | _ => raise Not2Constructor
  end.

Definition right : tactic :=
  A <- goal_type;
  l <- M.constrs A;
  match msnd l with
  | _ :m: [m: Dyn x] => apply x
  | _ => raise Not2Constructor
  end.

Definition assumption : tactic :=
  A <- goal_type;
  match_goal with [[ x : A |- A ]] => exact x end.

(** Given a type [T] it searches for a hypothesis with that type and
    executes the [cont]inuation on it.  *)
Definition select (T : Type) : gtactic T :=
  A <- goal_type;
  match_goal with [[ x : T |- A ]] => T.ret x end.

(** generalize with clear *)
Definition cmove_back {A} (x : A) (cont : tactic) : tactic :=
  generalize x ;; cclear x cont.
Notation "'move_back' x" := (cmove_back x idtac) (at level 50).

Definition first {B} : mlist (gtactic B) -> gtactic B :=
  fix go l : gtactic B :=
    match l with
    | [m:] => T.raise NoProgress
    | x :m: xs => x || go xs
    end.

End T.
Coercion T.of_M : M >-> gtactic.
