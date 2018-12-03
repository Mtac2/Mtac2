Require Import Strings.String.
Require Import ssrmatching.ssrmatching.
From Mtac2 Require Export Base.
From Mtac2 Require Import Logic Datatypes List Utils Logic intf.Sorts.
Import Sorts.S.
Import M.notations.
Import Mtac2.lib.List.ListNotations.

Require Import Strings.String.
Require Import NArith.BinNat.
Require Import NArith.BinNatDef.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

(** Exceptions *)
Mtac Do New Exception NoGoalsLeft.
Mtac Do New Exception NotSameSize.
Mtac Do New Exception DoesNotMatchGoal.
Mtac Do New Exception NoPatternMatchesGoal.

Import ProdNotations.

(** The type for tactics *)
Definition gtactic (A: Type) := goal gs_base -> M.t (mlist (mprod A (goal gs_any))).
Definition tactic := gtactic unit.

Delimit Scope tactic_scope with tactic.
Bind Scope tactic_scope with gtactic.

Module T.
Definition with_goal {A} (f : goal gs_base -> M A) := fun g : goal gs_base =>
  match g with
  | Goal _ g' =>
    y <- f g; M.ret [m: (m: y, GoalOut _ g')]
  end.

Coercion of_M {A} (x : M A) : gtactic A := with_goal (fun _ => x).

Definition mtry' {A} (t : gtactic A)
    (f : Exception -> gtactic A) : gtactic A := fun g =>
  M.mtry' (t g) (fun e => f e g).

Definition raise {A} (e : Exception) : gtactic A := M.raise e.

Definition fix0 (B : Type) : (gtactic B -> gtactic B) -> gtactic B :=
  @M.fix1 (goal _) (fun _ => mlist (B *m (goal _))).

Definition fix1 {A} (B : A -> Type) :
    ((forall x : A, gtactic (B x)) -> (forall x : A, gtactic (B x))) ->
    forall x : A, gtactic (B x) :=
  @M.fix2 A (fun _ => (goal _)) (fun x _ => mlist (B x *m (goal _))).

Definition fix2 {A1} {A2 : A1 -> Type} (B : forall a1 : A1, A2 a1 -> Type) :
    ((forall (x1 : A1) (x2 : A2 x1), gtactic (B x1 x2)) ->
      forall (x1 : A1) (x2 : A2 x1), gtactic (B x1 x2)) ->
    forall (x1 : A1) (x2 : A2 x1), gtactic (B x1 x2) :=
  @M.fix3 A1 A2 (fun _ _ => (goal _)) (fun x y _ => mlist (B x y *m (goal _))).

Definition fix3 {A1} {A2 : A1 -> Type} {A3 : forall a1 : A1, A2 a1 -> Type}
  (B : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type) :
    ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), gtactic (B x1 x2 x3)) ->
      forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), gtactic (B x1 x2 x3)) ->
    forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), gtactic (B x1 x2 x3) :=
  @M.fix4 A1 A2 A3 (fun _ _ _ => (goal _)) (fun x y z _ => mlist (B x y z *m (goal _))).

Definition fix4 {A1} {A2 : A1 -> Type} {A3 : forall a1 : A1, A2 a1 -> Type}
    {A4 : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type}
    (B : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2), A4 a1 a2 a3 -> Type) :
    ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), gtactic (B x1 x2 x3 x4)) ->
      forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), gtactic (B x1 x2 x3 x4)) ->
    forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), gtactic (B x1 x2 x3 x4) :=
  @M.fix5 A1 A2 A3 A4 (fun _ _ _ _ => (goal _)) (fun x y z z' _ => mlist (B x y z z' *m (goal _))).

Fixpoint pattern_map {A} {B : A -> Type} (g : (goal _)) (y : A)
    (p : pattern gtactic A B y) : pattern M A (fun y => mlist (B y *m (goal _))) y :=
  match p with
  | pany b => pany (b g)
  | pbase x f r => pbase x (fun Heq => f Heq g) r
  | ptele f => ptele (fun x => pattern_map g y (f x))
  | psort f => psort (fun s => pattern_map g y (f s))
  end.

Definition branch_map {A} {B} (y : A) (g : (goal _)) (b : branch gtactic A B y) :
  branch M A (fun y => mlist (B y *m (goal _))) y :=
  match b in branch _ A' _ y' return branch _ A' _ y' with
  | branch_pattern p =>
    branch_pattern (pattern_map g _ p)
  | branch_app_static U ct cont =>
    let cont := MTele.MTele_constmap_app (si:=SType) SProp (fun _ _ => _) ct cont g in
    @branch_app_static _ _ _ _ _ U _ cont
  | branch_forallP cont => branch_forallP (fun X Y => cont X Y g)
  | branch_forallT cont => branch_forallT (fun X Y => cont X Y g)
  end.


Definition mmatch' {A P} (E : Exception) (y : A)
    (ps : mlist (branch gtactic A P y)) : gtactic (P y) := fun g =>
  M.mmatch' E y (mmap (branch_map y g) ps).

Definition ret {A} (x : A) : gtactic A := fun '(Goal _ g) => M.ret [m:(m: x, GoalOut _ g)].
Definition idtac : tactic := ret tt.

Definition try (t : tactic) : tactic := fun '(Goal _ g' as g)=>
  mtry t g with _ => M.ret [m:(m: tt, GoalOut _ g')] end.

Definition or {A} (t u : gtactic A) : gtactic A := fun g=>
  mtry t g with _ => u g end.

Definition get_binder_name {A} (x : A) : gtactic string := fun '(@Goal _ _ g) =>
  s <- M.get_binder_name x; M.ret [m:(m: s,GoalOut _ g)].

Definition goal_type : gtactic Type := with_goal M.goal_type.
Definition goal_prop : gtactic Prop := with_goal M.goal_prop.

Definition ltac (t : string) (args : mlist dyn) : tactic := fun g =>
  match g with
  | @Goal s ty el =>
    ''(m: v, l) <- @M.call_ltac s ty t args;
    M.unify_or_fail UniCoq v el;;
    let l' := dreduce (@mmap) (mmap (mpair tt) l) in
    M.ret l'
  end.

Definition treduce (r : Reduction) : tactic := fun g=>
  match g with
  | @Goal SType T e=>
    let T' := reduce r T in
    e <- M.evar T';
    mif M.cumul UniEvarconv g (@Goal SType T e) then M.ret [m:(m: tt, @GoalOut SType _ e)]
    else M.failwith "treduce"
  | @Goal SProp T e=>
    let T' := reduce r T in
    e <- M.evar T';
    mif M.cumul UniEvarconv g (@Goal SProp T e) then M.ret [m:(m: tt, @GoalOut SProp _ e)]
    else M.failwith "treduce"
  end.

(** We wrap "pattern" in two functions: one that abstracts a term from a type
    (the usual use of pattern), and another one which abstracts a term from
    another term. For the latter, we need to wrap the term in a type to make
    it work. *)
Ltac Mssrpattern p := ssrpattern p.

Definition Backtrack {s:Sort} {A} (x:A) (f: A->s) : Exception. exact exception. Qed.
Definition abstract_from_sort (s:Sort) {A} (x:A) (B:s) : M (moption (A -> s)) :=
  mtry
    ''(m: _, gs) <- M.call_ltac s (A:=B) "Mssrpattern" [m:Dyn x];
    mmatch gs with
    | [? y (f:A->s) t] [m: @GoalOut s (let z := y in f z) t] =u>
      M.raise (Backtrack y f) (* nasty HACK: we backtract so as not to get evars
      floating: we only care about the term! (which should be well typed in the
      right sigma) *)
    | [? y (f:A->SProp) t] [m: @GoalOut SProp (let z := y in f z) t] =u>
      (* sometimes it might cast down a Prop (that was previously casted to Type *)
      match s as s' return M (moption (A -> s')) with
      | SProp => M.print_term gs;; M.failwith "abstract_from_sort: mmatch"
      | SType => M.raise (Backtrack (s:=SType) y (f:A->Prop))
      end
    | _ => M.print_term gs;; M.failwith "abstract_from_sort: mmatch goal not ground"
    end
  with [? (f:A-> s)] Backtrack x f => M.ret (mSome f)
  | ExceptionNotGround => M.failwith "abstract_from_sort: backtrack"
  | [?s] Failure s => M.raise (Failure s)
  | [?s] LtacError s => M.ret mNone (* we suppose it's not matched *)
  end.
Definition abstract_from_type {A} := @abstract_from_sort SType A.

Definition wrapper {A} (t: A) : Prop. exact False. Qed.

Definition abstract_from_term {A} {B} (x:A) (t : B) : M (moption (A -> B)) :=
  f <- abstract_from_sort SProp x (wrapper t);
  mmatch f with
  | [? g] mSome (fun z:A=>wrapper (g z)) => M.ret (mSome g)
  | mNone => M.ret mNone
  | [? t] mSome t => M.print_term t;; M.failwith "abstract_from_term"
  end.


(** [close_goals x l] takes the list of goals [l] and appends
    hypothesis [x] to each of them. *)
Definition close_goals {A B} (y : B) : mlist (A *m _) -> M (mlist (A *m _)) :=
  M.map (fun '(m: x,g') => r <- M.abs_fun y g'; M.ret (m: x, @AHyp B r)).

(** [let_close_goals x l] takes the list of goals [l] and appends
    hypothesis [x] with its definition to each of them (it assumes it is defined). *)
Definition let_close_goals {A: Type} {B:Type} (y : B) : mlist (A *m goal gs_any) -> M (mlist (mprod A _)) :=
  let t := reduce (RedOneStep [rl:RedDelta]) y in (* to obtain x's definition *)
  M.map (fun '(m: x,g') => r <- M.abs_let y t g'; M.ret (m: x, HypLet B r)).

(** [rem_hyp x l] "removes" hypothesis [x] from the list of goals [l]. *)
Definition rem_hyp {A B} (x : B) (l: mlist (A *m goal gs_any)) : M (mlist (A *m goal gs_any)) :=
  let v := dreduce (@mmap) (mmap (fun '(m: y,g) => (m: y, HypRem x g)) l) in M.ret v.

(** [rep_hyp x l] "replaces" hypothesis [x] from the list of goals [l]. *)
Definition rep_hyp {A B C} (x : A) (e : A =m= B) (l: mlist (C *m goal gs_any)) : M (mlist (C *m goal gs_any)) :=
  let v := dreduce (@mmap) (mmap (fun '(m: y,g) => (m: y, HypReplace x e g)) l) in M.ret v.

(** Returns if a goal is open, i.e., a meta-variable. *)
Definition is_open : forall {gs}, goal gs -> M bool := mfix2 is_open (gs : _) (g : goal gs) : M _ :=
  match g with
  | Goal _ e | GoalOut _ e => M.is_evar e
  | @AHyp C f =>
    (* we get the name in order to avoid inserting existing names
      (nu will raise an exception otherwise) *)
    M.nu Generate mNone (fun x : C => is_open _ (f x))
  | HypLet A f =>
    (* we get the name in order to avoid inserting existing names
      (nu will raise an exception otherwise) *)
    M.nu_let Generate f (fun _ : A =>is_open _)
  | HypRem _ g => is_open _ g (* we don't care about the variable *)
  | HypReplace _ _ g => is_open _ g (* we don't care about the variable *)
  end.

(** removes the goals that were solved *)
Definition filter_goals {A} : mlist (A *m goal gs_any) -> M (mlist (A *m goal gs_any)) :=
  M.filter (fun '(m: x,g) => is_open g).

(** [open_and_apply t] is a tactic that "opens" the current goal
    (pushes all the hypotheses in the context) and applies tactic [t]
    to the so-opened goal. The result is "closed" back. *)
Definition open_and_apply {A} (t : gtactic A) : goal gs_any -> M (mlist (A *m goal gs_any)) :=
  mfix1 open (g: goal gs_any) : M _ :=
    match g return M _ with
    | Goal _ g | GoalOut _ g => t (@Goal _ _ g)
    | @AHyp C f =>
      M.nu (FreshFrom f) mNone (fun x : C =>
        open (f x) >>= close_goals x)
    | HypLet B f =>
      M.nu_let (FreshFrom f) f (fun (x : B) (g : goal gs_any) =>
        open g >>= let_close_goals x)
    | HypRem x f =>
      M.remove x (open f) >>= rem_hyp x
    | HypReplace x e f =>
      M.replace x e (open f) >>= rep_hyp x e
    end.

(** Sequencing *)

Definition bind {A B} (t : gtactic A) (f : A -> gtactic B) : gtactic B := fun g =>
  gs <- t g >>= filter_goals;
  r <- M.map (fun '(m: x,g') => open_and_apply (f x) g') gs;
  let res := dreduce (@mconcat, mapp) (mconcat r) in
  M.ret res.

Definition fmap {A B} (f : A -> B) (x : gtactic A) : gtactic B :=
  bind x (fun a => ret (f a)).
Definition fapp {A B} (f : gtactic (A -> B)) (x : gtactic A) : gtactic B :=
  bind f (fun g => fmap g x).

Fixpoint gmap {A} (tacs : mlist (gtactic A)) (gs : mlist (goal gs_any)) : M (mlist (mlist (A *m goal gs_any))) :=
  match tacs, gs with
  | [m:], [m:] => M.ret [m:]
  | tac :m: tacs', g :m: gs' => mcons <$> open_and_apply tac g <*> gmap tacs' gs'
  | l, l' => M.raise NotSameSize
  end.

Class Seq (A B C : Type) :=
  seq : gtactic A -> C -> gtactic B.
Arguments seq {A B C _} _%tactic _%tactic.

Instance seq_one {A B} : Seq A B (gtactic B) := fun t1 t2 => bind t1 (fun _ => t2).

Instance seq_list {A B} : Seq A B (mlist (gtactic B)) := fun t f g =>
  gs <- filter_goals =<< t g;
  ls <- gmap f (mmap msnd gs);
  let res := dreduce (@mconcat, mapp) (mconcat ls) in
  M.ret res.

(** match_goal *)

Inductive goal_pattern (B : Type) : Prop :=
  | gbase : forall {A}, A -> gtactic B -> goal_pattern B
  | gbase_context : forall {A}, A -> ((A -> Type) -> gtactic B) -> goal_pattern B
  | gtele : forall {C}, (C -> goal_pattern B) -> goal_pattern B
  | gtele_evar : forall {C}, (C -> goal_pattern B) -> goal_pattern B.
Arguments gbase {B A} _ _.
Arguments gbase_context {B} {A} _ _.
Arguments gtele {B C} _.
Arguments gtele_evar {B C} _.

Unset Printing All.
Unset Printing Universes.
Definition match_goal_context (s2:Sort)
    {C}{A} (x: A) (y: s2) (cont: (A -> s2) -> gtactic C) : gtactic C := fun g=>
  r <- abstract_from_sort s2 x y;
  match r with
  | mSome r =>
    cont r g
  | mNone => M.raise DoesNotMatchGoal
  end.

Fixpoint match_goal_pattern' {B}
    (u : Unification) (p : goal_pattern B) : mlist Hyp -> mlist Hyp -> gtactic B :=
  fix go l1 l2 g :=
  match p, l2 with
  | gbase P t, _ =>
    gT <- M.goal_type g;
    mif M.cumul u P gT then t g
    else M.raise DoesNotMatchGoal
  | gbase_context x t, _ =>
    match g with
    | @Goal SProp gT _ =>
      (fun (A : Prop) =>
      match_goal_context SProp x A t g) gT
    | @Goal SType gT _ =>
      (fun (A : Type) =>
      match_goal_context SType x A t g) gT
    end
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

Definition print_goal : tactic := with_goal M.print_goal.

(** Type for goal manipulation primitives *)
Definition selector A := mlist (A *m goal gs_any) -> M (mlist (A *m goal gs_any)).

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
    ((fun g => t%MC) : gtactic _) (at level 200, g at level 0, right associativity).

  Notation "r '<-' t1 ';' t2" := (bind t1 (fun r => t2%tactic))
    (at level 20, t1 at level 100, t2 at level 200,
     format "'[' r  '<-'  '[' t1 ;  ']' ']' '/' t2 ") : tactic_scope.
  Notation "' r1 .. rn '<-' t1 ';' t2" := (bind t1 (fun r1 => .. (fun rn => t2%tactic) ..))
    (at level 20, r1 binder, rn binder, t1 at level 100, t2 at level 200,
     format "'[' ''' r1 .. rn  '<-'  '[' t1 ;  ']' ']' '/' t2 ") : tactic_scope.
  Notation "` r1 .. rn '<-' t1 ';' t2" := (bind t1 (fun r1 => .. (bind t1 (fun rn => t2%tactic)) ..))
    (at level 20, r1 binder, rn binder, t1 at level 100, t2 at level 200,
     right associativity, format "'[' '`' r1  ..  rn  '<-'  '[' t1 ;  ']' ']' '/' t2 ") : tactic_scope.

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
    (@mmatch' _ (fun _ => _) DoesNotMatch x ls%with_pattern)
    (at level 200, ls at level 91) : tactic_scope.
  Notation "'mmatch' x 'return' 'gtactic' p ls" :=
    (@mmatch' _ (fun x => p%type) DoesNotMatch x ls%with_pattern)
    (at level 200, ls at level 91) : tactic_scope.
  Notation "'mmatch' x 'as' y 'return' 'gtactic' p ls" :=
    (@mmatch' _ (fun y => p%type) DoesNotMatch x ls%with_pattern)
    (at level 200, ls at level 91) : tactic_scope.

  Notation "'mtry' a ls" :=
    (mtry' a (fun e =>
      (@mmatch' _ (fun _ => _) M.NotCaught e
                   (mapp ls%with_pattern [m:branch_pattern (pany (raise e))%pattern]))))
      (at level 200, a at level 100, ls at level 91, only parsing) : tactic_scope.

  Notation "t || u" := (or t u) : tactic_scope.

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

  Import MTele.TeleNotation.
  Notation "'dcase' v 'as' A ',' x 'in' t" := (fun g => @M.decompose_app' _ (fun _ => _) [tele A (_:A)] UniMatchNoRed v (@Dyn) (fun A x => t g)) (at level 91, t at level 200) : tactic_scope.
  Notation "'dcase' v 'as' x 'in' t" := (dcase v as _, x in t) (at level 91, t at level 200) : tactic_scope.

End notations.

End T.
Coercion T.of_M : M >-> gtactic.
