From Mtac2 Require Import Base Datatypes List Sorts tactics.Tactics.
Require Import Strings.String.
Import Sorts.S.
Import Mtac2.lib.List.ListNotations.
Import ProdNotations.
Import Tactics.T.
Import M.
Import M.notations.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Module TT.

(** A typed tactic is a program that promises in its type the goal it solves,
    pehaps creating (dynamically-typed) goals. *)
Definition ttac A := M (A *m mlist (goal gs_any)).

Declare Scope typed_tactic_scope.
Bind Scope typed_tactic_scope with ttac.
Delimit Scope typed_tactic_scope with TT.

(** [to_goal A] returns an evar with type A, and a the [goal] based on it.  It
    tries to coerce [A] into a [Prop] first, in order to provide the most
    precise goal possible.  For that, we need to backtrack in case it is not a
    [Prop] (and treat it as a [Type]). *)
Mtac Do New Exception NotAProp.
Definition to_goal (A : Type) : M (A *m goal gs_open) :=
  mtry
    P <- evar Prop;
    of <- unify_univ P A UniMatchNoRed;
    match of with
    | mSome f => a <- M.evar P;
                 let a' := reduce (RedOneStep [rl: RedBeta]) (f a) in
                 ret (m: a', Metavar Propₛ a)
    | mNone => raise NotAProp (* we backtrack to erase P *)
    end
  with [#] NotAProp | =n>
    a <- evar A;
    M.ret (m: a, Metavar Typeₛ a)
  end.

(** [demote] is a [ttac] that proves anything by simply postponing it as a
    goal. *)
Definition demote {A: Type} : ttac A :=
  ''(m: a, g) <- to_goal A;
  let '(Metavar _ g) := g in
  M.ret (m: a, [m: AnyMetavar _ g]).

(** [use t] tries to solve the goal with tactic [t] *)
Definition use {A} (t : tactic) : ttac A :=
    ''(m: a, g) <- to_goal A;
    gs <- t g;
    let gs := dreduce (@mmap) (mmap (fun '(m: _, g) => g) gs) in
    M.ret (m: a, gs).
Arguments use [_] _%tactic.

Definition idtac {A} : ttac A :=
    ''(m: a, g) <- to_goal A;
    let '(Metavar _ g) := g in
    M.ret (m: a, [m: AnyMetavar _ g]).

(** [by'] is like [use] but it ensures there are no goals left. *)
Definition by' {A} (t : tactic) : ttac A :=
  ''(m: a, g) <- to_goal A;
  gs <- t g;
  gs' <- T.filter_goals gs;
  match gs' with
  | [m:] => ret (m: a, [m:])
  | _ => failwith "couldn't solve"
  end.
Arguments by' [_] _%tactic.

(** Coercion between an [M] program and a [ttac] *)
Definition lift {A} (t : M A) : ttac A :=
  t >>= (fun a => M.ret (m: a,  [m:])).

Coercion lift : M.t >-> ttac.

(** The composition operator. It combines the subgoals according to function [comb]. *)
Definition fappgl {A B C} (comb : C -> C -> M C) (f : M ((A -> B) *m C)) (x : M (A *m C)) : M (B *m C) :=
  (f >>=
     (fun '(m: b, cb) =>
        ''(m: a, ca) <- x;
        c <- comb cb ca;
        M.ret (m: b a, c)
     )
  )%MC.

Definition Mappend {A} (xs ys : mlist A) :=
  let zs := dreduce (@mapp) (mapp xs ys) in
  M.ret zs.

(** [to_T t] uses the result of a [ttac] as a [tactic]. *)
Definition to_T {A} : (A *m mlist (goal _)) -> tactic :=
  (fun '(m: a, gs) g =>
    exact a g;;
    let gs := dreduce (@mmap) (mmap (mpair tt) gs) in
    M.ret gs
  )%MC.


Definition apply {A} (a : A) : ttac A :=
  M.ret (m: a, [m:]).


Definition apply_ {A} : ttac A :=
  by' apply_.

Definition try {A} (t : ttac A) : ttac A :=
  mtry t with _ => demote : M _ end.

Mtac Do New Exception TTchange_Exception.
Definition change A {B} (f : ttac A) : ttac B :=
  (oeq <- M.unify A B UniCoq;
   match oeq with
   | mSome eq =>
     match eq in Logic.meq _ X return ttac X with
     | Logic.meq_refl => f
     end
   | mNone => M.raise TTchange_Exception
   end
  )%MC.

Definition change_dep {X} (B : X -> Type) x {y} (f : ttac (B x)) : ttac (B y) :=
  (
  e <- M.unify x y UniCoq;
  match e with
  | mSome e =>
      match e in Logic.meq _ z return ttac (B z) with
      | Logic.meq_refl => f
      end
  | mNone => M.raise TTchange_Exception
  end
  )%MC.


Definition vm_compute {A} : ttac (A -> A) :=
  (
    M.ret (m: (fun a : A => a <: A), [m:])
  )%MC.

Definition vm_change_dep {X} (B : X -> Type) x {y} (f : ttac (B x)) : ttac (B y) :=
  (
    let x' := reduce RedVmCompute x in
    let y' := reduce RedVmCompute y in
  e <- M.unify x' y' UniMatchNoRed;
  match e with
  | mSome e =>
      match e in Logic.meq _ z return ttac (B z) with
      | Logic.meq_refl => f
      end
  | mNone => M.raise TTchange_Exception
  end
  )%MC.

Definition tintro {A P} (f: forall (x:A), ttac (P x))
  : ttac (forall (x:A), P x) :=
  M.nu (FreshFrom f) mNone (fun x=>
    ''(m: v, gs) <- f x;
    a <- M.abs_fun x v;
    b <- T.close_goals x (mmap (fun g=>(m: tt, g)) gs);
    let b := mmap msnd b in
    M.ret (m: a, b)).

Definition tpass {A} := lift (M.evar A).

Definition texists {A} {Q:A->Prop} : ttac (exists (x:A), Q x) :=
  e <- M.evar A;
  pf <- M.evar (Q e);
  M.ret (m: ex_intro _ e pf, [m: AnyMetavar Propₛ pf]).

Definition tassumption {A:Type} : ttac A :=
  lift (M.select _).

Definition tor {A:Type} (t u : ttac A) : ttac A :=
  mtry r <- t; M.ret r with _ => r <- u; M.ret r end.

Definition reflexivity {P} {A B : P} : TT.ttac (A = B) :=
  r <- M.coerce (eq_refl A); M.ret (m: r, [m:]).

Require Import Strings.String.

Definition ucomp1 {A B} (t: ttac A) (u: ttac B) : ttac A :=
  ''(m: v1, gls1) <- t;
  match gls1 with
  | [m: gl] =>
    ''(m: v2, gls) <- u;
    open_and_apply (exact v2) gl;;
    M.ret (m: v1, gls)
  | _ => mfail "more than a goal"%string
  end.

Definition lower {A} (t: ttac A) : M A :=
  ''(m: r, _) <- t;
  ret r.


(** [rewrite] allows to rewrite with an equation in a specific part of the goal. *)
Definition rewrite {X : Type} (C : X -> Type) {a b : X} (H : a = b) :
  ttac (C b) -> ttac (C a) := fun t =>
  ''(m: x, gs) <- t;
  M.ret (m:
          match H in _ = z return (C z) -> (C a) with
          | eq_refl => fun x => x
          end x,
          gs).

(** with_goal_prop is an easy way of focusing on the current goal to go from
    [tactic] to [ttac]. It is cheap when the goal is correctly annotated as
    a Prop and no more expensive than focusing via `match_goal` when it isn't.
 *)
Definition with_goal_prop (F : forall (P : Prop), ttac P) : tactic := fun g =>
  match g with
  | @Metavar Propₛ G g =>
    ''(m: x, gs) <- F G;
    M.cumul_or_fail UniCoq x g;;
    M.map (fun g => M.ret (m:tt,g)) gs
  | @Metavar Typeₛ G g =>
    gP <- evar Prop;
    mtry
      cumul_or_fail UniMatch gP G;;
      ''(m: x, gs) <- F gP;
      M.cumul_or_fail UniCoq x g;;
      M.map (fun g => M.ret (m:tt,g)) gs
    with _ => raise CantCoerce end (* its better to raise CantCoerce than NotCumul *)
  end.

(** with_goal_type is an easy way of focusing on the current goal to go from
    [tactic] to [ttac]. It is always cheap and will upcast props.
 *)
Definition with_goal_type (F : forall (T : Type), ttac T) : tactic := fun g =>
  match g with
  | @Metavar Propₛ G g =>
    ''(m: x, gs) <- F G;
    M.cumul_or_fail UniCoq x g;;
    M.map (fun g => M.ret (m:tt,g)) gs
  | @Metavar Typeₛ G g =>
    gP <- evar Prop;
    mtry
      cumul_or_fail UniMatch gP G;;
      ''(m: x, gs) <- F G;
      M.cumul_or_fail UniCoq x g;;
      M.map (fun g => M.ret (m:tt,g)) gs
    with _ => raise CantCoerce end (* its better to raise CantCoerce than NotCumul *)
  end.


Definition with_goal_sort (F : forall {s : Sort} (T : s), ttac T) (e : Exception) : tactic :=
  fun g =>
    match g with
    | @Metavar s T g =>
      ''(m: t, gs) <- F T;
      o <- M.unify g t UniMatchNoRed;
      match o with
      | mSome _ =>
        gs <- M.map (fun x => M.ret (mpair tt x)) gs;
        M.ret gs
      | mNone => raise e
      end
    end.

Module MatchGoalTT.
Import TacticsBase.T.notations.
Import Mtac2.lib.Logic.
Inductive goal_pattern : Prop :=
  | gbase : forall (A : _), ttac A -> goal_pattern
  | gbase_context : forall {A} (a : A), (forall (C : A -> Type), ttac (C a)) -> goal_pattern
  | gtele : forall {C}, (C -> goal_pattern) -> goal_pattern
  | gtele_evar : forall {C}, (C -> goal_pattern) -> goal_pattern.
Arguments gbase _ _.
Arguments gbase_context {A} _ _.
Arguments gtele {C} _.
Arguments gtele_evar {C} _.

Set Printing Implicit.

(* [with_upcast] is necessary to call the continuation in [gbase_context] on a
   sorted goal after abstracting from the goal. It avoids a [selem_of] coercion
   that would otherwise be introduced. *)
Definition with_upcast {s : Sort} {A} {a : A} :
  (forall (C : A -> Type), ttac (C a)) ->
  forall C : (A -> s), ttac (C a) :=
  match s with
  | Propₛ => fun t (f : A -> Propₛ) => t f
  | Typeₛ => fun t (f : A -> Typeₛ) => t f
  end.

Fixpoint match_goal_pattern'
    (u : Unification) (p : goal_pattern) : mlist Hyp -> mlist Hyp -> tactic :=
  fix go l1 l2 g :=
  match p, l2 with
  | gbase P t, _ =>
    with_goal_sort (
        fun s G =>
          o <- M.unify_univ P G u;
          match o with
          | mSome f =>
            ''(m: p, gs) <- t;
            let fp := reduce (RedOneStep [rl:RedBeta]) (f p) in
            M.ret (m: fp, gs)
          | mNone => raise DoesNotMatchGoal
          end
      ) (DoesNotMatchGoal) g
  | gbase_context x t, _ =>
    with_goal_sort (
        fun s G =>
          T.abstract_from_sort_dep s x G
                                   (fun C => C *m mlist (goal gs_any))
                                   (* avoid [selem_of] coercions *)
                                   (with_upcast t)
                                   (raise DoesNotMatchGoal)
      ) (DoesNotMatchGoal) g
  | @gtele C f, @ahyp A a d :m: l2' =>
    oeqCA <- M.unify C A u;
    match oeqCA with
    | mSome eqCA =>
      let a' := rcbv match Logic.meq_sym eqCA in _ =m= X return X with meq_refl => a end in
      mtry match_goal_pattern' u (f a') [m:] (mrev_append l1 l2') g
      with [#] DoesNotMatchGoal | =n>
        go (ahyp a d :m: l1) l2' g
      end
    | mNone => go (ahyp a d :m: l1) l2' g end
  | @gtele_evar C f, _ =>
    e <- M.evar C;
    match_goal_pattern' u (f e) l1 l2 g
  | _, _ => M.raise DoesNotMatchGoal
  end%MC.

Definition match_goal_pattern (u : Unification)
    (p : goal_pattern) : tactic := fun g=>
  (r <- M.hyps; match_goal_pattern' u p [m:] (mrev' r) g)%MC.

Fixpoint match_goal_base (u : Unification)
    (ps : mlist (goal_pattern)) : tactic := fun g =>
  match ps with
  | [m:] => M.raise NoPatternMatchesGoal
  | p :m: ps' =>
    mtry match_goal_pattern u p g
    with [#] DoesNotMatchGoal | =n> match_goal_base u ps' g end
  end%MC.
End MatchGoalTT.
Import MatchGoalTT.

Arguments match_goal_base _ _%TT.

Module notations.
(* Notation "[t: x | .. | y ]" := (TT.compi x (.. (TT.compi y (M.ret I)) ..)). *)
(* Set Warnings "(-[non-reversible-notation,parsing])". *)
(* Notation "'doTT' t" := (ltac:(mrun (doTT t))) (at level 0). *)

Infix "<**>" := (fappgl Mappend) (at level 61, left associativity) : M_scope.
Infix "&**" := ucomp1 (at level 60) : M_scope.
Infix "||t" := tor (at level 59) : M_scope.

Declare Scope typed_match_goal_pattern_scope.

Notation "[[ |- ps ] ] => t" :=
  (gbase ps t)
  (at level 202, ps at next level) : typed_match_goal_pattern_scope.
Notation "[[? a .. b | x .. y |- ps ] ] => t" :=
  (gtele_evar (fun a => .. (gtele_evar (fun b =>
     gtele (fun x => .. (gtele (fun y => gbase ps t)).. ))).. ))
  (at level 202, a binder, b binder,
   x binder, y binder, ps at next level) : typed_match_goal_pattern_scope.
Notation "[[? a .. b |- ps ] ] => t" :=
  (gtele_evar (fun a => .. (gtele_evar (fun b => gbase ps t)).. ))
  (at level 202, a binder, b binder, ps at next level) : typed_match_goal_pattern_scope.
Notation "[[ x .. y |- ps ] ] => t" :=
  (gtele (fun x => .. (gtele (fun y => gbase ps t)).. ))
  (at level 202, x binder, y binder, ps at next level) : typed_match_goal_pattern_scope.

Notation "[[ |- 'context' C [ ps ] ] ] => t" :=
  (gbase_context ps (fun C => t))
  (at level 202, C at level 0, ps at next level) : typed_match_goal_pattern_scope.
Notation "[[? a .. b | x .. y |- 'context' C [ ps ] ] ] => t" :=
  (gtele_evar (fun a => .. (gtele_evar (fun b =>
     gtele (fun x=> .. (gtele (fun y => gbase_context ps (fun C => t))).. ))).. ))
  (at level 202, a binder, b binder,
   x binder, y binder, C at level 0, ps at next level) : typed_match_goal_pattern_scope.
Notation "[[? a .. b |- 'context' C [ ps ] ] ] => t" :=
  (gtele_evar (fun a => .. (gtele_evar (fun b => gbase_context ps (fun C => t))).. ))
  (at level 202, a binder, b binder, C at level 0, ps at next level) : typed_match_goal_pattern_scope.
Notation "[[ x .. y |- 'context' C [ ps ] ] ] => t" :=
  (gtele (fun x=> .. (gtele (fun y => gbase_context ps (fun C => t))).. ))
  (at level 202, x binder, y binder, C at level 0, ps at next level) : typed_match_goal_pattern_scope.

Delimit Scope typed_match_goal_pattern_scope with typed_match_goal_pattern.

Declare Scope typed_match_goal_with_scope.

Notation "'with' | p1 | .. | pn 'end'" :=
  ((@mcons (goal_pattern) p1%typed_match_goal_pattern (.. (@mcons (goal_pattern) pn%typed_match_goal_pattern [m:]) ..)))
    (at level 91, p1 at level 210, pn at level 210) : typed_match_goal_with_scope.
Notation "'with' p1 | .. | pn 'end'" :=
  ((@mcons (goal_pattern) p1%typed_match_goal_pattern (.. (@mcons (goal_pattern) pn%typed_match_goal_pattern [m:]) ..)))
    (at level 91, p1 at level 210, pn at level 210) : typed_match_goal_with_scope.

Delimit Scope typed_match_goal_with_scope with typed_match_goal_with.

Notation "'match_goal' ls" := (match_goal_base UniCoq ls%typed_match_goal_with)
  (at level 200, ls at level 91) : typed_tactic_scope.
Notation "'match_goal_nored' ls" := (match_goal_base UniMatchNoRed ls%typed_match_goal_with)
  (at level 200, ls at level 91) : typed_tactic_scope.
End notations.

End TT.
