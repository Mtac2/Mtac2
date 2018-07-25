From Mtac2 Require Import Base Datatypes List MTele MTeleMatch MTeleMatchDef MFixDef Sorts tactics.Tactics.
Require Import Strings.String.
Import Sorts.
Import Mtac2.List.ListNotations.
Import ProdNotations.
Import Tactics.T.
Import M.
Import M.notations.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

(** THIS CODE SHOULD BE MOVED AWAY *)
(* Local Inductive msigT {A} (P : A -> Type) : Type := | mexistT x : P x -> msigT P. *)
(* Local Notation "'{$'  x .. y  &  P }" := (msigT (fun x => .. (msigT (fun y => P)) .. )) (x binder, y binder). *)
(* Local Definition mprojT1 {A} {P} : @msigT A P -> A := fun '(mexistT _ x _) => x. *)
(* Local Definition mprojT2 {A} {P} : forall s : @msigT A P, P (mprojT1 s) := fun '(mexistT _ _ p) => p. *)
(* Local Inductive TTele : Type := *)
(* | ttbase (X : Type) : TTele *)
(* | tttele {X} : (X -> TTele) -> TTele. *)
(* Fixpoint TTele_ty (M : Type -> Type) t := *)
(*   match t with *)
(*   | ttbase X => M X *)
(*   | tttele F => forall x, TTele_ty M (F x) *)
(*   end. *)

(* Local Fixpoint TTele_bind {X} {t} : (X -> TTele_ty M t) -> (TTele_ty M.t t) := *)
(*   match t with *)
(*   | ttbase X => M.bind (M.evar _) *)
(*   | tttele F => fun f (t : _) => @TTele_bind X (F t) (fun x : X => f x t) *)
(*   end *)
(* . *)

(* Local Fixpoint func_of (l : mlist Prop) := *)
(*   match l with *)
(*   | mnil => True *)
(*   | mcons T l => prod T (func_of l) *)
(* end. *)

(* Local Notation "x -*> y" := (prod (func_of x) y) (only parsing, at level 91). *)

(* Local Notation tty := (TTele_ty (fun T => msigT (fun l => M (l -*> T)))). *)

(* Local Fixpoint TTele_bind' {X : Prop} (x : X) {t} : (TTele_ty (fun T => msigT (fun l => X -> M (l -*> T))) t) -> (tty t) := *)
(*   match t with *)
(*   | ttbase B => fun '(mexistT _ l f) => mexistT _ (X :m: l) ( *)
(*                   H <- M.evar X; *)
(*                   ''(goals, R) <- f H; *)
(*                   M.ret ((H,goals), R)) *)
(*   | tttele F => fun f t => *)
(*                   TTele_bind' x (f t) *)
(*   end *)
(* . *)

(* Definition lift_lemma : forall (A : Prop), A -> *)
(*       M (msigT tty) := *)
(*   let m := (mTele (fun (A : Prop) => (mTele (fun (a:A) => mBase)))) in *)
(*   @mfix' m *)
(*          (fun A (a:A) => msigT tty) *)
(*         (fun rec (A : Prop) => *)
(*            let m (A : Prop) := mTele (fun a:A => mBase) in *)
(*            mtmmatch' *)
(*              _ m (fun A a => msigT tty) A *)
(*              [m: *)
(*               (mtptele (fun B:Prop => mtptele (fun (C:Prop) => (mtpbase ( m:=fun A:Prop => A -> M _)) _ ( *)
(*               fun (f : B -> C) => *)
(*                 M.nu (FreshFrom A) mNone (fun b : B => *)
(*                                ''(mexistT _ t X) <- rec C (f b); *)
(*                                match t as t return tty t -> M (_) with *)
(*                                | tttele _ => *)
(*                                  fun _ => *)
(*                                    M.failwith "Lemma to be lifted has dependent quantifiers after non-dependent ones. This is not supported." *)
(*                                | ttbase P => fun f => *)
(*                                                let '(mexistT _ l f) := f in *)
(*                                                f' <- M.abs_fun b f; *)
(*                                                f' <- M.coerce f'; *)
(*                                                let T' := reduce (RedWhd RedAll) *)
(*                                                                 (TTele_bind' b (t:=ttbase _) (mexistT _ l f')) in *)
(*                                           M.ret (mexistT tty (ttbase P) T') *)
(*                                end X *)
(*                      ) *)
(*               ) UniMatchNoRed)))%mtpattern *)
(*              | *)
(*              (mtptele (fun B:Type => mtptele (fun (C:B -> Prop) => (mtpbase ( m:=fun A:Prop => A -> M _)) _ ( *)
(*               fun (f : forall b:B, C b) => *)
(*                 M.nu (FreshFrom A) mNone (fun b : B => *)
(*                                ''(mexistT _ t X) <- rec _ (f b); *)
(*                                t' <- M.abs_fun b t; *)
(*                                X <- M.coerce X; *)
(*                                X' <- M.abs_fun (P:=fun b => tty (t' b)) b X; *)
(*                                M.ret (mexistT tty (tttele t') (fun x => X' x)) *)
(*                      ) *)
(*               ) UniMatchNoRed)))%mtpattern *)
(*               | *)
(*               (mtpbase ( m:=fun A:Prop => A -> M _) A *)
(*                        (fun a:A => *)
(*                           M.ret (mexistT tty (ttbase A) (mexistT _ mnil (M.ret (I,a)))) *)
(*                        ) *)
(*                        UniCoq *)
(*               )%mtpattern *)
(*              ]%with_mtpattern *)
(*         ) *)
(* . *)


(* Local Fixpoint TTele_App {P1} {t} (P2 : forall T (H : P1 T), Type) : TTele_ty P1 t -> Type := *)
(*   match t with *)
(*   | ttbase P => fun x => P2 _ x *)
(*   | tttele F => fun g => forall x, TTele_App P2 (g x) *)
(*   end. *)

(* Local Fixpoint TTele_app {P1} {t} P2 (f : forall T PT, P2 T PT) : forall tt, TTele_App (P1:=P1) (t:=t) P2 tt := *)
(* match t with *)
(* | ttbase T => fun tt : P1 T => f _ _ *)
(* | tttele F => fun (tt : forall t, TTele_ty P1 (F t)) t => @TTele_app _ (F t) _ f (tt t) *)
(* end. *)

(* Definition do_def n {A:Prop} (a:A) := *)
(*   ''(mexistT _ t f) <- lift_lemma A (a); *)
(*   (* let f := reduce (RedStrong [rl: RedBeta; RedZeta; RedFix; RedMatch; RedDeltaOnly [rl: Dyn (@M.type_of); Dyn (@TTele_ty)] ]) (f) in *) *)
(*   let x := reduce (RedStrong [rl: RedFix; RedMatch; RedBeta; RedDeltaOnly [rl: Dyn (@TTele_app)]]) (TTele_app (fun T PT => let '(mexistT _ l _) := PT in M (l -*> T)) *)
(*                                                 (fun T PT => let '(mexistT _ l X) := PT in *)
(*                                                              X *)
(*                                                 ) f) in *)
(*   let T := reduce (RedStrong [rl: RedBeta; RedZeta; RedFix; RedMatch; *)
(*                            RedDeltaOnly [rl: Dyn (@M.type_of); Dyn (@TTele_ty); Dyn (@TTele_App); Dyn (@TTele_app); Dyn (@func_of)] ]) (M.type_of x) in *)
(*                @M.declare dok_Definition n false T x;; M.ret tt. *)

(* (** We use a synonim to prod to emulate typed goals. The idea *)
(*     is that at the left we have the hypotheses, and at the right *)
(*     the goal type. A goal H1, ..., Hn |- G is then written *)
(*     (H1 * ... * Hn) =m> G *)

(*     A lemma lifted to this type will produce an element of type G given *)
(*     promises (evars) for H1, ..., Hn. *)
(* *) *)

(* Definition myprod := prod. *)
(* Arguments myprod _%type _%type. *)

(* Notation "T1 '|m-' G" := (myprod T1 G) *)
(*   (at level 98, no associativity, *)
(*    format "T1  |m-  G") : type_scope. *)


(* (** composes on the left of the arrow *) *)
(* Definition compl {A} {B} (f: M (A |m- B)) (g : M A) : M B := *)
(*   ''(a, b) <- f; *)
(*   a' <- g; *)
(*   mif unify a a' UniCoq then *)
(*     ret b *)
(*   else failwith "nope". *)

(* (** composes a product *) *)
(* Definition compi {A} {B} (g : M A) (h : M B) : M (A * B) := *)
(*   g >>= fun xg=> h >>= fun xh => ret (xg, xh). *)

(* (** Solves goal A provided tactic t *) *)
(* Definition Mby' {A} (t: tactic) : M A := *)
(*   e <- evar A; *)
(*   l <- t (Goal SType e); *)
(*   l' <- T.filter_goals l; *)
(*   match l' with mnil => ret e | _ => failwith "couldn't solve" end. *)

(* Definition Muse {A} (t: tactic) : M A := *)
(*   mtry *)
(*     P <- evar Prop; *)
(*     of <- unify_univ P A UniMatchNoRed; *)
(*     match of with *)
(*     | mSome f => e <- M.evar P; *)
(*                  t (Goal SProp e);; *)
(*                  let e := reduce (RedOneStep [rl: RedBeta]) (f e) in *)
(*                  ret e *)
(*     | mNone => raise NotAProp *)
(*     end *)
(*   with | NotAProp => *)
(*     e <- evar A; *)
(*     t (Goal SType e);; *)
(*     ret e *)
(*   end. *)

(* Definition is_prod T := *)
(*   mmatch T with *)
(*   | [? A B] (A * B)%type => ret true *)
(*   | _ => ret false *)
(*   end. *)

(* Definition dest_pair {T} (x:T) : M (dyn * dyn) := *)
(*   mmatch Dyn x with *)
(*   | [? A B a b] @Dyn (A*B) (a, b) => ret (Dyn a, Dyn b) *)
(*   end. *)

(* (** Given an element with type of the form (A1 * ... * An), *)
(*     it generates a goal for each unsolved variable in the pair. *) *)
(* Program Definition to_goals : forall {A}, A -> M (mlist (unit *m goal)) := *)
(*   mfix2 to_goals (A: Type) (a: A) : M _ := *)
(*   mif is_evar a then ret [m: (m: tt, Goal SType a)] *)
(*   else *)
(*     mif is_prod A then *)
(*       ''(d1, d2) <- dest_pair a; *)
(*       dcase d1 as x in *)
(*       dcase d2 as y in *)
(*       t1s <- to_goals _ x; *)
(*       t2s <- to_goals _ y; *)
(*       ret (t1s +m+ t2s) *)
(*     else *)
(*       ret [m:]. *)

(* (** From a typed tactic with type A |m- B, it generates an untyped one *) *)
(* Definition to_tactic {A B} (f: M (A |m- B)) : tactic := fun g=> *)
(*   gT <- goal_type g; *)
(*   mif unify gT B UniCoq then *)
(*     ''(a, b) <- f; *)
(*     al <- to_goals a; *)
(*     ls <- T.filter_goals al; *)
(*     T.exact b g;; *)
(*     ret ls *)
(*   else *)
(*     failwith "nope". *)

(* Definition pass := evar. *)
(* Arguments pass {_}. *)

(* Import Strings.Ascii. *)
(* Local Open Scope string. *)

(* Definition doTT {A:Prop} (x:A) := *)
(*   s <- pretty_print x; *)
(*   let s := *)
(*       match String.get 0 s with *)
(*       | Some "@"%char => String.substring 1 (String.length s -1) s *)
(*       | _ => s *)
(*       end  ++ "T" in *)
(*   print s;; *)
(*   do_def s x. *)

Module TT.

Definition ttac A := M (A *m mlist goal).
Bind Scope typed_tactic_scope with ttac.
Delimit Scope typed_tactic_scope with TT.

Mtac Do New Exception NotAProp.
Definition to_goal (A : Type) : M (A *m goal) :=
  mtry
    P <- evar Prop;
    of <- unify_univ P A UniMatchNoRed;
    match of with
    | mSome f => a <- M.evar P;
                 let a' := reduce (RedOneStep [rl: RedBeta]) (f a) in
                 ret (m: a', Goal SProp a)
    | mNone => raise NotAProp (* we backtrack to erase P *)
    end
  with NotAProp =>
    a <- evar A;
    M.ret (m: a, Goal SType a)
  end.

Definition demote {A: Type} : ttac A :=
  ''(m: a, g) <- to_goal A; M.ret (m: a, [m: g]).

Definition use {A} (t : tactic) : ttac A :=
    ''(m: a, g) <- to_goal A;
    gs <- t g;
    let gs := dreduce (@mmap) (mmap (fun '(m: _, g) => g) gs) in
    M.ret (m: a, gs).
Arguments use [_] _%tactic.

Definition idtac {A} : ttac A :=
    ''(m: a, g) <- to_goal A;
    M.ret (m: a, [m: g]).

Definition by' {A} (t : tactic) : ttac A :=
  ''(m: a, g) <- to_goal A;
  gs <- t g;
  gs' <- T.filter_goals gs;
  match gs' with
  | [m:] => ret (m: a, [m:])
  | _ => failwith "couldn't solve"
  end.
Arguments by' [_] _%tactic.

Definition lift {A} (t : M A) : ttac A :=
  t >>= (fun a => M.ret (m: a,  [m:])).

Coercion lift : M.t >-> ttac.
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


Definition to_T {A} : (A *m mlist goal) -> tactic :=
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

Mtac Do (new_exception "TTchange_Exception").
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
  M.ret (m: ex_intro _ e pf, [m: Goal SProp pf]).

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
    exact v2 gl;;
    M.ret (m: v1, gls)
  | _ => mfail "more than a goal"%string
  end.

Definition lower {A} (t: ttac A) : M A :=
  ''(m: r, _) <- t;
  ret r.


Module MatchGoalTT.
Import Abstract.
Import TacticsBase.T.notations.
Import Mtac2.Logic.
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
Definition match_goal_context
    {A} (x: A) (y: Type) (cont: forall (C : A -> Type), ttac (C x)) : tactic :=
  r <- T.abstract_from_term x y;
  match r with
  | mSome r =>
    cont r >>=
    to_T
  | mNone => M.raise DoesNotMatchGoal
  end.

Fixpoint match_goal_pattern'
    (u : Unification) (p : goal_pattern) : mlist Hyp -> mlist Hyp -> tactic :=
  fix go l1 l2 g :=
  match p, l2 with
  | gbase P t, _ =>
    gT <- M.goal_type g;
    mif M.cumul u P gT then (r <- t; to_T r g)
    else M.raise DoesNotMatchGoal
  | gbase_context x t, _ =>
    gT <- M.goal_type g;
    match_goal_context x gT t g
  | @gtele C f, @ahyp A a d :m: l2' =>
    oeqCA <- M.unify C A u;
    match oeqCA with
    | mSome eqCA =>
      let a' := rcbv match Logic.meq_sym eqCA in _ =m= X return X with meq_refl => a end in
      mtry match_goal_pattern' u (f a') [m:] (mrev_append l1 l2') g
      with DoesNotMatchGoal =>
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
    with DoesNotMatchGoal => match_goal_base u ps' g end
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
