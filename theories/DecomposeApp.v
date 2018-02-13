From Mtac2 Require Import Base Datatypes List Sorts Specif MTele MFixDef MTeleMatchDef Tactics.
Import Sorts.
Import M.notations.
Import ListNotations.

Set Polymorphic Inductive Cumulativity.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(** Given `(A T : Type) (t : T)`, derive
    - `m : MTele`
    - `MTele_Const A m`
    such that
    - `T = MTele_Const A m`
    - `t : MTele_Const A m`
*)

(* FIX: proper error messaging *)
Definition MTele_of (A : Type) : forall T, T -> M (msigT (MTele_Const (s:=SType) A)) :=
  let matchtele := fun T => mTele (fun _ : T => mBase) in
  let fixtele := mTele (matchtele) in
  mfix'
    (m:=fixtele)
    (fun T (_ : T) => msigT (MTele_Const (s:=SType) A))
    (
      fun f T =>
        mtmmatch'
          _
          matchtele
          _
          T
          [m:
             (@mtpbase
                _
                (fun T => T -> M (msigT (MTele_Const (s:=SType) A)))
                A
                (fun t : A => M.ret (mexistT (MTele_Const (s:=SType) A) mBase t))
                UniCoq
             )
          |  (mtptele (fun (X : Type) => mtptele (fun (F : forall x : X, Type) =>
              @mtpbase
                _
                (fun T => T -> M (msigT (MTele_Const (s:=SType) A)))
                (forall x : X, F x)
                (fun t : _ =>
                   b <- M.fresh_binder_name T;
                   M.nu b mNone (fun x =>
                                   let Fx := reduce (RedOneStep [rl:RedBeta]) (F x) in
                                   let tx := (* rone_step *) (t x) in
                                   ''(mexistT _ n T) <- f Fx tx;
                                   n' <- M.abs_fun (P:=fun _ => MTele) x n;
                                   T' <- M.coerce T;
                                   T' <- M.abs_fun (P:=fun x => MTele_Const (s:=SType) A (n' x)) x T';
                                   M.ret (mexistT (MTele_Const (s:=SType) A) (mTele n') T')
                                )
                )
                UniCoq
             )))
          ]
    ).

Definition decompose_app {m : MTele} (p : PTele m) {A B T: Type} (a : A) (t : T):
  M (MTele_Const (s:=SProp) (M B) p -> M B) :=
  (
    ''(mexistT _ m' T') <- MTele_of A T t;
    M.unify m m' UniCoq;;
    MT <- M.evar _;
    t' <- M.coerce t;
    eq <- M.unify_or_fail UniCoq _ _;
    let x := @M.decompose_app' A B m p a MT t' eq in
    M.ret x
  ).

Notation "'<[decapp' a b 'with' x , .. , z ]>" :=
  (
      let p := (pTele x .. (pTele z pBase) ..) in
      ltac:(mrun (decompose_app p a b))
  )
  (at level 0, a at next level, b at next level) : M_scope.

Notation "'<[decapp' a b ]>" :=
  (
    let p := pBase in
    ltac:(mrun (decompose_app p a b))
  )
  (at level 0, a at next level, b at next level) : M_scope.

Local Definition mtele_convert {B : Prop} {G : Type} {mt} (p : PTele mt) :
  (G -> MTele_Const (s:=SProp) B p) ->
  (MTele_Const (s:=SProp) (G -> B) p).
induction p.
- cbn. induction n.
  + cbn. refine (fun x => x).
  + cbn. intros. refine (H _ _). intro. now refine (H0 _ _).
- cbn.
  refine IHp.
Defined.

Local Definition mtele_convert' {B : Prop} {G : Type} {mt} (p : PTele mt) :
  (MTele_Const (s:=SProp) (G -> B) p) ->
  (G -> MTele_Const (s:=SProp) (B) p).
induction p.
- cbn. induction n.
  + cbn. refine (fun x => x).
  + cbn. intros. refine (H _ _ _); [now refine (H0 _)|assumption].
- cbn.
  refine IHp.
Defined.

Definition decompose_app_tactic {m : MTele} (p : PTele m) {A B T: Type} (a : A) (t : T):
  M ((MTele_Const (s:=SProp) (gtactic B) p) -> gtactic B) :=
  (
    ''(mexistT _ m' T') <- MTele_of A T t;
    M.unify m m' UniCoq;;
    MT <- M.evar _;
    t' <- M.coerce t;
    eq <- M.unify_or_fail UniCoq _ _;
    let x := fun f (g : goal) => @M.decompose_app' A (mlist (mprod B goal)) m p a MT t' eq (f g) in
    let y := fun f => x (mtele_convert' _ f) in
    M.ret y
  ).

Notation "'<[decapp' a b 'with' x , .. , z ]>" :=
  (
      let p := (pTele x .. (pTele z pBase) ..) in
      ltac:(mrun (decompose_app_tactic p a b))
  )
  (at level 0, a at next level, b at next level) : tactic_scope.

Notation "'<[decapp' a b ]>" :=
  (
    let p := pBase in
    ltac:(mrun (decompose_app_tactic p a b))
  )
  (at level 0, a at next level, b at next level) : tactic_scope.