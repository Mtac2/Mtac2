From Mtac2 Require Import Base Datatypes List Sorts Specif MTele MFixDef MTeleMatchDef.
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
                                   let Fx := rone_step (F x) in
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

(* This wrapper hardcodes an empty list of arguments. FIXME *)
Definition decompose_app {m : MTele} {A B T: Type} (a : A) (t : T):
  M (MTele_Const (s:=SProp) (M B) m -> M B) :=
  (
    ''(mexistT _ m' T') <- MTele_of A T t;
    M.unify m m' UniCoq;;
    MT <- M.evar _;
    t' <- M.coerce t;
    eq <- M.unify_or_fail UniCoq _ _;
    let x := @M.decompose_app' A B m (pBase) a MT t' eq in
    M.ret x
  ).

Notation "'<[decapp' a b ]>" := (ltac:(mrun (decompose_app a b)))
  (at level 0, a at next level, b at next level).
