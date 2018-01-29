From Mtac2 Require Import Base Datatypes List Sorts Specif MTele MFixDef MTeleMatchDef.
Import Sorts.
Import M.notations.
Import ListNotations.

Set Polymorphic Inductive Cumulativity.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Set Use Unicoq.

(** Given `(A T : Type) (t : T)`, derive
    - `m : MTele`
    - `MTele_Const A m`
    such that
    - `T = MTele_Const A m`
    - `t : MTele_Const A m`
*)

Definition MTele_of (A : Type) : forall T, T -> M (msigT (MTele_Const (s:=SType) A)) :=
  let matchtele := fun T => mTele (fun _ : T => mBase) in
  let fixtele := mTele (matchtele) in
  mfix'
    (m:=fixtele)
    (fun T (_ : T) => msigT (MTele_Const (s:=SType) A))
    (
      fun f T =>
        (* ltac:(simpl in *; refine (mtmmatch' _ matchtele _ _ _)) *)
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
                                   T' <- M.abs_fun x T;
                                   T' <- M.coerce T';
                                   M.ret (mexistT _ (mTele n') T')
                                )
                )
                UniCoq
                                                 )
                      )
             )
          ]
    ).

Check ltac:(mrun (MTele_of (nat) _ (@plus))).

Definition decompose_app {m : MTele} {A B T: Type} (a : A) (t : T) {F}:
  @lift
    (MTele_Const (s:=SProp) (M B) m -> M B)
    (
      ''(mexistT _ m' T') <-
        mtry
          MTele_of A T t
        with | [?E] E => M.print_term E;; M.evar _ end;
        M.unify m m' UniCoq;;
        t' <- M.coerce t;
        let x := @M.decompose_app' A B m a t' in
        M.ret x
    )
    (F) := F.

Check ltac:(mrun ((decompose_app (3+5) (@plus) : (_ -> _)) (fun x y => M.ret (x,y)))).