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
                                   (* M.print "x";; *)
                                   (* M.print_term x;; *)
                                   (* M.print "n";; *)
                                   (* M.print_term n;; *)
                                   n' <- M.abs_fun (P:=fun _ => MTele) x n;
                                   (* M.print "n'";; *)
                                   (* M.print_term n';; *)
                                   (* M.print "T";; *)
                                   (* M.print_term T;; *)
                                   T' <- M.coerce T;
                                   T' <- M.abs_fun (P:=fun x => MTele_Const (s:=SType) A (n' x)) x T';
                                   (* T' <- M.abs_fun x T; *)
                                   (* T' <- M.coerce T'; *)
                                   M.ret (mexistT (MTele_Const (s:=SType) A) (mTele n') T')
                                )
                )
                UniCoq
                                                 )
                      )
             )
          ]
    ).

Check ltac:(mrun (MTele_of (nat) _ (@plus))).

(* This wrapper hardcodes an empty list of arguments. FIXME *)
Definition decompose_app {m : MTele} {A B T: Type} (a : A) (t : T) {F}:
  @lift
    (MTele_Const (s:=SProp) (M B) m -> M B)
    (
      ''(mexistT _ m' T') <-
        mtry
          MTele_of A T t
        with | [?E] E => M.print_term E;; M.evar _ end;
        M.unify m m' UniCoq;;
        (* M.print_term m;; *)
        (* M.print_term T';; *)
        (* let typi := dreduce (@MTele_Ty, @MTele_Sort) (MTele_Ty m) in *)
        (* M.print_term typi;; *)
        (* MT <- M.coerce (B:=typi) T'; *)
                MT <- M.evar _;
        t' <- M.coerce t;
        eq <- M.unify_or_fail UniCoq _ _;
        let x := @M.decompose_app' A B m (pBase) a MT t' eq in
        M.ret x
    )
    (F) := F.

Check ltac:(mrun ((decompose_app (3+5) (@plus) : (_ -> _)) (fun x y => M.ret (x,y)))).