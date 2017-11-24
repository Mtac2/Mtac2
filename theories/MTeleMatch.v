From Mtac2 Require Import Base Logic Datatypes MTele MTeleMatchDef.
Import M.notations.

Definition MTele_of {A} (T : A -> Prop) :=
  b <- M.fresh_binder_name T;
  M.nu b mNone (fun a =>
  (mfix1 f (T : Prop) : M (MTele) :=
    mmatch T as t' return M MTele with
    | [?X : Type] M X =u> M.ret (mBase X)
    (* | [?(X : Prop) (F : forall x:X, Prop)] (forall x:X, F x) =u> *)
    (*   b <- M.fresh_binder_name F; *)
    (*   f <- M.nu b None (fun x => *)
    (*           g <- f (F x); *)
    (*           M.abs_fun x g); *)
    (*   M.ret (mTele f) *)
    | [?(X : Type) (F : forall x:X, Prop)] (forall x:X, F x) =u>
      b <- M.fresh_binder_name F;
      f <- M.nu b mNone (fun x =>
              g <- f (F x);
              M.abs_fun x g);
      M.ret (mTele f)
   end
  ) (T a) >>= (M.abs_fun a)).


Bind Scope mtpattern_prog_scope with mtpattern.
Delimit Scope mtpattern_prog_scope with mtpattern_prog.

Notation "[? x .. y ] ps" := (mtptele (fun x => .. (mtptele (fun y => ps)).. ))
  (at level 202, x binder, y binder, ps at next level) : mtpattern_prog_scope.

Notation "d '=u>' t" := (mtpbase d t UniCoq)
    (at level 201) : mtpattern_prog_scope.
Notation "d '=c>' t" := (mtpbase d t UniEvarconv)
    (at level 201) : mtpattern_prog_scope.
Notation "d '=n>' t" := (mtpbase d t UniMatchNoRed)
    (at level 201) : mtpattern_prog_scope.
Notation "d '=m>' t" := (mtpbase d t UniMatch)
    (at level 201) : mtpattern_prog_scope.

Notation "'_' => b " := (mtptele (fun x=> mtpbase x b%core UniMatch))
  (at level 201, b at next level) : mtpattern_prog_scope.

Notation "'with' | p1 | .. | pn 'end'" :=
  ((@mcons (mtpattern _ _) p1%mtpattern_prog (.. (@mcons (mtpattern _ _) pn%mtpattern_prog mnil) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_mtpattern_prog_scope.
Notation "'with' p1 | .. | pn 'end'" :=
  ((@mcons (mtpattern _ _) p1%mtpattern_prog (.. (@mcons (mtpattern _ _) pn%mtpattern_prog mnil) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_mtpattern_prog_scope.

Delimit Scope with_mtpattern_prog_scope with with_mtpattern_prog.

Class TC_UNIFY {T : Type} (A B : T) := tc_unify : (A =m= B).
Arguments tc_unify {_} _ _ {_}.
Hint Extern 0 (TC_UNIFY ?A ?B) => mrun (o <- M.unify A B UniCoq; match o with | mSome eq => M.ret eq | mNone => M.failwith "cannot (tc_)unify." end) : typeclass_instances.

Structure CS_UNIFY (T : Type) :=
  CS_Unify {
      cs_unify_A : T;
      cs_unify_B : T;
      cs_unify: cs_unify_A =m= cs_unify_B
    }.

Canonical Structure CS_UNIFY_REFl {T} (A : T) : CS_UNIFY T := CS_Unify _ A A meq_refl.
Arguments cs_unify [_ _].

Class MT_OF {A} (T : A -> Prop) := mt_of : A -> MTele.
Arguments mt_of {_} _ {_}.
Hint Extern 0 (MT_OF ?t) => mrun (MTele_of t) : typeclass_instances.

Notation "'mtmmatch_prog' x 'as' y 'return' T p" :=
  (
    let m := mt_of (fun y => T) in
    match tc_unify (fun _z => MTele_ty M (m _z))((fun y => T))
          in _ =m= R return mlist (mtpattern _ R) -> R x with
    | meq_refl => mtmmatch' _ (m) x
    end
    (p%with_mtpattern_prog)
  ) (at level 200, p at level 201).



Definition mtpbase_eq {A} {m : A -> Prop} (x : A) F (eq : m x =m= F x) : F x -> Unification -> mtpattern A m :=
  match eq in _ =m= R return R -> _ -> _ with
  | meq_refl => mtpbase x
  end.


Bind Scope mtpattern_scope with mtpattern.
Delimit Scope mtpattern_scope with mtpattern.


Class MTY_OF {A} := MTt_Of { mty_of : A -> Prop }.
Arguments MTt_Of [_] _.

Class RET_TY (A : Type) := Ret_Ty { ret_ty : A }.
Arguments Ret_Ty [_] _.
Arguments ret_ty [_ _].

Notation "[? x .. y ] ps" := (mtptele (m:=mty_of) (fun x => .. (mtptele (m:=mty_of) (fun y => ps)).. ))
  (at level 202, x binder, y binder, ps at next level) : mtpattern_scope.

Notation "d '=u>' t" := (mtpbase_eq (m:=mty_of) d ret_ty cs_unify t UniCoq)
    (at level 201) : mtpattern_scope.
Notation "d '=c>' t" := (mtpbase_eq (m:=mty_of) d ret_ty cs_unify t UniEvarconv)
    (at level 201) : mtpattern_scope.
Notation "d '=n>' t" := (mtpbase_eq (m:=mty_of) d ret_ty cs_unify t UniMatchNoRed)
    (at level 201) : mtpattern_scope.
Notation "d '=m>' t" := (mtpbase_eq (m:=mty_of) d ret_ty cs_unify t UniMatch)
    (at level 201) : mtpattern_scope.

Notation "'_' => b " := (mtptele (m:=mty_of) (fun x=> mtpbase_eq (m:=mty_of) x ret_ty cs_unify b%core UniMatch))
  (at level 201, b at next level) : mtpattern_scope.

Notation "'with' | p1 | .. | pn 'end'" :=
  ((@mcons (mtpattern _ _) p1%mtpattern (.. (@mcons (mtpattern _ _) pn%mtpattern mnil) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_mtpattern_scope.
Notation "'with' p1 | .. | pn 'end'" :=
  ((@mcons (mtpattern _ _) p1%mtpattern (.. (@mcons (mtpattern _ _) pn%mtpattern mnil) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_mtpattern_scope.

Delimit Scope with_mtpattern_scope with with_mtpattern.

Notation "'mtmmatch' x 'as' y 'return' T p" :=
  (
    let F : RET_TY _ := Ret_Ty (fun y => T) in
    let m := M.eval (MTele_of (fun y => T)) in
    let mt : MTY_OF := MTt_Of (fun _z => MTele_ty M (m _z)) in
    mtmmatch' _ m x p%with_mtpattern
  ) (at level 90, p at level 91).