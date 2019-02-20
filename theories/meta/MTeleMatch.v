Require Import Coq.Strings.String.
From Mtac2 Require Import Base Specif Logic Datatypes MTele MTeleMatchDef.
Import M.notations.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Definition MTele_of {A:Type} (T : A -> Prop) : M (A -> msigT MTele_Ty) :=
  M.nu (FreshFrom T) mNone (fun a =>
  let T' := reduce (RedOneStep [rl:RedBeta]) (T a) in
  (mfix1 f (T : Prop) : M (msigT MTele_Ty) :=
    mmatch T return M (msigT MTele_Ty) with
    | [?X : Type] M X =u> M.ret (mexistT _ mBase X)
    | [?(X : Type) (F : forall x:X, Prop)] (forall x:X, F x) =u>
      M.nu (FreshFrom T) mNone (fun x =>
                      let T' := reduce (RedOneStep [rl:RedBeta]) (F x) in
                      '(mexistT _ n T) <- f T';
                      n' <- M.abs_fun x n;
                      T' <- (M.coerce (B:=MTele_Ty (n' x)) T >>= M.abs_fun x);
                      M.ret (mexistT _ (mTele n') T')
                   )
   end
  ) (T') >>= (fun t =>
                (* M.print_term t;; *)
                t' <- M.abs_fun a t;
                (* M.print_term t';; *)
                M.ret t')).


Local Example test :=
fun x => mexistT MTele_Ty (mTele (fun _ : nat => mBase)) (fun y : nat => x = y).
Eval hnf in ltac:(mrun (MTele_of (fun x : nat => forall y:nat, M (x = y)))).
Local Example MTele_of_Test : nat -> msigT MTele_Ty :=
  Eval hnf in ltac:(mrun (MTele_of (fun x : nat => forall y:nat, M (x = y)))).

Bind Scope mtpattern_prog_scope with mtpattern.
Delimit Scope mtpattern_prog_scope with mtpattern_prog.

Notation "[¿ s .. t ] ps" := (mtpsort (fun s => .. (mtpsort (fun t => ps)) ..))
  (at level 202, s binder, t binder, ps at next level, only parsing) : mtpattern_prog_scope.
Notation "'[S?' s .. t ] ps" := (mtpsort (fun s => .. (mtpsort (fun t => ps)) ..))
  (at level 202, s binder, t binder, ps at next level) : mtpattern_prog_scope.

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
Definition tc_unify_mtac T (A B : T) :=
  (* M.print "tc_unify 1";; *)
  o <- @M.unify T A B UniCoq;
  (* M.print "tc_unify 2";; *)
  match o with
  | mSome eq => M.ret eq
  | mNone =>
    let A := reduce (RedStrong RedAll) A in
    let B := reduce (RedStrong RedAll) B in
    (* M.print_term (A,B);; *)
    M.failwith "cannot (tc_)unify."
  end.
Hint Extern 0 (@TC_UNIFY ?T ?A ?B) => mrun (tc_unify_mtac T A B) : typeclass_instances.

Structure CS_UNIFY (T : Type) :=
  CS_Unify {
      cs_unify_A : T;
      cs_unify_B : T;
      cs_unify: cs_unify_A =m= cs_unify_B
    }.

Class MT_OF {A} (T : A -> Prop) := mt_of : A -> msigT MTele_Ty.
Arguments mt_of {_} _ {_}.
Hint Extern 0 (@MT_OF ?A ?t) => mrun (@MTele_of A t) : typeclass_instances.


Notation "'mtmmatch_prog' x 'as' y 'return' T p" :=
  (
    let mt1 := mt_of (fun y => T) in
    match tc_unify (fun _z => MTele_ty M (mprojT2 (mt1 _z))) ((fun y => T))
          in _ =m= R return mlist (mtpattern _ R) -> R x with
    | meq_refl => mtmmatch' _ (fun _z => mprojT1 (mt1 _z)) (fun _z => mprojT2 (mt1 _z)) x
    end
    (p%with_mtpattern_prog)
  ) (at level 200, p at level 201).

Local Example mt_of_test : MT_OF (fun x:nat => forall y:nat, M nat).
Proof. apply _. Qed.
(* Set Printing All. *)
Set Printing Universes.
Definition bluf := (fun x:(nat:Type) => forall y:(nat:Type), M (nat:Type)).
Eval hnf in ltac:(mrun (MTele_of (bluf))).
Local Example test1 :=
    let mt1 := ltac:(mrun (MTele_of bluf)) in
    let _ := ltac:(mrun (let mt1 := reduce (RedOneStep [rl:RedDelta]) mt1 in M.print_term mt1)) in
    ltac:(mrun(tc_unify_mtac _ (fun _z : (nat:Type) => MTele_ty M (mprojT2 (mt1 _z))) ((fun x:(nat:Type) => forall y:(nat:Type), M (nat:Type))))).


Local Program Example mtmmatch_prog_test (x : (nat : Type)) :=
  mtmmatch_prog x as x return forall y, M (x = y) with
  | [?i] i =n>  fun y => M.failwith ""
end.

Canonical Structure CS_UNIFY_REFl {T} (A : T) : CS_UNIFY T := CS_Unify _ A A meq_refl.
Arguments cs_unify [_ _].


Definition mtpbase_eq {A} {m : A -> Prop} (x : A) F (eq : m x =m= F x) : F x -> Unification -> mtpattern A m :=
  match eq in _ =m= R return R -> _ -> _ with
  | meq_refl => mtpbase x
  end.


Bind Scope mtpattern_scope with mtpattern.
Delimit Scope mtpattern_scope with mtpattern.


Polymorphic Class MTY_OF {A} := MTt_Of { mty_of : A -> Prop }.
Arguments MTt_Of [_] _.

Polymorphic Class RET_TY (A : Type) := Ret_Ty { ret_ty : A }.
Arguments Ret_Ty [_] _.
Arguments ret_ty [_ _].

Notation "[¿ s .. t ] ps" := (mtpsort (m:=mty_of) (fun s => .. (mtpsort (m:=mty_of) (fun t => ps)) ..))
  (at level 202, s binder, t binder, ps at next level, only parsing) : mtpattern_scope.
Notation "'[S?' s .. t ] ps" := (mtpsort (m:=mty_of) (fun s => .. (mtpsort (m:=mty_of) (fun t => ps)) ..))
  (at level 202, s binder, t binder, ps at next level) : mtpattern_scope.

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
    let mt1 := M.eval (MTele_of (fun y => T)) in
    let mt : MTY_OF := MTt_Of (fun _z => MTele_ty M (n:=mprojT1 (mt1 _z)) (mprojT2 (mt1 _z))) in
    mtmmatch' _ (fun y => mprojT1 (mt1 y)) (fun y => mprojT2 (mt1 y)) x p%with_mtpattern
  ) (at level 90, p at level 91).