From Mtac2 Require Import Base Datatypes List MTeleMatch MFix.
Import M.notations.
Import Mtac2.List.ListNotations.

Local Inductive msigT {A} (P : A -> Type) : Type := | mexistT x : P x -> msigT P.
Local Notation "'{$'  x .. y  &  P }" := (msigT (fun x => .. (msigT (fun y => P)) .. )) (x binder, y binder).
Local Definition mprojT1 {A} {P} : @msigT A P -> A := fun '(mexistT _ x _) => x.
Local Definition mprojT2 {A} {P} : forall s : @msigT A P, P (mprojT1 s) := fun '(mexistT _ _ p) => p.
Local Inductive TTele : Type :=
| ttbase (X : Type) : TTele
| tttele {X} : (X -> TTele) -> TTele.
Fixpoint TTele_ty (M : Type -> Type) t :=
  match t with
  | ttbase X => M X
  | tttele F => forall x, TTele_ty M (F x)
  end.

Local Fixpoint TTele_bind {X} {t} : (X -> TTele_ty M t) -> (TTele_ty M.t t) :=
  match t with
  | ttbase X => M.bind (M.evar _)
  | tttele F => fun f (t : _) => @TTele_bind X (F t) (fun x : X => f x t)
  end
.

Local Fixpoint func_of (l : mlist Prop) :=
  match l with
  | mnil => True
  | mcons T l => prod T (func_of l)
end.

Local Notation "x -*> y" := (prod (func_of x) y) (only parsing, at level 91).

Local Notation tty := (TTele_ty (fun T => msigT (fun l => M (l -*> T)))).

Local Fixpoint TTele_bind' {X : Prop} (x : X) {t} : (TTele_ty (fun T => msigT (fun l => X -> M (l -*> T))) t) -> (tty t) :=
  match t with
  | ttbase B => fun '(mexistT _ l f) => mexistT _ (X :m: l) (
                  H <- M.evar X;
                  ''(goals, R) <- f H;
                  M.ret ((H,goals), R))
  | tttele F => fun f t =>
                  TTele_bind' x (f t)
  end
.

Definition lift_lemma : forall (A : Prop), A ->
      M (msigT tty) :=
  mfix' ([tele  (A : Prop) (a:A), msigT tty])
        (fun rec (A : Prop) =>
           let m (A : Prop) := [tele (a:A), _] in
           mtmmatch'
             _ m A
             [m:
              (mtptele (fun B:Prop => mtptele (fun (C:Prop) => (mtpbase (m:=fun A:Prop => A -> M _)) _ (
              fun (f : B -> C) =>
                n <- M.fresh_binder_name A;
                M.nu n mNone (fun b : B =>
                               ''(mexistT _ t X) <- rec C (f b);
                               match t as t return tty t -> M (_) with
                               | tttele _ =>
                                 fun _ =>
                                   M.failwith "Lemma to be lifted has dependent quantifiers after non-dependent ones. This is not supported."
                               | ttbase P => fun f =>
                                               let '(mexistT _ l f) := f in
                                               f' <- M.abs_fun b f;
                                               f' <- M.coerce f';
                                               let T' := reduce (RedWhd RedAll)
                                                                (TTele_bind' b (t:=ttbase _) (mexistT _ l f')) in
                                          M.ret (mexistT tty (ttbase P) T')
                               end X
                     )
              ) UniMatchNoRed)))%mtpattern
             |
             (mtptele (fun B:Type => mtptele (fun (C:B -> Prop) => (mtpbase (m:=fun A:Prop => A -> M _)) _ (
              fun (f : forall b:B, C b) =>
                n <- M.fresh_binder_name A;
                M.nu n mNone (fun b : B =>
                               ''(mexistT _ t X) <- rec _ (f b);
                               t' <- M.abs_fun b t;
                               X <- M.coerce X;
                               X' <- M.abs_fun (P:=fun b => tty (t' b)) b X;
                               M.ret (mexistT tty (tttele t') (fun x => X' x))
                     )
              ) UniMatchNoRed)))%mtpattern
              |
              (mtpbase (m:=fun A:Prop => A -> M _) A
                       (fun a:A =>
                          M.ret (mexistT tty (ttbase A) (mexistT _ mnil (M.ret (I,a))))
                       )
                       UniCoq
              )%mtpattern
             ]%with_mtpattern
        )
.


Local Fixpoint TTele_App {P1} {t} (P2 : forall T (H : P1 T), Type) : TTele_ty P1 t -> Type :=
  match t with
  | ttbase P => fun x => P2 _ x
  | tttele F => fun g => forall x, TTele_App P2 (g x)
  end.

Local Fixpoint TTele_app {P1} {t} P2 (f : forall T PT, P2 T PT) : forall tt, TTele_App (P1:=P1) (t:=t) P2 tt :=
match t with
| ttbase T => fun tt : P1 T => f _ _
| tttele F => fun (tt : forall t, TTele_ty P1 (F t)) t => @TTele_app _ (F t) _ f (tt t)
end.

Definition do_def n {A:Prop} (a:A) :=
  ''(mexistT _ t f) <- lift_lemma A (a);
  (* let f := reduce (RedStrong [rl: RedBeta; RedZeta; RedFix; RedMatch; RedDeltaOnly [rl: Dyn (@M.type_of); Dyn (@TTele_ty)] ]) (f) in *)
  let x := reduce (RedStrong [rl: RedFix; RedMatch; RedBeta; RedDeltaOnly [rl: Dyn (@TTele_app)]]) (TTele_app (fun T PT => let '(mexistT _ l _) := PT in M (l -*> T))
                                                (fun T PT => let '(mexistT _ l X) := PT in
                                                             X
                                                ) f) in
  let T := reduce (RedStrong [rl: RedBeta; RedZeta; RedFix; RedMatch;
                           RedDeltaOnly [rl: Dyn (@M.type_of); Dyn (@TTele_ty); Dyn (@TTele_App); Dyn (@TTele_app); Dyn (@func_of)] ]) (M.type_of x) in
               @M.declare dok_Definition n false T x;; M.ret tt.

From Coq Require Import String.
Module Test.
Time Check ltac:(mrun (do_def "test" (@PeanoNat.Nat.lt_trans))).
Check test.
Print test.
End Test.