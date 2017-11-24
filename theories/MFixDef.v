From Mtac2 Require Import Base MTele.
Import M.notations.

Notation MFA := (MTele_ty M).

Fixpoint UNCURRY (m : MTele) : Type :=
  match m with
  | mBase T => unit
  | mTele f => sigT (fun x => UNCURRY (f x))
  end.

Fixpoint RETURN (m : MTele) : UNCURRY m -> Type :=
  match m with
  | mBase T => fun _ => T
  | mTele f => fun '(existT _ x U) => RETURN _ U
  end.

Fixpoint uncurry (m : MTele) : MFA m -> forall U : UNCURRY m, M (RETURN _ U) :=
  match m with
  | mBase T => fun F _ => F
  | mTele f => fun F '(existT _ x U) => uncurry (f x) (F x) U
  end.

Fixpoint curry (m : MTele) : (forall U : UNCURRY m, M (RETURN _ U)) -> MFA m :=
  match m with
  | mBase T => fun F => F tt
  | mTele f => fun F x => curry (f x) (fun U => F (existT _ x U))
  end.

Definition mfix' (m : MTele) (F : MFA m -> MFA m) : MFA m :=
  curry m (mfix1 rec (U : _) : M _ := uncurry m (F (curry m rec)) U).

(* Definition mfix' (m : MTele) (F : MFA m -> MFA m) : MFA m := *)
(*   curry m (M.fix1 _ (fun rec => uncurry m (F (curry m rec)))). *)
