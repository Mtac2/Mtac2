From Mtac2 Require Import Base MTele.
Import Sorts.S.
Import M.notations.

Set Polymorphic Inductive Cumulativity.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Local Notation MFA T := (MTele_val (MTele_C SType SProp M T)).

Fixpoint UNCURRY (m : MTele) : Type :=
  match m with
  | mBase => unit
  | mTele f => sigT (fun x => UNCURRY (f x))
  end.

Fixpoint RETURN {m : MTele} : MTele_Ty m -> UNCURRY m -> Type :=
  match m with
  | mBase => fun T _ => T
  | mTele f => fun T '(existT _ x U) => RETURN (T x) U
  end.

Fixpoint uncurry {m : MTele} :
  forall {T : MTele_Ty m},
  MFA T -> forall U : UNCURRY m, M (RETURN T U) :=
  match m as m return
        forall T : MTele_Ty m,
          MTele_val (MTele_C SType SProp M T) -> forall U : UNCURRY m, M (RETURN _ U)
  with
  | mBase => fun T F _ => F
  | mTele f => fun T F '(existT _ x U) => uncurry (F x) U
  end.

Fixpoint curry {m : MTele} :
  forall {T : MTele_Ty m},
  (forall U : UNCURRY m, M (RETURN T U)) -> MFA T :=
  match m with
  | mBase => fun T F => F tt
  | mTele f => fun T F x => curry (fun U => F (existT _ x U))
  end.

Definition mfix' {m : MTele} (T : MTele_Ty m) (F : MFA T -> MFA T) : MFA T :=
  curry (mfix1 rec (U : _) : M _ := uncurry (F (curry rec)) U).

(* Definition mfix' (m : MTele) (F : MFA m -> MFA m) : MFA m := *)
(*   curry m (M.fix1 _ (fun rec => uncurry m (F (curry m rec)))). *)
