From Mtac2 Require Import Base Specif MTele.
Import Sorts.S.
Import M.notations.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Local Notation MFA T := (MTele_val (MTele_C SType SProp M T)).

Fixpoint uncurry {m : MTele} :
  forall {T : MTele_Ty m},
  MFA T -> forall U : ArgsOf m, M (apply_sort T U) :=
  match m as m return
        forall T : MTele_Ty m,
          MFA T -> forall U : ArgsOf m, M (apply_sort T U)
  with
  | mBase => fun T F _ => F
  | mTele f => fun T F '(mexistT _ x U) => uncurry (F x) U
  end.

Fixpoint curry {m : MTele} :
  forall {T : MTele_Ty m},
  (forall U : ArgsOf m, M (apply_sort T U)) -> MFA T :=
  match m with
  | mBase => fun T F => F tt
  | mTele f => fun T F x => curry (fun U => F (mexistT _ x U))
  end.

Definition mfix' {m : MTele} (T : MTele_Ty m) (F : MFA T -> MFA T) : MFA T :=
  curry (mfix1 rec (U : _) : M _ := uncurry (F (curry rec)) U).

(* Definition mfix' (m : MTele) (F : MFA m -> MFA m) : MFA m := *)
(*   curry m (M.fix1 _ (fun rec => uncurry m (F (curry m rec)))). *)
