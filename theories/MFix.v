From Mtac2 Require Import Mtac2 MTeleMatch.

Check M.fix1.

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

Definition mfix (m : MTele) (F : MFA m -> MFA m) : MFA m :=
  curry m (mfix1 rec (U : _) : M _ := uncurry m (F (curry m rec)) U).

Definition mfix' (m : MTele) (F : MFA m -> MFA m) : MFA m :=
  curry m (M.fix1 _ (fun rec => uncurry m (F (curry m rec)))).

Definition Mmap {A B} (f : A -> M B) : list A -> M (list B) :=
  mfix (mTele (fun _ : list A => mBase (list B)))
       (fun (rec : list A -> M (list B)) la =>
          mmatch la with
       | nil => M.ret nil
       | [?a la] cons a la => b <- f a; lb <- rec la; M.ret (cons b lb)
        end
       ).

Definition Mmap1 {A B} (f : A -> M B) : list A -> M (list B) :=
  M.fix1 ((fun _ : list A => (list B)))
       (fun (rec : list A -> M (list B)) la =>
          mmatch la with
       | nil => M.ret nil
       | [?a la] cons a la => b <- f a; lb <- rec la; M.ret (cons b lb)
        end
       ).


From Mtac2 Require Import Debugger List.
Import Mtac2.List.ListNotations.

Time Compute ltac:(mrun
                (
                   (Mmap (fun b => M.ret (negb b)) (List.repeat true 2000));; M.ret tt
                )
             ).

Time Compute ltac:(mrun
                (
                   (Mmap1 (fun b => M.ret (negb b)) (List.repeat true 2000));; M.ret tt
                )
             ).
