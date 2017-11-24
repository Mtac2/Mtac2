(** MTele: a telescope which represents functions of the type
      `X -> ... -> Z -> M R`
    where R may depend on the value given for X and Y

   This will be used to represent legal types of patterns and fixpoints.
 *)
Inductive MTele : Type :=
| mBase (R : Type) : MTele
| mTele {X : Type} (F : X -> MTele) : MTele
.

Notation "'[tele' x .. y , b ]" := (mTele (fun x => .. (mTele (fun y => mBase b)) .. )) (at level 100, x binder, y binder).

(** MTele_ty: calculate `X -> ... -> Z -> M R` from a given MTele

   To be able to use this in the definition of M.t itself, we paramatrize by M.
*)
Fixpoint MTele_ty M (m : MTele) : Prop :=
  match m with
  | mBase R => M R
  | @mTele X F => forall (x : X), MTele_ty M (F x)
  end.

(** Constant MTele_ty *)
Fixpoint MTele_C (M : Type -> Prop) (b : forall R, M R) m : MTele_ty M m :=
  match m with
  | mBase R => b R
  | mTele F => fun x => MTele_C M b (F x)
  end.


Fixpoint MTele_map' (M : Type -> Prop) {X : forall R :Type, Prop} (m : MTele) : forall (f : MTele_ty (fun R => M R -> X R) m), MTele_ty M m -> MTele_ty (fun R => X R) m :=
  match m as m' return _ m' -> MTele_ty M m' -> MTele_ty _ m' with
  | mBase R => fun (f : M R -> X R) (t : M R) => f t
  | mTele F => fun (f : forall x : _, MTele_ty _ (F x)) (t : forall x : _, MTele_ty M (F x)) =>
                 fun x : _ => MTele_map' M (F x) (f x) (t x)
  end.

Fixpoint MTele_mkfunc (M : Type -> Prop) {X : Type -> Prop} (b : forall R, M R -> X R) (m : MTele) : MTele_ty (fun R => M R -> X R) m :=
  match m as m' return MTele_ty (fun R => M R -> X R) m' with
  | mBase R => fun t => b _ t
  | mTele F => fun x => MTele_mkfunc M b (F x)
  end.

Notation MT_Acc R m := (forall (M' : Type -> Prop), MTele_ty M' m -> M' R).

Fixpoint MTele_open (M : Type -> Prop) {X : Type -> Prop} m :
  (forall R, MT_Acc R m -> X R) -> MTele_ty X m  :=
  match m as m' return (forall R, MT_Acc R m' -> X R) -> MTele_ty X m' with
  | mBase R => fun b => b R (fun M' x => x)
  | mTele F => fun b x => MTele_open M (F x) (fun R f => b R (fun M' mR => f M' (mR x)))
  end.

Definition MTele_map (M : Type -> Prop) {X : Type -> Prop}  (b : forall R, M R -> X R) (m : MTele) : MTele_ty M m -> MTele_ty (fun R => X R) m :=
  MTele_map' M _ (MTele_mkfunc _ b m).
