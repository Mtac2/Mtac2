From Mtac2 Require Import Mtac2 MTeleMatch.

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


(* Less specific version of MTele_of in MTeleMatch.v *)
Definition MTele_of :=
  (mfix1 f (T : Prop) : M (MTele) :=
                    mmatch T as t' return M MTele with
                                        | [?X : Type] M X =u> M.ret (mBase X)
                                        | [?(X : Type) (F : forall x:X, Prop)] (forall x:X, F x)
                                          =c>
                                           b <- M.fresh_binder_name F;
                                          f <- M.nu b None (fun x =>
                                                 g <- f (F x);
                                                 M.abs_fun x g);
                                          M.ret (mTele f)
   end
  ).

Class MT_OF (T : Prop) := mt_of : MTele.
Arguments mt_of _ {_}.
Hint Extern 0 (MT_OF ?t) => mrun (MTele_of t) : typeclass_instances.

(* This is notation is not nice. To appease Coq's restrictions on notations
   (which I don't understand) we have to use unification to change the type of
   [mfix'] instead of the type of the function given by the user.
   The notation also will not print even though Coq does not complain about
   irreversibility.
 *)
Notation "'mfix' f x .. y : T := b" :=
  (
    let m := mt_of (forall x, .. (forall y , T) ..) in
    match tc_unify ((forall x, .. (forall y, T) .. )) (MTele_ty M m)
          in _ = R return ((R -> R) -> R) -> R with
    | eq_refl => fun g => g (fun f => (fun x => ..  (fun y => b) ..))
    end (mfix' m)
  ) (no associativity,
     at level 85,
     f ident,
     x closed binder,
     y closed binder,
     (* T at level 0, *)
     format "mfix  f  x  ..  y  :  T  :=  b"
    ).