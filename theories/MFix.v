From Mtac2 Require Import Base Logic Datatypes MFixDef MTele MTeleMatch.
Import M.notations.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(* Less specific version of MTele_of in MTeleMatch.v *)
Polymorphic Definition MTele_of : Prop -> M (sigT MTele_Ty) :=
  mfix1 f (T : Prop) : M (sigT MTele_Ty) :=
     mmatch T return M (sigT MTele_Ty) with
     | [?X : Type] M X =u> M.ret (existT _ mBase X)
     | [?(X : Type) (F : forall x:X, Prop)] (forall x:X, F x) =c>
       b <- M.fresh_binder_name F;
       M.nu b mNone (fun x =>
                       ''(existT _ n T) <- f (F x);
                       n' <- M.abs_fun (P:=fun _ => MTele) x n;
                       T' <- M.abs_fun x T;
                       T' <- M.coerce T';
                       M.ret (existT _ (mTele n') T')
                    )
   end
.

Class MT_OF (T : Prop) := mt_of : sigT MTele_Ty.
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
    let mt := mt_of (forall x, .. (forall y, T) ..) in
    match tc_unify ((forall x, .. (forall y, T) .. )) (MTele_ty M (n:=projT1 mt) (projT2 mt))
          in _ =m= R return ((R -> R) -> R) -> R with
    | meq_refl => fun g => g (fun f => (fun x => ..  (fun y => b) ..))
    end (mfix' (m:=projT1 mt) (projT2 mt))
  ) (no associativity,
     at level 85,
     f ident,
     x closed binder,
     y closed binder,
     (* T at level 0, *)
     format "mfix  f  x  ..  y  :  T  :=  b"
    ).