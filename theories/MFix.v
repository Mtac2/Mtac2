From Mtac2 Require Import Base Logic Datatypes MFixDef MTele MTeleMatch.
Import M.notations.

(* Less specific version of MTele_of in MTeleMatch.v *)
Definition MTele_of :=
  (mfix1 f (T : Prop) : M (MTele) :=
     mmatch T as t' return M MTele with
     | [?X : Type] M X =u> M.ret (mBase X)
     | [?(X : Type) (F : forall x:X, Prop)] (forall x:X, F x) =c>
       b <- M.fresh_binder_name F;
       f <- M.nu b mNone (fun x =>
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
          in _ =m= R return ((R -> R) -> R) -> R with
    | meq_refl => fun g => g (fun f => (fun x => ..  (fun y => b) ..))
    end (mfix' m)
  ) (no associativity,
     at level 85,
     f ident,
     x closed binder,
     y closed binder,
     (* T at level 0, *)
     format "mfix  f  x  ..  y  :  T  :=  b"
    ).