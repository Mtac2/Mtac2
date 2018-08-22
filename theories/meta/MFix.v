From Mtac2 Require Import Base Logic Datatypes MFixDef MTele MTeleMatch.
Import M.notations.
Import Sorts.S.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.


Local Definition MFA {n} (T : MTele_Ty n) := (MTele_val (MTele_C SType SProp M T)).

(* Less specific version of MTele_of in MTeleMatch.v *)
Definition MTele_of' :=
  (mfix1 f (T : Prop) : M { m : MTele & { mT : MTele_Ty m & T =m= MFA mT } } :=
     mmatch T as T0 return M { m : MTele & { mT : MTele_Ty m & T =m= MFA mT } } with
     | [?X : Type] M X =u> [H]
                        M.ret (existT (fun m => {mT : MTele_Ty m & T =m= MFA mT}) (mBase)
                                      (existT (fun mT : MTele_Ty mBase => T =m= MFA mT) _ H)
                              )
     | [?(X : Type) (F : forall x:X, Prop)] (forall x:X, F x) =c> [H]
       M.nu (FreshFrom F) mNone (fun x =>
                       ''(existT _ m (existT _ mT E)) <- f (F x);
                       m' <- M.abs_fun x m;
                       mT' <- (M.coerce mT >>=
                               M.abs_fun (P:=fun x => MTele_Ty (m' x)) x);
                       (* E' <- (M.abs_fun x E >>= M.coerce (B:=_ =m= MFA mT')); *)
                       E' <- M.coerce (@meq_refl _ (MFA (n:=mTele m') mT'));
                       M.ret (existT _ (mTele m') (existT _ mT' E'))
                       (* mf <- M.abs_fun (P:=fun x => {m : _ & F x =m= MFA m}) x mf; *)
                       (* let g := (fun x => projT1 (mf x)) in *)
                       (* let h := (fun x => projT2 (mf x)) in *)
                       (* e <- M.evar ((forall x, F x) =m= MFA (mTele g)); *)
                       (* er <- M.coerce (meq_refl (forall x, F x)); *)
                       (* M.unify e er UniEvarconv;; *)
                       (* M.ret (existT (fun m => (forall x:X, F x) =m= MFA m) (mTele g) e) *)
                    )
   end
  ).

Definition MTele_of : Prop -> M (sigT MTele_Ty) :=
  mfix1 f (T : Prop) : M (sigT MTele_Ty) :=
     mmatch T return M (sigT MTele_Ty) with
     | [?X : Type] M X =u> M.ret (existT _ mBase X)
     | [?(X : Type) (F : forall x:X, Prop)] (forall x:X, F x) =c>
       M.nu (FreshFrom F) mNone (fun x =>
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


Set Use Unicoq.

Structure execV {A} (f : M A) B := ExecV { value : B } .

Monomorphic Canonical Structure the_value {A} (f : M A) v := ExecV _ f (lift f v) v.

Arguments value {A} f {B} {e}.

Notation "'[run'  t ]" :=
((let H := _ in let _ : value (t) = H := eq_refl in H)).

Definition exec {A} (f : M A) {v:A} : lift f v := v.

Notation "'[ex'  t ']'" := (exec t) (at level 0).

Definition mfix_eq {m : MTele} {T: MTele_Ty m} {A : Prop} : forall {Eq : MFA T =m= A}, (A -> A) -> A :=
  fun eq => match eq in _ =m= R return (R -> R) -> R with
            | meq_refl => fun f => mfix' _ f
            end.

Definition mfix_lift {m : MTele} {A : Prop} {F : (A -> A) -> A}:
  lift (
     ''(existT _ m' (existT _ mT E)) <-mtry  MTele_of' A
        with
    | [?E] E =>
      M.print_term E;;
      M.evar _
      end;
      M.unify m m' UniCoq;;
        match meq_sym E in _ =m= R return M ((R -> R) -> R) with
        | meq_refl => M.ret (mfix' mT)
        end) (F) := F.

(* Eval cbn in mfix_lift  : ((nat -> M nat) -> (nat -> M nat)) -> nat -> M nat. *)
(* Definition blubb := mfix_lift (fun f (x : nat) => M.ret x). *)

Notation "'mfix' f x .. y : T := b" :=
  (
  (*   let mt := mt_of (forall x, .. (forall y, T) ..) in *)
  (*   match tc_unify ((forall x, .. (forall y, T) .. )) (MTele_ty M (n:=projT1 mt) (projT2 mt)) *)
  (*         in _ =m= R return ((R -> R) -> R) -> R with *)
  (*   | meq_refl => fun g => g (fun f => (fun x => ..  (fun y => b) ..)) *)
  (*   end (mfix' (m:=projT1 mt) (projT2 mt)) *)
  (* ) (no associativity, *)
  (*    at level 85, *)
    ((mfix_lift
      :
        (* _ *)
        (* _ -> _ *)
        (* (_ -> _) -> _ *)
        ((forall x, .. (forall y, T) ..)
         -> (forall x, .. (forall y, T) ..))
        -> (forall x, .. (forall y, T) ..)
     )
       (fun f => (fun x => .. (fun y => b) ..))
    )
  ) (only parsing,
      no associativity,
     at level 85,
     f ident,
     x binder,
     y binder,
     (* T at level 0, *)
     format "mfix  f  x  ..  y  :  T  :=  b"
    ).

Definition bla := mfix f (x : nat) : True -> M True := fun i => f x i.