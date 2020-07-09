From Mtac2 Require Import Sorts Specif.
Import Sorts.S.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Polymorphic Inductive Cumulativity.
Set Printing Coercions.
(* Set Printing Universes. *)

(** MTele: a telescope which represent nested binder

   This will be used to represent legal types of patterns and fixpoints.

 *)
Inductive MTele : Type :=
| mBase : MTele
| mTele {X : Type} (F : X -> MTele) : MTele
.

(** MTele_Const : A constant (i.e. binder independent) type-level interpretation
of MTele. It constructs `∀ x .. z, T`. *)
Fixpoint MTele_Const {s : Sort} (T : s) (n : MTele) : s :=
match n with
| mBase => T
| mTele F => ForAll (fun x => MTele_Const T (F x))
end.
Definition MTele_ConstP (T : Prop) (n : MTele) : Prop := @MTele_Const Propₛ T n.
Definition MTele_ConstT (T : Type) (n : MTele) : Type := @MTele_Const Typeₛ T n.

Fixpoint MTele_const {s : Sort} {T : s} {n : MTele} : @MTele_Const s T n -> stype_of s :=
  match n return MTele_Const T n -> _ with
  | mBase => fun _ => T
  | mTele F => fun C => ForAll (fun x => MTele_const (App C x))
  end.

Definition MTele_constP {T : Prop} {n} : MTele_ConstP T n -> Prop := @MTele_const Propₛ T n.
Definition MTele_constT {T : Type} {n} : MTele_ConstT T n -> Type := @MTele_const Typeₛ T n.

(** MTele_Sort: compute `∀ x .. z, Type` from a given MTele *)
Definition MTele_Sort (s : Sort) (n : MTele) : Type := MTele_ConstT (stype_of s) n.
Fixpoint MTele_Sort' (s : Sort) (n : MTele) : Type :=
  match n with
  | mBase => stype_of s
  | mTele F => forall x, MTele_Sort' s (F x)
  end.
(* Lemma MTele_Sort_eq s n : MTele_Sort s n -> MTele_Sort' s n. *)
(* Proof. induction n. intros H. exact H. intros H x. apply X0. apply H. Qed. *)

(* Lemma MTele_Sort_eq' s n : MTele_Sort' s n -> MTele_Sort s n. *)
(* Proof. induction n. intros H. exact H. cbn. intros H x. apply X0. apply H. Qed. *)

Definition MTele_Ty := (MTele_Sort Typeₛ).
Definition MTele_Pr := (MTele_Sort Propₛ).

(* Definition MTele_sort {s : Sort} {n : MTele} : MTele_Sort s n -> Type := @MTele_constT _ n. *)
Fixpoint MTele_sort {s : Sort} {n : MTele} :
  forall S : MTele_Sort s n, Type :=
  match n return MTele_Sort s n -> _ with
  | mBase => fun S => selem_of S
  | mTele F => fun S => forall x, MTele_sort (S x)
  end.

(** Register MTele_ty as a coercion so that we can pretend any `MTele` is a
    type. *)
(* Coercion MTele_Ty : MTele >-> Sortclass. *)

(** MTele_val: compute `λ x .. z, T x .. z` from `T : MTele_ty n` *)
Fixpoint MTele_val {s} {n : MTele} : MTele_Sort s n -> s :=
  match n as n return MTele_Sort s n -> s with
  | mBase => fun f => f
  | mTele F => fun f => ForAll (fun x => MTele_val (f x))
  end.

Definition MTele_valT {n} : MTele_Ty n -> Type :=
  MTele_val (s := Typeₛ) (n:=n).
  (* ltac:( *)
  (*   let e := constr:(MTele_val (s := Typeₛ) (n:=n)) in *)
  (*   let e := (eval red in e) in *)
  (*   let e := (eval cbv match beta delta [ForAll stype_of] in e) in *)
  (*   let e := (eval fold MTele_Ty in e) in *)
  (*   exact e). *)
Definition MTele_valP {n} : MTele_Pr n -> Prop :=
  MTele_val (s := Propₛ) (n:=n).

(* Coercion MTele_valT : MTele_Ty >-> Sortclass. *)


(** Currying and Uncurrying for Telescope Types and Functions *)
Fixpoint ArgsOf (m : MTele) : Type :=
  match m with
  | mBase => unit
  | mTele f => msigT (fun x => ArgsOf (f x))
  end.

Fixpoint apply_const {s : Sort} {m : MTele} {T : s} :
  MTele_Const T m -> ArgsOf m -> T :=
  match m with
  | mBase => fun t _ => t
  | mTele f => fun t '(mexistT _ x U) => apply_const (App t x) U
  end.

Definition apply_constT {m : MTele} {T : Typeₛ} := @apply_const Typeₛ m T.
Definition apply_constP {m : MTele} {T : Prop} := @apply_const Propₛ m T.

Definition apply_sort {s : Sort} {m : MTele} :
  MTele_Sort s m -> ArgsOf m -> stype_of s :=
  @apply_const Typeₛ m (stype_of s).

Fixpoint apply_val {s : Sort} {m : MTele} :
  forall {T : MTele_Sort s m} (v : MTele_val T) (a : ArgsOf m), apply_sort T a :=
  match m with
  | mBase => fun _ v _ => v
  | mTele f => fun _ v '(mexistT _ x U) => apply_val (App v x) U
  end.

Fixpoint curry_const {s : Sort} {m : MTele} {T : s} : (ArgsOf m -> T) -> MTele_Const T m :=
  match m with
  | mBase => fun f => f tt
  | mTele F => fun f => Fun (fun x => curry_const (fun a => f (mexistT (fun x => ArgsOf _) x a)))
  end.

Definition curry_sort (s : Sort) {m : MTele} : _ -> MTele_Sort s m :=
  @curry_const Typeₛ m (stype_of s).

Fixpoint curry_val {s : Sort} {m : MTele} :
  forall {T : MTele_Sort s m}, (forall a: ArgsOf m, apply_sort T a) -> MTele_val T :=
  match m with
  | mBase => fun T f => f tt
  | mTele F => fun T f => Fun (fun x => curry_val (fun a => f (mexistT _ _ _)))
  end.


(** Convert a MTele_Const `C : ∀ x .. z, T` into a dependently-typed
telescope type `∀ x .. z, C x .. z` *)
Fixpoint MTele_ConstSort {s : Sort} {n : MTele} : forall {T : s} (C : MTele_Const T n), MTele_Sort s n :=
  match n with
  | mBase => fun T _ => T
  | mTele F => fun _ C t => MTele_ConstSort (App C t)
  end.


(** MTele_To: recursively apply the given functor G to binders and return B at
the base. MTele_Sort and MTele_val could be instances of this if we were to wrap
∀ and λ in definitions. *)
Fixpoint MTele_To {s : Sort} (B : s) (G: forall X, (X -> s) -> s) (n : MTele) : s :=
  match n as n return s with
  | mBase => B
  | mTele F => G _ (fun x => MTele_To B G (F x))
  end.

Fixpoint MTele_to {s : Sort} {B : s} {G: forall X, (X -> s) -> s} {n : MTele} (b : B) (g : forall X F, G X F) :
  MTele_To B G n :=
    match n as n return MTele_To B G n with
    | mBase => b
    | mTele F => g _ _
    end.


(* Fixpoint MTele_ConstMap {si : Sort} (so : Sort) {n : MTele} {T : si} (G : T -> so) : forall (C : MTele_Const T n), MTele_Sort so n := *)
(*   match n with *)
(*   | mBase => fun C => G C *)
(*   | mTele F => fun C t => MTele_ConstMap so G (App C t) *)
(*   end. *)

Definition MTele_ConstMap {si : Sort} (so : Sort) {n : MTele} {T : si} (G : T -> so) : forall (C : MTele_Const T n), MTele_Sort so n :=
  fun C => curry_sort so (fun a => G (apply_const C a)).

Fixpoint MTele_constmap_app {si : Sort} (so : Sort) {n : MTele} {T : si} {A : Type} (G : T -> A -> so) {struct n} :
  forall (C : MTele_Const T n), MTele_sort (@MTele_ConstMap si so n T ((fun x => ForAll (fun a => G x a))) C) ->
                                forall a : A,
                                  MTele_sort (@MTele_ConstMap si so n T (fun x => G x a) C) :=
  match n with
  | mBase => fun C f a => App f a
  | mTele F => fun C f a t => MTele_constmap_app _ _ _ (f _) a
  end.

Fixpoint apply_ConstMap {si so : Sort} {n : MTele} {T : si} {G : T -> so} :
  forall {C : MTele_Const T n} (v : MTele_val (MTele_ConstMap so G C)), forall a : ArgsOf n, G (apply_const C a) :=
  match n with
  | mBase => fun T v a => v
  | mTele F => fun T v '(mexistT _ x a) => apply_ConstMap (App v x) a
  end.

Fixpoint curry_ConstMap {si so : Sort} {n : MTele} {T : si} {G : T -> so} :
  forall {C : MTele_Const T n}, (forall a, G (apply_const C a)) -> MTele_val (MTele_ConstMap so G C) :=
  match n with
  | mBase => fun T f => f tt
  | mTele F => fun T f => Fun (fun x => curry_ConstMap (fun a => f (mexistT _ _ _)))
  end.


(** MTele_C: MTele_map with a constant function *)
Definition MTele_C (s so : Sort) {n : MTele} :
  (s -> so) -> MTele_Sort s n -> MTele_Sort so n :=
  fun G T => MTele_ConstMap (si:=Typeₛ) (T:=stype_of s) so G T.

Fixpoint MTele_c (s so : Sort) {n : MTele} :
  forall (G : s -> so)
         (g : ForAll G)
         (T : MTele_Sort s n),
  MTele_val T -> MTele_val (MTele_C _ _ G T) :=
  match n with
  | mBase => fun G g T v => App g _
  | mTele F => fun G g T v => Fun (fun x => MTele_c s so G g (T x) (App v x))
  end.

Definition apply_C {s : Sort} (so : Sort) {n : MTele} {G : s -> so}
  {T : MTele_Sort s n} : MTele_val (MTele_C _ so G T) -> forall a : ArgsOf n, G (apply_sort T a) :=
  apply_ConstMap.

Definition curry_C {s : Sort} (so : Sort) {n : MTele} {G : s -> so} {T : MTele_Sort s n} : (forall a, G (apply_sort T a)) -> MTele_val (MTele_C s so G T) :=
  curry_ConstMap.

(* Old MTele functions redefined on top of the more general newer ones above *)

Definition MTele_ty (M : Type -> Prop) {n : MTele} :
  forall A : MTele_Ty n, Prop :=
  fun A => MTele_val (MTele_C Typeₛ Propₛ M A).

Notation MT_Acc R T := (forall (M' : Type -> Prop), MTele_ty M' T -> M' R).

(* MTele_open: old telescope accessor *)
Fixpoint MTele_open (M : Type -> Prop) {X : Type -> Prop} {m}:
  forall (T : MTele_Ty m),
    (forall R, MT_Acc R T -> X R) -> MTele_ty X T  :=
  match m as m' return forall T : MTele_Ty m', (forall R, MT_Acc R T -> X R) -> MTele_ty X T with
  | mBase => fun T b => b _ (fun X x => x)
  | mTele F => fun T b x => MTele_open M (T x) (fun R f => b R (fun M' mR => f M' (mR x)))
  end.


Module TeleNotation.
  Notation "'[tele' x .. z ]" :=
    (mTele (fun x => .. (mTele (fun z => mBase)) ..))
      (x binder, z binder, format "[tele  '[hv' x  ..  z ']'  ]").

  Notation "'[tele' ]" := (mBase).
End TeleNotation.
