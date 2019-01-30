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
Definition MTele_ConstP (T : Prop) (n : MTele) : Prop := @MTele_Const SProp T n.
Definition MTele_ConstT@{i+} (T : Type@{i}) (n : MTele@{i}) : Type@{i} := @MTele_Const SType T n.

Fixpoint MTele_const {s : Sort} {T : s} {n : MTele} : @MTele_Const s T n -> stype_of s :=
  match n return MTele_Const T n -> _ with
  | mBase => fun _ => T
  | mTele F => fun C => ForAll (fun x => MTele_const (App C x))
  end.

Definition MTele_constP {T : Prop} {n} : MTele_ConstP T n -> Prop := @MTele_const SProp T n.
Definition MTele_constT {T : Type} {n} : MTele_ConstT T n -> Type := @MTele_const SType T n.

(** MTele_Sort: compute `∀ x .. z, Type` from a given MTele *)
Definition MTele_Sort@{i j k} (s : Sort) (n : MTele@{i}) : Type@{j} := MTele_ConstT@{j k} (stype_of@{j i} s) n.
Fixpoint MTele_Sort' (s : Sort) (n : MTele) : Type :=
  match n with
  | mBase => stype_of s
  | mTele F => forall x, MTele_Sort' s (F x)
  end.
(* Lemma MTele_Sort_eq s n : MTele_Sort s n -> MTele_Sort' s n. *)
(* Proof. induction n. intros H. exact H. intros H x. apply X0. apply H. Qed. *)

(* Lemma MTele_Sort_eq' s n : MTele_Sort' s n -> MTele_Sort s n. *)
(* Proof. induction n. intros H. exact H. cbn. intros H x. apply X0. apply H. Qed. *)

Definition MTele_Ty := (MTele_Sort SType).
Definition MTele_Pr := (MTele_Sort SProp).

(* Definition MTele_sort {s : Sort} {n : MTele} : MTele_Sort s n -> Type := @MTele_constT _ n. *)
Fixpoint MTele_sort@{i+} {s : Sort} {n : MTele@{i}} :
  forall S : MTele_Sort s n, Type@{i} :=
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
  MTele_val (s := SType) (n:=n).
  (* ltac:( *)
  (*   let e := constr:(MTele_val (s := SType) (n:=n)) in *)
  (*   let e := (eval red in e) in *)
  (*   let e := (eval cbv match beta delta [ForAll stype_of] in e) in *)
  (*   let e := (eval fold MTele_Ty in e) in *)
  (*   exact e). *)
Definition MTele_valP {n} : MTele_Pr n -> Prop :=
  MTele_val (s := SProp) (n:=n).

(* Coercion MTele_valT : MTele_Ty >-> Sortclass. *)


(** Convert a MTele_Const `C : ∀ x .. z, T` into a dependently-typed
telescope type `∀ x .. z, C x .. z` *)
Fixpoint MTele_ConstSort {s : Sort} {n : MTele} : forall {T : s} (C : MTele_Const T n), MTele_Sort s n :=
  match n with
  | mBase => fun T _ => T
  | mTele F => fun _ C t => MTele_ConstSort (App C t)
  end.

Fixpoint MTele_ConstMap {si : Sort} (so : Sort) {n : MTele} {T : si} (G : T -> so) : forall (C : MTele_Const T n), MTele_Sort so n :=
  match n with
  | mBase => fun C => G C
  | mTele F => fun C t => MTele_ConstMap so G (App C t)
  end.

Fixpoint MTele_constmap_app {si : Sort} (so : Sort) {n : MTele} {T : si} {A : Type} (G : T -> A -> so) {struct n} :
  forall (C : MTele_Const T n), MTele_sort (@MTele_ConstMap si so n T ((fun x => ForAll (fun a => G x a))) C) ->
                                forall a : A,
                                  MTele_sort (@MTele_ConstMap si so n T (fun x => G x a) C) :=
  match n with
  | mBase => fun C f a => App f a
  | mTele F => fun C f a t => MTele_constmap_app _ _ _ (f _) a
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


(** Accessors: An accessor is a pair of two functions called [acc_sort] and
[acc_val] respectively. They behave as follows:
- [acc_sort] converts [MTele_Sort s n] into [stype_of s]
- [acc_val] converts [MTele_val T] into [acc_sort T]

Intuitively, they are meant to represent (extensionally) "having access" to the
values for every binder in the telescope. It is possible, though, to simply
return fixed [stype_of s] values and corresponding inhabitants. *)
Set Primitive Projections.
Record accessor (n : MTele) :=
  Accessor {
      acc_const : forall {s : Sort} {T : s}, MTele_Const T n -> T;
      acc_constP {P : Prop} : MTele_ConstP P n -> P := @acc_const SProp P;
      acc_constT {T : Type} : MTele_ConstT T n -> T := @acc_const SType T;
      acc_sort {s : Sort} : MTele_Sort s n -> s := @acc_const SType _ ;
      acc_val : forall {s : Sort} (T : MTele_Sort s n), MTele_val T -> acc_sort T;
    }.
Arguments acc_const {_} _ {_} {_} _.
Arguments acc_constP {_} _ {_} _.
Arguments acc_constT {_} _ {_} _.
Arguments acc_sort {_} _ {_} _.
Arguments acc_val {_} _ {_ _} _.


(** MTele_In: Use an accessor to gain access to multiple telescoped types and
values at the same time to compute a new telescoped _type_. *)
Fixpoint MTele_In (s : Sort) {n : MTele} :
  (accessor n -> s) -> MTele_Sort s n :=
  match n as n return (accessor n -> s) -> MTele_Sort s n with
  | mBase => fun thunk => thunk (Accessor mBase (fun s T C => C) (fun _ _ v => v))
  | mTele F =>
    fun thunk t =>
      MTele_In s (fun a =>
                    thunk
                      (Accessor (mTele F)
                                (fun _ T C => a.(acc_const) (App C t))
                                (fun _ _ v => a.(acc_val) (App v t))
                      )
                 )
  end.

Notation "'[WithT' now_ty , now_val '=>' T ]" :=
  (MTele_In SType (fun '(Accessor _ now_ty now_val) => T))
    (at level 0, format "[WithT  now_ty ,  now_val  =>  T ]").

Notation "'[WithP' now_ty , now_val '=>' T ]" :=
  (MTele_In SProp (fun '(Accessor _ now_ty now_val) => T))
    (at level 0, format "[WithP  now_ty ,  now_val  =>  T ]").

(** MTele_in: gain access to potentially multiple telescoped types and values at the same time to compute a new telescoped _value_ of type `MTele_In ..`. *)
Fixpoint MTele_in (s : Sort) {n : MTele} :
  forall {thunk : accessor n -> s},
  (forall a : accessor n, thunk a)
  -> MTele_val (MTele_In (n:=n) s thunk) :=
  match n as n return
        forall thunk : accessor n -> s,
          (forall a : accessor n, thunk a)
        -> MTele_val (MTele_In (n:=n) s thunk)
  with
  | mBase =>
    fun _ thunk => thunk (Accessor mBase (fun s T C => C) (fun _ _ v => v))
  | mTele F =>
    fun _ thunk =>
      Fun (fun t =>
             MTele_in s (fun a =>
                           thunk
                             (Accessor (mTele F)
                                       (fun _ T C => a.(acc_const) (App C t))
                                       (fun _ _ v => a.(acc_val) (App v t))
                             )
                        )
          )
  end.

Notation "'[withT' now_ty , now_val '=>' t ]" :=
  (MTele_in (SType) (fun '(Accessor _ now_ty now_val) => t))
    (at level 0, format "[withT  now_ty ,  now_val  =>  t ]").

Notation "'[withP' now_ty , now_val '=>' t ]" :=
  (MTele_in (SProp) (fun '(Accessor _ now_ty now_val) => t))
    (at level 0, format "[withP  now_ty ,  now_val  =>  t ]").

(** MTele_Map: compute type `∀ x .. z, B x .. z` from type
    `∀ x .. z, A x .. z` *)
Fixpoint MTele_Map (s so : Sort) {n : MTele} :
  MTele_sort (MTele_In (SType) (n := n) (fun _ => stype_of s -> stype_of so)) -> MTele_Sort s n -> MTele_Sort so n
  :=
  match n return
        MTele_sort (MTele_In (SType) (n := n) (fun _ => stype_of s -> stype_of so)) -> MTele_Sort s n -> MTele_Sort so n
  with
  | mBase => fun f A => f A
  | mTele F => fun f A t => @MTele_Map s so (F t) (f t) (A t)
  end.

Eval cbn in MTele_In (SType).

(** MTele_C: MTele_map with a constant function *)
Fixpoint MTele_C (s so : Sort) {n : MTele} :
  (s -> so) -> MTele_Sort s n -> MTele_Sort so n :=
  match n return (s -> so) -> MTele_Sort s n -> MTele_Sort so n with
  | mBase => fun f A => f A
  | mTele F => fun f A t => MTele_C s so f (A t)
  end.

Fixpoint MTele_c (s so : Sort) {n : MTele} :
  forall (G : s -> so)
         (g : ForAll G)
         (T : MTele_Sort s n),
  MTele_val T -> MTele_val (MTele_C _ _ G T) :=
  match n with
  | mBase => fun G g T v => App g _
  | mTele F => fun G g T v => Fun (fun x => MTele_c s so G g (T x) (App v x))
  end.

(* MTele_map: map values of type `∀ x .. z, A x .. z` to values of type
   `∀ x .. z, B x .. z` *)
Fixpoint MTele_map {s} {n : MTele} :
  forall {A : MTele_Sort s n} {B :  MTele_Sort s n},
    MTele_val (MTele_In s (fun a => Impl (a.(acc_sort) A) (a.(acc_sort) B))) -> MTele_val A -> MTele_val B :=
  match n with
  | mBase => fun A B f a => App f a
  | mTele F => fun A B f a => Fun (fun t => MTele_map (App f t) (App a t))
  end.

(** MTele_id: a sanity check to see if we can witness `(∀ x .. z, A x .. z) ->
(∀ x .. z, A x .. z)` by constructing `∀ x .. z, A x .. z -> A x .. z` *)
Local Fixpoint MTele_id {s} (n : MTele) :
  forall {A : MTele_Sort s n},
    MTele_val (MTele_In s (fun a => Impl (a.(acc_sort) A) (a.(acc_sort) A))) :=
  match n  with
  | mBase => fun A => Fun (fun x : selem_of A => x)
  | mTele F => fun A => Fun (fun x => MTele_id (F x))
  end.

Local Example map_id {s} {n : MTele} {A : MTele_Sort s n} := @MTele_map s n A A (MTele_id n).

(** Partial Telescopes *)
Inductive PTele : MTele -> Type :=
| pBase {n} : PTele n
| pTele {X} {F} (x : X) : PTele (F x) -> PTele (@mTele X F).

Fixpoint PTele_MTele {n} (p : PTele n) : MTele :=
  match p with
  | pBase => n
  | pTele _ p => PTele_MTele p
  end.

Coercion PTele_MTele : PTele >-> MTele.

Fixpoint PTele_Sort {s} {n} (p : PTele n) : MTele_Sort s n -> MTele_Sort s p :=
  match p with
  | pBase => fun x => x
  | pTele _ p => fun T => PTele_Sort p (T _)
  end.



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

Definition apply_sort {s : Sort} {m : MTele} :
  MTele_Sort s m -> ArgsOf m -> stype_of s :=
  @apply_const SType m (stype_of s).

Fixpoint apply_val {s : Sort} {m : MTele} :
  forall {T : MTele_Sort s m} (v : MTele_val T) (a : ArgsOf m), selem_of (apply_sort T a) :=
  match m with
  | mBase => fun _ v _ => v
  | mTele f => fun _ v '(mexistT _ x U) => apply_val (App v x) U
  end.



(* Old MTele functions redefined on top of the more general newer ones above *)

Definition MTele_ty (M : Type -> Prop) {n : MTele} :
  forall A : MTele_Ty n, Prop :=
  fun A => MTele_val (MTele_C SType SProp M A).

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

  Notation "'[ptele' x , .. , z ]" :=
    (pTele x .. (pTele z pBase) ..)
      (format "[ptele  '[hv' x ,  .. ,  z ']'  ]").

  Notation "'[ptele' ]" := (pBase).

  (* Check [ptele 3, 5] : PTele [tele _ _ ]. *)
End TeleNotation.