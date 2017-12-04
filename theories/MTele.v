From Mtac2 Require Import Sorts.
Import Sorts.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(** MTele: a telescope which represent nested binder

   This will be used to represent legal types of patterns and fixpoints.

 *)
Inductive MTele : Type :=
| mBase : MTele
| mTele {X : Type} (F : X -> MTele) : MTele
.

(** MTele_Sort: compute `∀ x .. z, Type` from a given MTele *)
Fixpoint MTele_Sort (s : Sort) (n : MTele) : Type :=
  match n with
  | mBase => s
  | mTele F => forall x, MTele_Sort s (F x)
  end.

Definition MTele_Ty := (MTele_Sort SType).
Definition MTele_Pr := (MTele_Sort SProp).

Fixpoint MTele_sort {s : Sort} {n : MTele} :
  forall S : MTele_Sort s n, Type :=
  match n return MTele_Sort s n -> Type with
  | mBase => fun S => selem_of S
  | mTele F => fun S => forall x, MTele_sort (S x)
  end.

(** Register MTele_ty as a coercion so that we can pretend any `MTele` is a
    type. *)
(* Coercion MTele_Ty : MTele >-> Sortclass. *)

(** MTele_val: compute `λ x .. z, T x .. z` from `T : MTele_ty n` *)
Definition MTele_val {s} : forall {n : MTele}, MTele_Sort s n -> s :=
  fix go n :=
    match n as n return MTele_Sort s n -> s with
    | mBase => fun f => f
    | mTele F => fun f => ForAll (fun x => go _ (f x))
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

(** MTele_In: gain access to potentially multiple telescoped types and values at
the same time to compute a new telescoped _type_. *)
Fixpoint MTele_In (s : Sort) {n : MTele} :
  (forall (now_ty : forall s, MTele_Sort s n -> s)
          (now_val : forall s {T : MTele_Sort s n}, MTele_val T -> now_ty s T), s)
  -> MTele_Sort s n :=
  match n as n return
        (forall (now_ty : forall s, MTele_Sort s n -> s)
                (now_val : forall s {T : MTele_Sort s n}, MTele_val T -> now_ty s T), s)
        -> MTele_Sort s n
  with
  | mBase => fun thunk => thunk (fun s T => T) (fun _ _ v => v)
  | mTele F =>
    fun thunk t =>
      MTele_In s (fun now_ty now_val =>
                    thunk
                      (fun _ T => now_ty _ (T t))
                      (fun _ _ v => now_val _ _ (App v t))
                 )
  end.

Notation "'[WithT' now_ty , now_val '=>' T ]" :=
  (MTele_In SType (fun now_ty now_val => T))
    (at level 0, format "[WithT  now_ty ,  now_val  =>  T ]").

(** MTele_in: gain access to potentially multiple telescoped types and values at the same time to compute a new telescoped _value_ of type `MTele_In ..`. *)
Fixpoint MTele_in (s : Sort) {n : MTele} :
  forall {thunk},
  (forall (now_ty : forall s, MTele_Sort s n -> s)
          (now_val : forall s {T : MTele_Sort s n}, MTele_val T -> now_ty s T),
      now_ty s (MTele_In s thunk))
  -> MTele_val (MTele_In (n:=n) s thunk) :=
  match n as n return
        forall thunk,
        (forall (now_ty : forall s, MTele_Sort s n -> s)
                (now_val : forall s {T : MTele_Sort s n}, MTele_val T -> now_ty s T),
            now_ty s (MTele_In s thunk)
        )
        -> MTele_val (MTele_In (n:=n) s thunk)
  with
  | mBase => fun _ thunk => thunk (fun s T => T) (fun _ _ v => v)
  | mTele F =>
    fun _ thunk =>
      Fun (fun t =>
             MTele_in s (fun now_ty now_val =>
                           thunk
                             (fun _ T => now_ty _ (T t))
                             (fun _ _ v => now_val _ _ (App v t))
                        )
          )
  end.

Notation "'[withT' now_ty , now_val '=>' t ]" :=
  (MTele_in (SType) (fun now_ty now_val => t))
    (at level 0, format "[withT  now_ty ,  now_val  =>  t ]").

(** MTele_Map: compute type `∀ x .. z, B x .. z` from type
    `∀ x .. z, A x .. z` *)
Fixpoint MTele_Map (s so : Sort) {n : MTele} :
  MTele_sort (MTele_In (SType) (n := n) (fun _ _ => stype_of s -> stype_of so)) -> MTele_Sort s n -> MTele_Sort so n
  :=
  match n return
        MTele_sort (MTele_In (SType) (n := n) (fun _ _ => stype_of s -> stype_of so)) -> MTele_Sort s n -> MTele_Sort so n
  with
  | mBase => fun f A => f A
  | mTele F => fun f A t => @MTele_Map s so (F t) (f t) (A t)
  end.

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
    MTele_val (MTele_In s (fun ty _ => Impl (ty _ A) (ty _ B))) -> MTele_val A -> MTele_val B :=
  match n with
  | mBase => fun A B f a => App f a
  | mTele F => fun A B f a => Fun (fun t => MTele_map (App f t) (App a t))
  end.

(** MTele_id: a sanity check to see if we can witness `(∀ x .. z, A x .. z) ->
(∀ x .. z, A x .. z)` by constructing `∀ x .. z, A x .. z -> A x .. z` *)
Local Fixpoint MTele_id {s} (n : MTele) :
  forall {A : MTele_Sort s n},
    MTele_val (MTele_In s (fun ty _ => Impl (ty _ A) (ty _ A))) :=
  match n  with
  | mBase => fun A => Fun (fun x : selem_of A => x)
  | mTele F => fun A => Fun (fun x => MTele_id (F x))
  end.

Local Example map_id {s} {n : MTele} {A : MTele_Sort s n} := @MTele_map s n A A (MTele_id n).


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