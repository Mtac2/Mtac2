(** This file contains several examples showing the different tactics and tactic
    operators in Mtac2. Many of the examples are inspired from SF. *)

(** Here is a list of basic tactics included in Mtac2, that we present here:
 - intros, cintros, typed_intros (with and without definitions).
 - destruct (and its variants).
 - left, right.
 - reflexivity.
 - apply.
 - fix.
 - generalize.
 - assert.
 - pose.
 - exists
*)

(** We start by importing Mtac2. The module [Mtac2] imports most of Mtac2's
stuff. *)
Require Import Mtac2.Mtac2.
(** Since we are going to work with the [Tactics] module, we import the inner [T] module. *)
Import T.

(** We're going to prove stuff about lists. *)
Require Import Lists.List.
Import Lists.List.ListNotations.

(** A simple example to warm up. *)
Theorem surjective_pairing_1 : forall A B (p : A * B),
  p = (fst p, snd p).
MProof.
  (** [typed_intros] introduces everything of a certain type *)
  typed_intros Type.
  (** [destructn] is [destruct] for a certain (0-based) number of binders. *)
  destructn 0.
  intros.
  (** (We must FIX how the goal is presented, now it contains extra stuff about sorts) *)
  simpl.
  reflexivity.
Qed.

(** We can use the [&>] composition operator (left associative) of [Mtac2] to inline the proof. *)
Theorem surjective_pairing : forall A B (p : A * B),
  p = (fst p, snd p).
MProof.
  typed_intros Type &> destructn 0 &> reflexivity. (* [reflexivity] does [intros] *)
Qed.

(** Mtac2 has intro patterns, with a tactic call [pintros] and a combinator
(similar to SSReflect's [=>]) called [asp]. *)
Theorem tl_length_pred : forall l: list nat,
  pred (length l) = length (tl l).
MProof.
  destructn 0 asp [ [] ; ["n" ; "l'"] ].
  - (* l = nil *)
    simpl.
    reflexivity.
  - (* l = cons n l' *)
    simpl.
    reflexivity.
Qed.

(** Another example using [assert] and the [rewrite] tactic imported from Coq's
own. *)
Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
MProof.
  intros n m p q.
  assert (H : n + m = m + n).
  - rewrite -> PeanoNat.Nat.add_comm &> reflexivity.
  - rewrite -> H &> reflexivity.
Qed.

(** An example featuring scoped introduction of variables [cintros] and
[mexists]. *)
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
MProof.
  cintros n {- destructn 0 &> intros m Hm -}.
  simpl.
  mexists (2 + m).
  (** We need to FIX the beta-expanded goal *)
  apply Hm.
Qed.

(** An example featuring the handy [select] tactic to pick an element from the
list of hypotheses based on its type. *)
Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  intros. select (_ -> _) >>= apply. assumption.
Qed.

(** Note that we can't use [&>] to compose [intros] with [select] (try it!).
The reason is that the holes in the type (the underscores) are turn into
meta-variables, which can't refer to the introduced variables. *)

(** We can, however, inline the proof with cintros. In order to avoid parens we
need the right-associative composition operator [;;]. *)
Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  cintros _ _ _ _ {- select (_ -> _) >>= apply;; assumption -}.
Qed.

(** If we want to be able to compose [intros] with [select], we must create the
meta-variables for each hole (using the [M.evar] construct). *)
Definition apply_fun : tactic :=
  `A B <- M.evar _;
  select (A -> B) >>= apply.

Goal forall P Q, (P -> Q) -> P -> Q.
MProof.
  intros &> apply_fun &> assumption.
Qed.

(** Of course, we can inline it too as [(`A B <- M.evar _; select (A->B) >>= apply)] *)

(** One simple example using the [cut] tactic. *)
Example cut_ex P Q R: (P \/ Q -> R) -> P -> R.
MProof.
  intros.
  cut (P \/ Q).
  - assumption.
  - left &> assumption.
Qed.

(** We can inline the previous proof thanks to the overloading of the [&>] operator. *)
Example cut_ex_inline P Q R: (P \/ Q -> R) -> P -> R.
MProof.
  intros.
  cut (P \/ Q) &> [m: idtac | left] &> assumption.
  (** Note the notation for a list of tactics. Instead of Coq's lists, we use
  Mtac2's (with type [mlist]), which are universe polymorphic.  We use Ltac's
  notation, using the pipe instead of the semi-colon for each element of the
  list. *)
Qed.

(** Using the [fix_tac] tactic (similar to Coq's fix) *)
Theorem plus_n_O : forall n:nat, n = n + 0.
MProof.
  fix_tac (TheName "IH") 1.
  destructn 0.
  - reflexivity.
  - intro n'. simpl. rewrite <- IH.
    reflexivity.
Qed.

(** An example combining standard FP programming with tactic programming: *)
(** [apply_one_of] take a list of lemmas and tries to apply each until one
succeed. Again, we use Mtac2's own definition for lists. *)
Mtac Do New Exception NoneApply.
Definition apply_one_of (l: mlist dyn) : tactic :=
  mfold_left (fun a b=>a || (dcase b as e in apply e)) l (raise NoneApply).

(** The type [dyn] packs an element with its type. An element of this type is
constructed with the [Dyn] constructor, providing an element (implicitly taking
its type). [dcase] is notation for taking the element from the [Dyn]. *)
Goal forall x y z : nat, In x (z :: y :: x :: nil).
MProof.
  intros &> T.repeat (apply_one_of [m:Dyn in_eq | Dyn in_cons]).
Qed.

(** To conclude, we present a way of hacking the type inference algorithm to
execute an Mtactic. We use the [ltac:] escape to be able to write Ltac code
inside a term, and then we use Mtac2's (Ocaml) tactic [mrun] to execute, in this
case, the [apply] tactic. *)
Notation "x ?" := (ltac:(mrun (apply x))) (at level 0).

(** With this notation, we can now let Coq infer the number of arguments that a
term should have. *)
Definition test_question_mark (x y z: nat) : In x [x] := in_eq?.
