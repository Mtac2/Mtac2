From Mtac2 Require Import Base MTele Logic.
Import M.notations.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

From Coq Require Import JMeq.

Notation "x =j= y" := (JMeq x y)
                 (at level 70, y at next level, no associativity).
Lemma JMeq_types : forall {A B} (x: A) (y: B) (H: x =j= y), A =m= B.
Proof.
  intros.
  destruct H. reflexivity.
Qed.

Lemma JMeq_meq : forall {A} (x: A) (y: A) (H: x =j= y), x =m= y.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

(** Given a term [t] of type [T], assumed to be of the form [let x : A := y in
    t'], with [T] being [let x : A := y in P] (or its let-expanded version), it
    gets a function [f] and executes [f A x y P meq_refl t' JMeq_refl] under the
    context extended with [x : A := y].  Assuming it returns value [b], it
    returns it after checking no harm is done: [x] is not free in [b]. Note that
    one might tink that it's wrong to return [y] or [P]. However, these terms
    where well-typed in the original context, so there is no problem. [x] is the
    only one being added to the context, and the one to care about. *)
Definition nu_let {T} (n: name) (t: T)
  {B : Type}
  (f : forall A (x y: A) P (eqxy: x =m= y) (t': P) (eqP: t =j= t'), M B) :
  M B.
  intros. exact M.mkt.
Qed.

(** Given a variable [x] of type [A], a definition (supposed to be equal) [y],
    and a term [t] of type [P], it returns a [t'] equals to [t]: [let z : A := y
    in t{z/x}]. It won't check if [y] is the actual definition, as long it is
    equal to [x] (that's what [eqxy] says), and assuming [x] is a variable, it
    should be sound to return the let-binding. The reason why the returned term
    has the same type as [P] is because [let z:A := y in t{z/x}] has type
    [P{y/x}] and, since [x =m= y], we get [P{x/x}] which is [P]. *)
Definition abs_let : forall {A : Type} {P : Type} (x y : A) (eqxy: x=m=y) (t: P),
    M {t' : P & t =m= t'}.
  intros. exact M.mkt.
Qed.

Obligation Tactic := intros.
Program
Definition completeness {B} (term: B) : M {blet : B & blet =m= term} :=
  nu_let (TheName "m") term (fun A m d P eqmd body eqP=>
    body_let <- abs_let (P:=P) m d eqmd body;
    let (blet, jeq) := body_let in
    M.ret (existT _ _ _ : { blet : _ & blet =m= term})).
Next Obligation.
  simpl in *.
  apply JMeq_types in eqP.
  rewrite eqP.
  exact blet.
Defined.
Next Obligation.
  simpl.
  cbv.
  simpl in jeq.
  destruct eqmd.
  destruct (JMeq_types term body eqP).
  rewrite eqP.
  rewrite jeq.
  reflexivity.
Defined.

Definition soundness {A} {P} (x d: A) (term: P) (eqxd : x =m= d) : M {t : P & t =m= term}.
  refine (letb <- abs_let x d eqxd term; let (blet, eq) := letb in _).
  refine (nu_let (TheName "m") blet (fun B a b T eqab t' eqblet => _)).
  refine (M.ret (existT _ _ _)).
  simpl in eq.
  generalize (JMeq_types _ _ eqblet).
  intro eqPT.
  generalize t' eqblet.
  clear t' eqblet.
  rewrite <- eqPT.
  intros t' eqblet.
  rewrite eq. rewrite eqblet.
  reflexivity.
Qed.
