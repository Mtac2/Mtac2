From Mtac2 Require Import Base MTele Logic.
Import M.notations.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

From Coq Require Import JMeq.

Notation "x =j= y" := (JMeq x y)
                 (at level 70, y at next level, no associativity).
Lemma JMeq_types : forall {A B} {x: A} {y: B} (H: x =j= y), A =m= B.
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
Definition full_nu_let {T} (n: name) (t: T)
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
Definition full_abs_let : forall {A : Type} {P : Type} (x y : A) (eqxy: x=m=y) (t: P),
    M {t' : P & t =m= t'}.
  intros. exact M.mkt.
Qed.

Definition old_nu_let {A B C : Type} (n: name) (blet: C) (f: A -> C -> M B) : M B :=
  full_nu_let n blet (fun A' x y P eqxy t' eqt'  =>
    eqAA' <- M.unify_or_fail UniCoq A' A;
    let x := reduce (RedWhd [rl:RedMatch]) (match eqAA' with meq_refl => x end) in
    let eqCP := dreduce (@JMeq_types, @meq_sym) (meq_sym (JMeq_types eqt')) in
    let t' := reduce (RedWhd [rl:RedMatch]) (match eqCP with meq_refl => t' end) in
    f x t').


Obligation Tactic := simpl; intros.
Program
Definition let_completeness {B} (term: B) : M {blet : B & blet =m= term} :=
  full_nu_let (TheName "m") term (fun A m d P eqmd body eqP=>
    body_let <- full_abs_let (P:=P) m d eqmd body;
    let (blet, jeq) := body_let in
    M.ret (existT _ _ _ : { blet : _ & blet =m= term})).
Next Obligation.
  apply JMeq_types in eqP.
  rewrite eqP.
  exact blet.
Defined.
Next Obligation.
  cbv.
  simpl in jeq.
  destruct eqmd.
  destruct (JMeq_types eqP).
  rewrite eqP.
  rewrite jeq.
  reflexivity.
Defined.

Program
Definition let_soundness {A} {P} (x d: A) (term: P) (eqxd : x =m= d) : M {t : P & t =m= term} :=
  letb <- full_abs_let x d eqxd term;
  let (blet, eq) := letb in
  full_nu_let (TheName "m") blet (fun B a b T eqab t' eqblet =>
     _).
Next Obligation.
  refine (M.ret (existT _ _ _)).
  simpl in eq.
  generalize (JMeq_types eqblet).
  intro eqPT.
  generalize t' eqblet.
  clear t' eqblet.
  rewrite <- eqPT.
  intros t' eqblet.
  rewrite eq. rewrite eqblet.
  reflexivity.
Qed.

Print Module M.M.

(** Let [T] equals to [forall x:A, B x] and [t] equals to [fun x:A => b], it
    introduces [x:A] in the context, and executes [f A x B b meq_refl meq_refl],
    the first [meq_refl] being the equality of types [T =m= forall x:A, B x] and
    the second of the body, morally [t x =m= b]. The value returned by [f] must
    not contain [x]. *)
Definition dest_fun_type (T C: Type) (t: T): Type.
  refine ((forall A (x: A) (B: A->Type) (b: B x)
  (eqTB : T =m= (forall z:A, B z)) (eqt: (_ : (forall z, B z)) x =m= b), M C) -> M C).
  rewrite eqTB in t. exact t.
Defined.

Definition dest_fun {T C} t : dest_fun_type T C t.
  intros; constructor. Qed.

Definition abs_fun: forall{A: Type} {P: A->Type} (x: A) (t: P x),
  M {t': forall x, P x & t' x =m= t}.
  constructor. Qed.


Require Import ssreflect.


Lemma equal_f_dep : forall {A B} {f g : forall (x : A), B x},
  f =m= g -> forall x, f x =m= g x.
Proof. by move=>? ? ? ? ->. Qed.

Axiom functional_extensionality_dep : forall {A} {B : A -> Type},
  forall (f g : forall x : A, B x),
  (forall x, f x =m= g x) -> f =m= g.

Program
Definition fun_completeness {T: Type} (t: T) : M {A:Type & {P:A->Type & {funp : forall x:A, P x & funp =j= t}}} :=
  dest_fun t (fun A x B b eqTB eqt =>
    absf <- abs_fun x b;
    let (t', eqtb') := absf in
      M.ret (existT _ A (existT _ B (existT _ t' _)))).
Next Obligation.
  cbv in eqt.
  rewrite -eqt in eqtb'.
  move: eqtb'.
  (* We know that [t' x =m= t' x] but we can't conclude that [t' =m=
  t]. Informally, this holds because [x] can be substituted by any [y], and then
  conclude with functional_extensionality_dep. *)
Admitted.

Axiom forall_extensionality : forall (A : Type) (B C : A -> Type),
  (forall x : A, B x =m= C x) -> (forall x : A, B x) =m= (forall x : A, C x).

Axiom forall_extensionality_domain : forall (A B: Type) (C: A -> Type) (D: B -> Type),
  (forall x : A, C x) =m= (forall x : B, D x) -> A =m= B. (* this is not true I think *)

Axiom forall_extensionality_codomain : forall (A: Type) (C: A -> Type) (D: A -> Type),
  (forall x, C x) =m= (forall x, D x) -> C =m= D. (* does it make sense? *)

Program
Definition fun_soundness {A: Type} {P: A->Type} (x: A) (b: P x) : M {b':P x & b' =m= b} :=
  absf <- abs_fun x b;
  let (funp, feq) := absf in
  dest_fun funp (fun A' x' B' b' eqPP' eqbb' =>
     M.ret (existT _ _ _ : {b':P x & b' =m= b})).
Next Obligation.
  move/forall_extensionality_domain: (eqPP')=>eqAA'.
  move: B' x' b' eqPP' eqbb'.
  rewrite -eqAA'.
  intros.
  move/forall_extensionality_codomain: (eqPP')=>eqPB'.
  move: b' eqPP' eqbb'.
  rewrite -eqPB'.
  move=>b' eqPP'.
  cbv.
Admitted.

Require Import BinNat.
Inductive level := aLevel : N -> level | aVar : N -> level.
Inductive sort := sProp | sSet | sType : level -> sort.

Definition dest_sort : Type -> M sort.
  intros. exact M.mkt. Qed.

Definition make_sort : sort -> M Type.
  intros. exact M.mkt. Qed.

(* There's nothing we can prove about this *)


(** Let's see what we can do with decompose_forallT *)
Require Import Mtac2.lib.Datatypes.

(* So far it doesn't provide any equality, so we can't prove anything *)
Axiom admit : forall P, P.
Program
Definition forall_complete (T:Type) : M {T':Type & T' =m= T} :=
  M.decompose_forallT (B:=fun _=>{T':Type & T' =m= T}) T (fun A b =>
     M.nu Generate mNone (fun x=>
       r <- M.abs_prod_type x (b x);
       M.ret (existT _ r (admit _)) : M {T':Type & T' =m= T})) (M.failwith "error").

Require Import Mtac2.
(* but it works *)
Goal (forall x, x > 0 : Type) =m= (forall x, x > 0 : Type).
MProof.
  r <- forall_complete (forall x, x > 0);
  let (x, _) := r in
  T.exact (meq_refl x).
Qed.
