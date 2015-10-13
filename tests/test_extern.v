Require Import MetaCoq.MetaCoq.
Import MetaCoqNotations.

Require Import Strings.String.
Open Scope string.

Require Import Omega.

Class Extern (s : string) A := extern_class { result : A }.

Definition omega := "omega".
Hint Extern 0 (Extern omega ?A) => (
  assert (H : A) by omega;
  exact (@extern_class omega A H))  : typeclass_instances.

Definition CouldntSolveGoal : Exception. exact exception. Qed.

Definition extern s {A} : M A :=
  e <- evar (Extern s A);
  solve_typeclasses;;
  b <- is_evar e;
  if b then
    raise CouldntSolveGoal
  else
    ret (@result s A e).

Definition intro {A : Type} {q} (s : forall x : A, M (q x))
: M (forall x : A, q x) :=
  nu x,
  p <- s x;
  abs x p.

Goal forall n : nat, n = 0 \/ n = 1 \/ n > 1.
MProof.
  intro (fun n=> extern omega).
Qed.


Hint Extern 0 (Extern "auto" ?A) => (
  assert (H : A) by auto;
  exact (@extern_class "auto" A H))  : typeclass_instances.

Goal forall P Q : Prop, P -> Q -> P /\ Q.
MProof.
  extern "auto".
Qed.

Definition try_auto {P} : M P :=
  mtry (extern "auto")
  with CouldntSolveGoal => evar P end.

Goal forall P Q : Prop, Q -> P /\ Q.
MProof.
  Fail extern "auto".
  try_auto.
Abort.

Goal forall P Q : Prop, P -> Q -> P /\ Q.
MProof.
  let x := $( auto )$ in ret x.
Abort.
