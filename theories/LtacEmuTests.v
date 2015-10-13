Require Import LtacEmu.
Require Import MetaCoq.MetaCoq.
Import MetaCoqNotations.

Lemma test1 : forall P, P -> P.
MProof.
  exact (fun P x => x).
Qed.

Lemma test2 : True.
MProof.
   apply (fun (x : True) => x).
   exact I.
Qed.

Lemma test3 : O = O.
MProof.
  reflexivity.
Qed.

(*
Require Import Omega.

Goal forall n : nat, n = 0 \/ n = 1 \/ n > 1.
Proof.
  intro n.
  omega.
Qed.

Lemma bar : forall x y : nat, x = y -> y = x.
Proof.
  intros x y H.
  idtac.
  apply sym_eq.
  exact H.
Qed.
*)

Lemma test4 : forall (p : Prop), p = p.
MProof.
  intro x.
  reflexivity.
Qed.

Lemma test5 : forall n m : nat, n = m -> m = n.
MProof.
  intros n m H.
  idtac. (* TODO: Remove this. Necessary to see the reduced term *)
  symmetry.
  assumption.
Qed.

Lemma test6 : forall (x y z : Prop), x = y -> y = z -> x = z.
MProof.
  intros x y z H G.
  idtac. (* TODO: Remove this. Necessary to see the reduced term *)
  transitivity y.
  exact H.
  exact G.
Qed.

Goal forall (p : Prop), p \/ ~p -> True.
MProof.
  intros p H.
  idtac.
  destruct H.
  intros H0.
  idtac.
  idtac.
  intro H0.
  idtac.
  idtac.
  exact I.
  exact I.
  absurd p.
Abort.

Inductive Option : Set :=
| Fail : Option
| Ok : bool -> Option.

Definition get : forall x:Option, x <> Fail -> bool.
MProof.
  refine (fun x : Option =>
            match x return x <> Fail -> bool with
              | Fail => _
              | Ok b => fun _ => b
            end).
  intro H.
  absurd (Fail = Fail).
  trivial.
Qed.
