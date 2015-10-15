Require Import MetaCoq.MetaCoq.
Require Import MetaCoq.LtacEmu.
Import MetaCoqNotations.
Import LtacEmuNotations.

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
  exact I.
  intro H0.
  idtac.
  exact I.
Qed.

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
  assump.
  reflexivity.
Qed.

Definition test := ([[ (b : nat) |- S b > 0  ]] => evar _)%goal_match.

Goal forall a b : nat, S b > 0.
MProof.
  intros a b.
  idtac.
  match_goal test.
Abort.

Goal forall P Q : Prop, P -> P.
MProof.
  intros P Q x.
  assump.
Qed.

Goal forall P Q : Prop, Q -> P -> P.
MProof.
  intros P Q xQ xP.
  assump.
Qed.

Goal forall P Q : Prop, Q -> P -> Q -> P /\ Q.
MProof.
  intros P Q xQ xP xP'.
  split.
  - assump.
  - assump.
Qed.

Goal forall x : bool, orb x true = true.
MProof.
  intro x.
  idtac.
  match_goal ([[ z:bool |- _ ]] => destruct (P:=fun z=>_ z _ = _) z).
  idtac. reflexivity.
  idtac.
  reflexivity.
Qed.
