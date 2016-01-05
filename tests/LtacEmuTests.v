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
(*  intro x. *)
  reflexivity.
Qed.

Lemma test5 : forall n m : nat, n = m -> m = n.
MProof.
  mintros n m H.
  idtac. (* TODO: Remove this. Necessary to see the reduced term *)
  symmetry.
  assumption.
Qed.

Lemma test6 : forall (x y z : Prop), x = y -> y = z -> x = z.
MProof.
  mintros x y z H G.
  idtac. (* TODO: Remove this. Necessary to see the reduced term *)
  transitivity y.
  exact H.
  exact G.
Qed.

Goal forall (p : Prop), p \/ ~p -> True.
MProof.
  mintros p H.
  idtac.
  destruct H.
  mintros H0.
  idtac.
  exact I.
  mintro H0.
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
  mintro H.
  absurd (Fail = Fail).
  assumption.
  reflexivity.
Qed.

Definition test := ([[ (b : nat) |- S b > 0  ]] => evar _)%goal_match.

Goal forall a b : nat, S b > 0.
MProof.
  mintros a b.
  idtac.
  match_goal test.
Abort.

Goal forall P Q : Prop, P -> P.
MProof.
  mintros P Q x.
  assumption.
Qed.

Goal forall P Q : Prop, Q -> P -> P.
MProof.
  mintros P Q xQ xP.
  assumption.
Qed.

Goal forall P Q : Prop, Q -> P -> Q -> P /\ Q.
MProof.
  mintros P Q xQ xP xP'.
  split.
  - assumption.
  - assumption.
Qed.

Goal forall x : bool, orb x true = true.
MProof.
  mintro x.
  idtac.
  match_goal ([[ z:bool |- _ ]] => destruct (P:=fun z=>_ z _ = _) z).
  idtac. reflexivity.
  idtac.
  reflexivity.
Qed.

Example for_yann : forall (a b : nat) (Hb : b = 0) (Ha : a = 0), b = 0.
MProof.
  mintros a b Hb Ha.
  idtac.
  match_goal ([[ (x:nat) (Hx : x = 0) |- _ ]] => exact Hx).
Qed.

Example for_yann2 : forall (a b : nat) (Ha : a = 0) (Hb : b = 0), a = a.
MProof.
  mintros a b Ha Hb.
  idtac.
  match_goal ([[ (x:nat) (Hx : x = 0) |- x = x ]] => print_term x;; reflexivity).
Qed.

Example for_yann3 : forall (a b : nat) (Ha : a = 0) (Hb : b = 0), b = b.
MProof.
  mintros a b Ha Hb.
  idtac.
  match_goal ([[ (x:nat) (Hx : x = 0) |- x = x ]] => print_term x;; reflexivity).
Qed.

Example apply_tactic (a b : nat) : a > b -> S a > S b.
MProof.
  mintro H.
  idtac.
  apply Gt.gt_n_S.
  assumption.
Qed.

Example apply_tactic_fail (a b : nat) : a > b -> S a > b.
Proof.
MProof.
  mintro H.
  idtac.
  Fail apply Gt.gt_n_S.
Abort.

Goal True.
MProof.
  auto.
Qed.