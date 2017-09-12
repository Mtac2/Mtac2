Require Import Bool.Bool.
Require Import MetaCoq.MetaCoq.
Import T.
Import MetaCoq.List.ListNotations.

Goal True.
MProof.
  exact I.
Qed.

Goal False.
MProof.
  Fail exact I.
Abort.

Example not_fail_not_var : 0 = 0.
MProof.
  destruct 0.
  - reflexivity.
Abort.

Example ex_destr (n:nat) : n = n.
MProof.
  destruct n.
  - reflexivity.
  - intro n'.
    reflexivity.
Qed.

Goal forall b : bool, b = b.
MProof.
  intro b.
  - destruct b &> [m:reflexivity| reflexivity]%list.
Qed.

Goal forall b1 : bool, b1 = b1.
MProof.
  intro b1 &> [m:reflexivity]%list.
Qed.

Goal forall b1 b2 b3 : bool, b1 && b2 && b3 = b3 && b2 && b1.
MProof.
  intro b1 ;; (intro b2;; intro b3).
  destruct b1;; (destruct b2;; (destruct b3;; reflexivity)).
Qed.

Goal forall b1 b2 b3 : bool, b1 && b2 && b3 = b3 && b2 && b1.
MProof.
  intro b1;; intro b2;; intro b3.
  destruct b1;; destruct b2;; destruct b3;; reflexivity.
Qed.

Goal forall b1 b2 b3 : bool, b1 && b2 && b3 = b3 && b2 && b1.
MProof.
  intros b1;; intros b2 b3.
  destruct b1;; destruct b2;; destruct b3;; reflexivity.
Qed.

Goal forall b1 b2 : bool, b1 && b2 = b2 && b1.
MProof.
  cintros b1 b2 {-
    destruct b1;; destruct b2;; reflexivity
  -}.
Qed.

Goal forall b1 b2 b3 : bool, b1 && b2 && b3 = b3 && b2 && b1.
MProof.
  cintros b1 b2 {-
    destruct b1;; destruct b2;;
    cintro b3 {- destruct b3;; reflexivity -}
  -}.
Qed.

Goal (forall x, x > 0) -> 3 > 0.
MProof.
  intro H.
  apply H.
Qed.

Goal (forall x, x > 0) -> 3 > 0.
MProof.
  cintro H {- apply H -}.
Qed.

Goal {x:nat & x > 0}.
MProof.
  apply (existT _ 1 _).
  Unshelve.
  hnf.
  apply le_n.
Qed.

Require Import Coq.omega.Omega.
Definition omega := ltac "Coq.omega.Omega.omega" MetaCoq.Datatypes.nil.

Goal (forall x y, x > y \/ y < x -> x <> y) -> 3 <> 0.
MProof.
  cintro H {- apply H;; left;; omega -}.
Qed.

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

Lemma test4 : forall (p : Prop), p = p.
MProof.
  intro x.
  reflexivity.
Qed.

Goal forall (x y z : Prop), x = y -> y = z -> x = z.
Proof.
  intros x y z H G.
  transitivity y.
  exact H.
  exact G.
Qed.

Lemma assumption_test (n m : nat) (H : n = m) : m = n.
MProof.
  symmetry.
  assumption.
Qed.

Goal forall (x y z : Prop), x = y -> y = z -> x = z.
MProof.
  intros x y z H G.
  transitivity y.
  - exact H.
  - exact G.
Qed.

Definition transitivity := "Coq.Init.Notations.transitivity".

Lemma test6 : forall (x y z : Prop), x = y -> y = z -> x = z.
MProof.
  intros x y z H G.
  ltac transitivity [m:Dyn y].
  ltac "Coq.Init.Notations.revgoals" MetaCoq.List.nil.
  exact H.
  exact G.
Qed.

Goal forall (p : Prop), p \/ ~p -> ~p \/ p.
Proof.
  intros p H.
  destruct H.
  - right. assumption.
  - left. assumption.
Qed.

(* *)
Lemma destruct1 : forall (p : Prop), p \/ ~p -> ~p \/ p.
MProof.
  intros p H.
  destruct H;; intro H0.
  - right;; assumption.
  - left;; assumption.
Qed.

Goal forall b, andb b b = b.
MProof.
  intro b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Definition testmg :=
  match_goal with [[ (b : nat) |- S b > 0  ]] => fun g=>destruct b g end.

Goal forall b : nat, S b > 0.
MProof.
  intros b.
  testmg.
  - omega.
  - intros n';; omega.
Qed.

Goal forall a b : nat, S b > 0.
MProof.
  intros a b.
  testmg.
  - omega.
  - intros n';; omega.
Qed.

Goal forall a b c : nat, S b > 0.
MProof.
  intros a b c.
  testmg.
  - omega.
  - intros n';; omega.
Qed.

Goal forall P Q : Prop, P -> P.
MProof.
  intros P Q x.
  assumption.
Qed.

Goal forall P Q : Prop, Q -> P -> P.
MProof.
  intros P Q xQ xP.
  assumption.
Qed.

Goal forall P Q : Prop, Q -> P -> Q -> P /\ Q.
MProof.
  intros P Q xQ xP xP'.
  split.
  - assumption.
  - assumption.
Qed.

Goal forall x : bool, orb x true = true.
MProof.
  intro x.
  match_goal with [[ z:bool |- _ ]] => destruct z end.
  - reflexivity.
  - reflexivity.
Qed.

Goal forall (a b : nat) (Hb : b = 0) (Ha : a = 0), b = 0.
MProof.
  intros a b Hb Ha.
  match_goal with [[ (x:nat) (Hx : x = 0) |- x = 0 ]] => exact Hx end.
Qed.

Goal forall (a b : nat) (Hb : b = 0) (Ha : a = 0), a = 0.
MProof.
  intros a b Hb Ha.
  match_goal with [[ (x:nat) (Hx : x = 0) |- x = 0 ]] => exact Hx end.
Qed.

Goal forall (a b : nat) (Ha : a = 0) (Hb : b = 0), a = a.
MProof.
  intros a b Ha Hb.
  match_goal with [[ (x:nat) (Hx : x = 0) |- x = x ]] => reflexivity end.
Qed.

Goal forall (a b : nat) (Ha : a = 0) (Hb : b = 0), b = b.
MProof.
  intros a b Ha Hb.
  match_goal with [[ (x:nat) (Hx : x = 0) |- x = x ]] => reflexivity end.
Qed.

Example apply_tactic (a b : nat) : a > b -> S a > S b.
MProof.
  intro H.
  apply Gt.gt_n_S.
  assumption.
Qed.

Example apply_tactic_fail (a b : nat) : a > b -> S a > b.
MProof.
  intro H.
  Fail apply Gt.gt_n_S.
Abort.

Goal forall b1 b2 b3 : bool, andb b1 (andb b2 b3) = andb b1 (andb b2 b3).
MProof.
  introsn 1.
  introsn 2.
  Fail introsn 1.
  introsn 0.
  reflexivity.
Qed.

Goal forall b1 b2 b3 : bool, andb b1 (andb b2 b3) = andb b1 (andb b2 b3).
MProof.
  destructn 0.
  - destructn 1.
    + Fail destructn 0.
      select bool destruct;; reflexivity.
    + select bool destruct;; reflexivity.
  - introsn 2;; reflexivity.
Qed.

(* clear *)
Goal forall (x : nat) (z : bool) (y : nat), x > y.
MProof.
  intros x z y.
  clear z.
  Fail clear y.
Abort.

(* generalize *)
Goal forall (x : nat) (z : bool) (y : nat), x > y.
MProof.
  intros x z y.
  generalize x;; generalize y;; generalize z.
  Show Proof.
Abort.

(* move_back *)
Goal forall (x : nat) (z : bool) (y : nat), x > y.
MProof.
  intros x z y.
  move_back x (move_back y (clear z)).
Abort.

Goal forall x : Prop, x = x.
MProof.
  ltac "Coq.Init.Notations.auto" MetaCoq.List.nil.
Qed.

(** intros_all test *)
Goal forall (x y z : nat) (H: x = y), y = x.
MProof.
  intros.
  select (_ = _) (fun x=>rewrite x).
  reflexivity.
Qed.

(** destruct_all *)
Goal forall x y : bool, x && y = y && x.
MProof.
  intros.
  destruct_all bool;; reflexivity.
Qed.

Goal forall x : bool, true = x.
MProof.
  try (intros;; reflexivity).
Abort.

Goal forall x y : bool, x = y -> y = x.
MProof.
  intros x y H.
  destruct x or idtac. (* should execute idtac because H depends on x *)
  move_back H (
    destruct x;; destruct y;; intros;;
      (reflexivity or (symmetry;; assumption))
  ).
Qed.

Goal True.
MProof.
  cpose I (fun x=>idtac).
  exact I.
Qed.

Require Import MetaCoq.ImportedTactics.

Goal forall x:nat, x = x.
MProof.
  trivial.
Qed.


Goal forall x:nat, forall y:nat, False -> x = 0.
MProof.
  (** trivial is just testing that if it does not solve the goal, the goal is still there *)
  trivial;; intros;; contradiction.
Qed.

Require Import MetaCoq.ImportedTactics.

Example ex_destr_not_var (b c: bool) : (if b && c then c else c) = c.
MProof.
  pose (H := b && c).
  assert (Heq : H = b && c).
  - reflexivity.
  - (rewrite <- Heq);; destruct H;; reflexivity.
Qed.

Example fix_tac_ex: forall x:nat, 0 <= x.
MProof.
  fix_tac "f" 1;; apply le_0_n.
Qed.

Example intros_def: let x := 0 in forall y, x <= y.
MProof.
  intros.
  apply le_0_n.
Qed.

Example intros_def': let x := 0 in forall y, x <= y.
MProof.
  intros x y.
  Ltac ind x :=induction x.
  ltac "mctacticstests.ind" [m:Dyn y];; apply le_0_n.
Qed.

Example test_unfold : id 0 = 0.
MProof.
  unfold (@id).
  reflexivity.
Qed.
