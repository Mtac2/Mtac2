From Mtac2 Require Import Datatypes List Mtac2 ConstrSelector.
Import T.
Import Mtac2.List.ListNotations.

Eval compute in M.eval (index 0).
Eval compute in M.eval (index S).
Eval compute in M.eval (index eq_refl).
Eval compute in M.eval (index nil).
Eval compute in M.eval (index (@cons _)).

Goal forall b, orb b (negb b) = true.
MProof.
  destructn 0 &> case true do reflexivity.
  reflexivity.
Qed.

Definition elim0 : tactic :=
  gT <- goal_type;
  A <- M.evar Type;
  intro_base (FreshFrom gT) (fun x:A=>elim x).

Definition rrewrite {A} (x: A) := trewrite RightRewrite [m:Dyn x]%list.
Definition lrewrite {A} (x: A) := trewrite LeftRewrite [m:Dyn x]%list.

Goal forall n, n + 0 = n.
MProof.
  elim0 &> case 0 do reflexivity.
  intros &> simpl. select (_ = _) >>= rrewrite ;; reflexivity.
Qed.

Goal forall n, n + 0 = n.
MProof.
  elim0 &> simpl &> case 0, S do intros &> try reflexivity.
  select (_ = _) >>= rrewrite ;; reflexivity.
Qed.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.

Inductive id : Type :=
  | Id : nat -> id.

Definition total_map (A:Type) := id -> A.

Definition beq_id id1 id2 :=
  match id1,id2 with
    | Id n1, Id n2 => beq_nat n1 n2
  end.

Definition t_update {A:Type} (m : total_map A)
                    (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.


Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp                (* <----- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => leb (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state),
    beval st b1 = beval st b2.


Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).



Inductive com : Type :=
  | CSkip : com
  | CBreak : com               (* <-- new *)
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).


Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ (t_update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;;; c2) / st \\ st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' ->
      (WHILE b DO c END) / st \\ st''

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

Require Import Strings.String.

Definition remember {A} (x:A) (def eq : string) : tactic :=
  cpose_base (TheName def) x (fun y:A=>
    cassert_base (TheName eq) (fun H: y = x =>lrewrite H) |1> reflexivity).

Lemma WHILE_true_nonterm : forall b c st st',
     bequiv b BTrue ->
     ~( (WHILE b DO c END) / st \\ st' ).
MProof.
  intros b c.
  remember (WHILE b DO c END) "cw" "Heqcw".
  intros st st' eqT H.
  induction H &> case E_Skip, E_Ass, E_IfTrue, E_IfFalse, E_Seq do discriminate.
  - (* E_WhileEnd *) (* contradictory -- b is always true! *)
    inversion Heqcw. subst.
    select (bequiv _ _) >>= unfold_in bequiv.
    move_back H. simpl.
    select (forall x:_, _) >>= rrewrite. simpl.
    discriminate.
  - (* E_WhileLoop *) (* immediate from the IH *)
    select (WHILE _ DO _ END = _ -> _) >>= apply.
    assumption.
Qed.
