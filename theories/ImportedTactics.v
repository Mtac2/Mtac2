From Mtac2 Require Import Base Tactics.
Import M.notations.
Import T.notations.

Require Import Strings.String.
Require Import Mtac2.List.
Import Mtac2.List.ListNotations.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

Definition qualify s := String.append "Mtac2.ImportedTactics." s.

Ltac trivial := trivial.
Definition trivial : tactic := T.ltac (qualify "trivial") [m:].

Ltac discriminate := discriminate.
Definition discriminate : tactic := T.ltac (qualify "discriminate") [m:].

Ltac intuition := intuition.
Definition intuition : tactic := T.ltac (qualify "intuition") [m:].

Ltac auto := auto.
Definition auto : tactic := T.ltac (qualify "auto") [m:].

Ltac eauto := eauto.
Definition eauto : tactic := T.ltac (qualify "eauto") [m:].

Ltac subst := subst.
Definition subst : tactic := T.ltac (qualify "subst") [m:].

Ltac contradiction := contradiction.
Definition contradiction : tactic := T.ltac (qualify "contradiction") [m:].

Ltac tauto' := tauto.
Definition tauto : tactic := T.ltac (qualify "tauto'") [m:].

Ltac unfold x := unfold x.
Definition unfold {A} (x: A) := T.ltac (qualify "unfold") [m:Dyn x].

Ltac rrewrite1 a := rewrite a.
Ltac rrewrite2 a b := rewrite a, b.
Ltac rrewrite3 a b c := rewrite a, b, c.
Ltac rrewrite4 a b c d := rewrite a, b, c, d.
Ltac rrewrite5 a b c d e := rewrite a, b, c, d, e.

Definition compute_terminator {A} (l: mlist A) : M string :=
  match l with
  | [m:] => M.failwith "At least one required"
  | [m: _] => M.ret "1"
  | _ :m: [m:_] => M.ret "2"
  | _ :m: _ :m: [m:_] => M.ret "3"
  | _ :m: _ :m: _ :m: [m:_] => M.ret "4"
  | _ :m: _ :m: _ :m: _ :m: [m:_] => M.ret "5"
  | _ => M.failwith "Unsupported"
  end%string.

Ltac lrewrite1 a := rewrite <- a.
Ltac lrewrite2 a b := rewrite <- a, b.
Ltac lrewrite3 a b c := rewrite <- a, b, c.
Ltac lrewrite4 a b c d := rewrite <- a, b, c, d.
Ltac lrewrite5 a b c d e := rewrite <- a, b, c, d, e.

Inductive RewriteDirection := LeftRewrite | RightRewrite.

Definition trewrite (d : RewriteDirection) (args : mlist dyn) : tactic := fun g =>
  (ter <- compute_terminator args;
  let prefix := match d with LeftRewrite => "l"%string | RightRewrite => "r"%string end in
  let name := reduce RedNF (qualify (prefix++"rewrite"++ter)) in
  T.ltac name args g)%MC.

Notation "'rewrite' '->' x , .. , z" :=
  (trewrite RightRewrite (mcons (Dyn x) .. (mcons (Dyn z) [m:]) ..))
    (at level 0, x at next level, z at next level).
Notation "'rewrite' '<-' x , .. , z" :=
  (trewrite LeftRewrite (mcons (Dyn x) .. (mcons (Dyn z) [m:]) ..))
    (at level 0, x at next level, z at next level).
Notation "'rewrite' x , .. , z" :=
  (trewrite RightRewrite (mcons (Dyn x) .. (mcons (Dyn z) [m:]) ..))
    (at level 0, x at next level, z at next level).

Ltac elim h := elim h.
Definition elim {A} (x:A) : tactic :=
  T.ltac (qualify "elim") [m: Dyn x].

Ltac induction v := induction v.
Definition induction {A} (x:A) : tactic :=
  T.ltac (qualify "induction") [m: Dyn x].

Definition injection {A} (x: A) : tactic :=
  T.ltac ("Coq.Init.Notations.injection") [m:Dyn x].

Ltac inversion H := inversion H.
Definition inversion {A} (x: A) : tactic :=
  T.ltac (qualify "inversion") [m:Dyn x].

Ltac typeclasses_eauto := typeclasses eauto.
Definition typeclasses_eauto : tactic :=
  T.ltac (qualify "typeclasses_eauto") [m:].

Ltac ltac_apply x := apply x.
Definition ltac_apply {A} (x:A) := T.ltac (qualify "ltac_apply") [m:Dyn x].

Ltac ltac_destruct x := destruct x.
Definition ltac_destruct {A} (x:A) := T.ltac (qualify "ltac_destruct") [m:Dyn x].
