From Mtac2 Require Import Base Tactics.
Require Import ssrmatching.ssrmatching.

Import M.notations.
Import T.notations.

Require Import Strings.String.
Require Import Mtac2.lib.List.
Import Mtac2.lib.List.ListNotations.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

Definition qualify s := String.append "Mtac2.tactics.ImportedTactics." s.

Ltac Mtrivial := trivial.
Definition trivial : tactic := T.ltac (qualify "Mtrivial") [m:].

Ltac Mdiscriminate := discriminate.
Definition discriminate : tactic := T.ltac (qualify "Mdiscriminate") [m:].

Ltac Mintuition := intuition.
Definition intuition : tactic := T.ltac (qualify "Mintuition") [m:].

Ltac Mauto := auto.
Definition auto : tactic := T.ltac (qualify "Mauto") [m:].

Ltac Meauto := eauto.
Definition eauto : tactic := T.ltac (qualify "Meauto") [m:].

Ltac Msubst := subst.
Definition subst : tactic := T.ltac (qualify "Msubst") [m:].

Ltac Mcontradiction := contradiction.
Definition contradiction : tactic := T.ltac (qualify "Mcontradiction") [m:].

Ltac Mtauto := tauto.
Definition tauto : tactic := T.ltac (qualify "Mtauto") [m:].

Ltac Munfold x := unfold x.
Definition unfold {A} (x: A) := T.ltac (qualify "Munfold") [m:Dyn x].

Ltac rrewrite1 a := rewrite a.
Ltac rrewrite2 a b := rewrite a, b.
Ltac rrewrite3 a b c := rewrite a, b, c.
Ltac rrewrite4 a b c d := rewrite a, b, c, d.
Ltac rrewrite5 a b c d e := rewrite a, b, c, d, e.

Definition compute_terminator {A} (l: mlist A) : M string :=
  match l with
  | [m:] => M.ret "_all" (* for rewrite_in *)
  | [m: _] => M.ret "1"
  | _ :m: [m:_] => M.ret "2"
  | _ :m: _ :m: [m:_] => M.ret "3"
  | _ :m: _ :m: _ :m: [m:_] => M.ret "4"
  | _ :m: _ :m: _ :m: _ :m: [m:_] => M.ret "5"
  | _ => M.failwith "Unsupported"
  end%string.

Ltac lrewrite1 a := rewrite <- a.
Ltac lrewrite2 a b := rewrite <- a, <- b.
Ltac lrewrite3 a b c := rewrite <- a, <- b, <- c.
Ltac lrewrite4 a b c d := rewrite <- a, <- b, <- c, <- d.
Ltac lrewrite5 a b c d e := rewrite <- a, <- b, <- c, <- d, <- e.

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

Ltac in_rrewrite_all x := rewrite x in *.
Ltac in_rrewrite1 x a := rewrite x in a.
Ltac in_rrewrite2 x a b := rewrite x in a, b.
Ltac in_rrewrite3 x a b c := rewrite x in a, b, c.
Ltac in_rrewrite4 x a b c d := rewrite x in a, b, c, d.
Ltac in_rrewrite5 x a b c d e := rewrite x in a, b, c, d, e.

Ltac in_lrewrite_all x := rewrite <- x in *.
Ltac in_lrewrite1 x a := rewrite <- x in a.
Ltac in_lrewrite2 x a b := rewrite <- x in a, b.
Ltac in_lrewrite3 x a b c := rewrite <- x in a, b, c.
Ltac in_lrewrite4 x a b c d := rewrite <- x in a, b, c, d.
Ltac in_lrewrite5 x a b c d e := rewrite <- x in a, b, c, d, e.

Definition trewrite_in {T} (d: RewriteDirection) (x: T) (args: mlist dyn) : tactic := \tactic g =>
  ter <- compute_terminator args;
  let prefix := match d with LeftRewrite => "l"%string | RightRewrite => "r"%string end in
  let name := reduce RedNF (qualify ("in_"++prefix++"rewrite"++ter)) in
  T.ltac name (Dyn x :m: args) g.

Notation "'rewrite_in' '->' a ; x , .. , z" :=
  (trewrite_in RightRewrite a (mcons (Dyn x) .. (mcons (Dyn z) [m:]) ..))
    (at level 0, x at next level, z at next level).
Notation "'rewrite_in' '<-' a ; x , .. , z" :=
  (trewrite_in LeftRewrite a (mcons (Dyn x) .. (mcons (Dyn z) [m:]) ..))
    (at level 0, x at next level, z at next level).
Notation "'rewrite_in' a ; x , .. , z" :=
  (trewrite_in RightRewrite a (mcons (Dyn x) .. (mcons (Dyn z) [m:]) ..))
    (at level 0, x at next level, z at next level).

Notation "'rewrite_*' '->' a" := (trewrite_in RightRewrite a [m:]) (at level 0).
Notation "'rewrite_*' '<-' a" := (trewrite_in LeftRewrite a [m:]) (at level 0).
Notation "'rewrite_*' a" := (trewrite_in a [m:]) (at level 0).

Ltac Melim h := elim h.
Definition elim {A} (x:A) : tactic :=
  T.ltac (qualify "Melim") [m: Dyn x].

Ltac Minduction v := induction v.
Definition induction {A} (x:A) : tactic :=
  T.ltac (qualify "Minduction") [m: Dyn x].

Definition injection {A} (x: A) : tactic :=
  T.ltac ("Coq.Init.Notations.injection") [m:Dyn x].

Ltac Minversion H := inversion H.
Definition inversion {A} (x: A) : tactic :=
  T.ltac (qualify "Minversion") [m:Dyn x].

Ltac Mtypeclasses_eauto := typeclasses eauto.
Definition typeclasses_eauto : tactic :=
  T.ltac (qualify "Mtypeclasses_eauto") [m:].

Ltac Mapply x := apply x.
Definition ltac_apply {A} (x:A) := T.ltac (qualify "Mapply") [m:Dyn x].

Ltac Mdestruct x := destruct x.
Definition ltac_destruct {A} (x:A) := T.ltac (qualify "Mdestruct") [m:Dyn x].

Ltac Mssrpattern p := ssrpattern p.
Definition ssrpattern {A} (x:A) := T.ltac (qualify "Mssrpattern") [m: Dyn x].

Ltac Madmit := admit.
Definition admit := T.ltac (qualify "Madmit") [m:].

Ltac Mcase n := case n.
Definition case {A} (x:A) := T.ltac (qualify "Mcase") [m: Dyn x].

Ltac Mcase_eq n := case_eq n.
Definition case_eq {A} (x:A) := T.ltac (qualify "Mcase_eq") [m: Dyn x].
