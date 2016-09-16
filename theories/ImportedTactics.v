From MetaCoq Require Import Mtac Tactics.
Import MtacNotations.
Import TacticsNotations.

Require Import Strings.String.
Require Import Lists.List.
Import ListNotations.

Definition qualify s := String.append "MetaCoq.ImportedTactics." s.

Ltac trivial := trivial.
Definition trivial : tactic := ltac (qualify "trivial") nil.

Ltac discriminate := discriminate.
Definition discriminate : tactic := ltac (qualify "discriminate") nil.

Ltac intuition := intuition.
Definition intuition : tactic := ltac (qualify "intuition") nil.

Ltac auto := auto.
Definition auto : tactic := ltac (qualify "auto") nil.

Ltac subst := subst.
Definition subst : tactic := ltac (qualify "subst") nil.

Ltac contradiction := contradiction.
Definition contradiction : tactic := ltac (qualify "contradiction") nil.

Definition tauto : tactic := ltac ("Coq.Init.Notations.tauto") nil.


Ltac rrewrite1 a := rewrite a.
Ltac rrewrite2 a b := rewrite a, b.
Ltac rrewrite3 a b c := rewrite a, b, c.
Ltac rrewrite4 a b c d := rewrite a, b, c, d.
Ltac rrewrite5 a b c d e := rewrite a, b, c, d, e.

Definition compute_terminator {A} (l: list A) : M string :=
  match l with
  | [] => failwith "At least one required"
  | [_] => ret "1"
  | [_;_] => ret "2"
  | [_;_;_] => ret "3"
  | [_;_;_;_] => ret "4"
  | [_;_;_;_;_] => ret "5"
  | _ => failwith "Unsupported"
  end.

Ltac lrewrite1 a := rewrite <- a.
Ltac lrewrite2 a b := rewrite <- a, b.
Ltac lrewrite3 a b c := rewrite <- a, b, c.
Ltac lrewrite4 a b c d := rewrite <- a, b, c, d.
Ltac lrewrite5 a b c d e := rewrite <- a, b, c, d, e.

Inductive RewriteDirection := LeftRewrite | RightRewrite.

Definition trewrite (d: RewriteDirection) (args: list dyn) : tactic := fun g=>
  ter <- compute_terminator args;
  let prefix := match d with LeftRewrite => "l" | RightRewrite => "r" end in
  let name := reduce RedNF (qualify (prefix++"rewrite"++ter)) in
  ltac name args g.


Notation "'rewrite' '->' x , .. , z" :=
  (trewrite RightRewrite (cons (Dyn x) .. (cons (Dyn z) nil) ..))
    (at level 0, x at next level, z at next level).
Notation "'rewrite' '<-' x , .. , z" :=
  (trewrite LeftRewrite (cons (Dyn x) .. (cons (Dyn z) nil) ..))
    (at level 0, x at next level, z at next level).
Notation "'rewrite' x , .. , z" :=
  (trewrite RightRewrite (cons (Dyn x) .. (cons (Dyn z) nil) ..))
    (at level 0, x at next level, z at next level).

Ltac elim h := elim h.
Definition elim {A} (x:A) : tactic :=
  ltac (qualify "elim") (cons (Dyn x) nil).

Notation induction := elim.
