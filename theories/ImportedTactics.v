Require Import MetaCoq.MCTactics.
Import MetaCoqNotations.
Import MCTacticsNotations.

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

Ltac rrewrite h := rewrite h.
Definition rrewrite {A} (x:A) : tactic :=
  ltac (qualify "rrewrite") (cons (Dyn x) nil).

Ltac lrewrite h := rewrite <- h.
Definition lrewrite {A} (x:A) : tactic :=
  ltac (qualify "lrewrite") (cons (Dyn x) nil).

Notation "'rewrite' '->'" := rrewrite (at level 40).
Notation "'rewrite' '<-'" := lrewrite (at level 40).

Ltac elim h := elim h.
Definition elim {A} (x:A) : tactic :=
  ltac (qualify "elim") (cons (Dyn x) nil).

Notation induction := elim.