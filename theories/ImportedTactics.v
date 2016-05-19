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

Ltac tauto := tauto.
Definition tauto : tactic := ltac (qualify "tauto") nil.
