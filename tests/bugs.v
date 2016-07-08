Require Import MetaCoq.MCTactics.
Require Import MetaCoq.ImportedTactics.

Require Import Bool.Bool.
Require Import Lists.List.

Import ListNotations.
Import MetaCoqNotations.
Import MCTacticsNotations.

(** A bug with destruct *)
Goal forall n:nat, 0 <= n.
MProof.
  intros.
  (* destruct n. *) (* the type of the match seems to be wrong *)
Abort.

(** a bug with call_ltac *)
Ltac induction n := induction n.

Definition induction {A} (n:A) : tactic := ltac "Top.induction" [Dyn n].
Goal forall n:nat, n >= 0.
MProof.
  intros.
  (* for the inductive case, induction generates a goal with an evar
     including the variable and its IH. we are returning this evar without
     closing it w.r.t. the enclosing environment, and therefore it fails
     to apply the lemma (and is wrong!). We need to take care of closing the evars. *)
  induction n;; [apply le_n; apply le_S].
Abort.