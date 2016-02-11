Require Import MetaCoq.MetaCoq.

Definition CouldntRefine (A B : Type) : Exception. exact exception. Qed.

Inductive Tactic : Prop :=
| Tthen : Tactic -> Tactic -> Tactic
| Trefine : forall {A}, A -> Tactic
| Tlet : forall {A}, MetaCoq A -> (A -> Tactic) -> Tactic
| Tor : Tactic -> (Exception -> Tactic) -> Tactic
| Traise : Exception -> Tactic
| Tmark_as_goal : forall {A}, A -> Tactic
| Tfocus : nat -> nat -> Tactic -> Tactic
| Tshelve : Tactic
(*
| Tunshelve : Tactic (list goal)
| Tfinished : Tactic bool
| Tmark_as_goal : forall {A}, A -> Tactic unit
*).
