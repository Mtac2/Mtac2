From Mtac2 Require Import Mtac2 Ttactics.


From Coq Require Import String.

Check ltac:(mrun (do_def "tt_lt_trans" (@PeanoNat.Nat.lt_trans))).
Check tt_lt_trans.

Arguments tt_lt_trans {_ _ _}.

(* (** Example: transitivity *) *)
(* Definition trans {x y z: nat} : M ((x < z) * (z < y) =m> x < y) := *)
(*   tg1 <- evar _; *)
(*   tg2 <- evar _; *)
(*   ret ((tg1, tg2), PeanoNat.Nat.lt_trans _ _ _ tg1 tg2). *)
Import TT.
Import TT.notations.

Goal 1 < 3 -> 3 < 4 -> 1 < 4.
MProof.
  intros.
  compl tt_lt_trans [t: assumption | assumption ].
Qed.

Goal 1 < 3 -> 3 < 4 -> 1 < 4.
MProof.
  intros.
  compl tt_lt_trans [t: use T.assumption |  assumption].
Qed.

Goal 1 < 3 -> 3 < 4 -> 1 < 4.
MProof.
  intros.
  to_tactic tt_lt_trans &> T.try T.assumption.
Qed.
