From Mtac2 Require Import Mtac2 CompoundTactics.
From Coq.Arith Require Import Arith.

Example beq_nat_ex : forall n, if beq_nat n 3 then True else True.
MProof.
  intros n.
  CT.destruct_eq (beq_nat _ _).
  - simpl. intro H. T.exact I.
  - simpl. intro H. T.exact I.
Qed.

Example beq_nat_ex_comp : forall n, if beq_nat n 3 then True else True.
MProof.
  intros n.
  CT.destruct_eq (beq_nat _ _) &> simpl &> intros &> T.exact I.
Qed.
