Require Import MetaCoq.MetaCoq.

Goal forall x, 0 <= x.
MProof.
  H <- get_reference "le_0_n";
  apply H.(elem).
Qed.

Goal forall x, 0 <= x.
MProof.
  H <- get_reference "Peano.le_0_n";
  apply H.(elem).
Qed.

Goal forall x, 0 <= x.
MProof.
  H <- get_reference "Coq.Init.Peano.le_0_n";
  apply H.(elem).
Qed.

Definition myle0n := le_0_n.

Goal forall x, 0 <= x.
MProof.
  H <- get_reference "myle0n";
  apply H.(elem).
Qed.

Goal forall x, 0 <= x -> 0 <= x.
MProof.
  intros x H.
  (fun g=>
    mtry
      H <- get_reference "H";
      apply H.(elem) g
    with RefNotFound "H" => apply myle0n g
    end) : tactic.
Qed.
