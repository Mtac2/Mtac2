From MetaCoq Require Import MetaCoq.

Goal forall x, 0 <= x.
MProof.
  H <- get_reference "le_0_n";
  let (_, e) := H :dyn in
  apply e.
Qed.

Goal forall x, 0 <= x.
MProof.
  H <- get_reference "Peano.le_0_n";
  match H with
  | Dyn e => exact e
  end.
Qed.

Goal forall x, 0 <= x.
MProof.
  H <- get_reference "Coq.Init.Peano.le_0_n";
  match H with
  | Dyn e => apply e
  end.
Qed.

Definition myle0n := le_0_n.

Goal forall x, 0 <= x.
MProof.
  H <- get_reference "myle0n";
  match H with
  | Dyn e => apply e
  end.
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
