From MetaCoq Require Import MetaCoq.

Goal forall x, 0 <= x.
MProof.
  H <- M.get_reference "le_0_n";
  let (_, e) := H :dyn in
  T.apply e.
Qed.

Goal forall x, 0 <= x.
MProof.
  H <- M.get_reference "Peano.le_0_n";
  match H with
  | Dyn e => T.exact e
  end.
Qed.

Goal forall x, 0 <= x.
MProof.
  H <- M.get_reference "Coq.Init.Peano.le_0_n";
  match H with
  | Dyn e => T.apply e
  end.
Qed.

Definition myle0n := le_0_n.

Goal forall x, 0 <= x.
MProof.
  H <- M.get_reference "myle0n";
  match H with
  | Dyn e => T.apply e
  end.
Qed.

Goal forall x, 0 <= x -> 0 <= x.
MProof.
  intros x H.
  mtry
    H <- M.get_reference "H";
    T.apply H.(elem)
  with RefNotFound "H" => T.apply myle0n
  end.
Qed.

Goal forall x, 0 <= x.
MProof.
  H <- M.get_reference "Peano.le_0_n";
  T.exact H.(elem).
Fail Qed.
(* it rightfully complains that the universe in elem is not compatible with the one from H.
   This is why it should be destroyed as done previously. *)
Abort.
