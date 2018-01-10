From Mtac2 Require Import Mtac2.

Goal forall x, 0 <= x.
MProof.
  H <- M.get_reference "le_0_n";
  dcase H as e in
  T.apply e.
Qed.

Goal forall x, 0 <= x.
MProof.
  H <- M.get_reference "Peano.le_0_n";
  dcase H as e in
  T.exact e.
Qed.

Goal forall x, 0 <= x.
MProof.
  H <- M.get_reference "Coq.Init.Peano.le_0_n";
  dcase H as e in T.apply e.
Qed.

Definition myle0n := le_0_n.

Goal forall x, 0 <= x.
MProof.
  H <- M.get_reference "myle0n";
  dcase H as e in T.apply e.
Qed.

Goal forall x, 0 <= x -> 0 <= x.
MProof.
  intros x H.
  mtry
    H <- M.get_reference "H";
    dcase H as e in T.apply e
  with RefNotFound "H" => T.apply myle0n
  end.
Qed.

(* We don't have this issue anymore *)
(* Goal forall x, 0 <= x. *)
(* MProof. *)
(*   H <- M.get_reference "Peano.le_0_n"; *)
(*   T.exact H.(elem). *)
(* Fail Qed. *)
(* (* it rightfully complains that the universe in elem is not compatible with the one from H. *)
(*    This is why it should be destroyed as done previously. *) *)
(* Abort. *)
