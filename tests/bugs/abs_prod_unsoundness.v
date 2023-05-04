From Mtac2 Require Import Mtac2.

Set Universe Polymorphism.

Goal nat -> Set.
  MProof.
  intros n.
  (* We cannot build something bigger than Set! This must fail. *)
  Fail M.abs_prod_type n Set.
  (* But building the right type works fine: *)
  M.abs_prod_type n nat. (* nat -> nat *)
Qed.
