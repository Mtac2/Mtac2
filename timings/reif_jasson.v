From Mtac2Tests Require Import reif_jasson.
Import PHOAS.

Local Notation n_small := 50%nat.
Local Notation n := 1000%nat.

Goal True.
  assert (H : exists e, Denote e = big 1 n).
  { cbv [big].
    eexists.
    (* Time let v := lazymatch goal with |- _ = ?x => x end in *)
    (*      let k := Ltac2LowLevel.Reify v in *)
    (*      idtac. (* 0.096 s *) *)
    Time let v := lazymatch goal with |- _ = ?x => x end in
         let k := LtacTacInTermExplicitCtx.Reify v in
         idtac. (* 9.87 s *)
    admit. }
  clear H.
  assert (H : exists e, Denote e = big 1 n_small).
  { cbv [big].
    eexists.
    (* Time let v := lazymatch goal with |- _ = ?x => x end in *)
    (*      let k := Ltac2LowLevel.Reify v in *)
    (*      idtac. (* 0.005 s *) *)
    Time let v := lazymatch goal with |- _ = ?x => x end in
         let k := LtacTacInTermExplicitCtx.Reify v in
         idtac. (* 0.044 s *)
    Time let v := lazymatch goal with |- _ = ?x => x end in
         let k := Mtac2Mmatch.Reify v in
         idtac. (* 11.657 s *)
    Time let v := lazymatch goal with |- _ = ?x => x end in
         let k := MTac2.Reify v in
         idtac. (* 7.771 s *)
    CanonicalStructuresPHOAS.pre_Reify_rhs ().
    Focus 2.
    Time refine eq_refl. (* 1.893 s *)
    admit. }
  clear H.
  assert (H : exists e, Denote e = big_flat 1 n).
  { cbv [big_flat big_flat_op].
    eexists.
    (* Time let v := lazymatch goal with |- _ = ?x => x end in *)
    (*      let k := Ltac2LowLevel.Reify v in *)
    (*      idtac. (* 0.065 s *) *)
    Time let v := lazymatch goal with |- _ = ?x => x end in
         let k := LtacTacInTermExplicitCtx.Reify v in
         idtac. (* 0.223 s *)
    Time let v := lazymatch goal with |- _ = ?x => x end in
         let k := Mtac2Mmatch.Reify v in
         idtac. (* 4.157 s *)
    Time let v := lazymatch goal with |- _ = ?x => x end in
         let k := MTac2.Reify v in
         idtac. (* 0.219 s *)
    CanonicalStructuresPHOAS.pre_Reify_rhs ().
    Focus 2.
    Time refine eq_refl. (* 0.599 s *)
    admit. }
Abort.