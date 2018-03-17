From Mtac2 Require Import Mtac2 DecomposeApp.


Fixpoint goal n :=
  match n with
  | 0 => True
  | S n' => goal n' /\ goal n'
  end.

Import M.notations.

Definition with_mmatch: forall {P:Prop}, M P := mfix1 f (P: Prop) : M P :=
  mmatch P as P' return M (P':Prop) with
  | True  => M.ret I
  | [? Q R] Q /\ R =>
    r1 <- f Q;
    r2 <- f R;
    M.ret (conj r1 r2)
  end.

Definition with_decapp: forall {P:Prop}, M P := mfix1 f (P: Prop) : M P :=
  mtry
    <[decapp P return (fun P':Prop=>P') with True]>%MC UniMatchNoRed (M.ret I)
  with _ =>
    <[decapp P return (fun P':Prop=>P') with and]>%MC UniMatchNoRed (fun Q R =>
      r1 <- f Q;
      r2 <- f R;
      M.ret (conj r1 r2)
    )
  end.
(*
Section Mmatch.

Example test1_mmatch : goal 10.
MProof.
  cbv.
  Time with_mmatch.
Qed.

Example test11_mmatch : goal 11.
MProof.
  cbv.
  Time with_mmatch.
Qed.

Example test12_mmatch : goal 12.
MProof.
  cbv.
  Time with_mmatch.
Qed.

Example test13_mmatch : goal 13.
MProof.
  cbv.
  Time with_mmatch.
Qed.

Example test14_mmatch : goal 14.
MProof.
  cbv.
  Time with_mmatch.
Qed.

Example test15_mmatch : goal 15.
MProof.
  cbv.
  Time with_mmatch.
Qed.

End Mmatch.


Section Decapp.

Example test1_decapp : goal 10.
MProof.
  cbv.
  Time with_decapp.
Qed.

Example test11_decapp : goal 11.
MProof.
  cbv.
  Time with_decapp.
Qed.

Example test12_decapp : goal 12.
MProof.
  cbv.
  Time with_decapp.
Qed.

Example test13_decapp : goal 13.
MProof.
  cbv.
  Time with_decapp.
Qed.

Example test14_decapp : goal 14.
MProof.
  cbv.
  Time with_decapp.
Qed.

Example test15_decapp : goal 15.
MProof.
  cbv.
  Time with_decapp.
Qed.

End Decapp.
*)
Require Import Strings.String.

Fixpoint pollute n :=
  match n with
  | 0 => goal 10
  | S n' =>
    nat ->
    pollute n'
  end.

Module MmatchM.

Example test1_mmatch : pollute 10.
Proof.
  cbv. intros.
  Time mrun with_mmatch.
Qed.

Example test11_mmatch : pollute 100.
Proof.
  cbv. intros.
  Time mrun with_mmatch.
Qed.

Example test12_mmatch : pollute 1000.
Proof.
  cbv. intros.
  Time mrun with_mmatch.
Qed.


End MmatchM.


Module DecappM.

Example test1_decapp : pollute 10.
Proof.
  cbv. intros.
  Time mrun with_decapp.
Qed.

Example test11_decapp : pollute 100.
Proof.
  cbv. intros.
  Time mrun with_decapp.
Qed.

Example test12_decapp : pollute 1000.
Proof.
  cbv. intros.
  Time mrun with_decapp.
Qed.


End DecappM.
