From Mtac2 Require Import Base MTele DecomposeApp Tactics List.
Import M.notations.
Import ProdNotations.
Import Mtac2.List.ListNotations.
From Mtac2Tests Require Import typed_term_decomposition.

Definition test1_iter :=
       Nat.iter 5000 (fun r => test1;; r) (M.ret tt).

Time Mtac Do (test1_iter).

Definition test1_vm := Eval vm_compute in test1_iter.
Time Mtac Do (test1_vm).

Definition test2_builtin : M _ :=
  Nat.iter 5000 (fun r => M.decompose app;; r) (M.ret tt).

Definition test2_derived : M _ :=
  Nat.iter 5000 (fun r => decompose_app app;; r) (M.ret tt).

Mtac Do (M.print "Timings for built-in [M.decompose]:").
Time Mtac Do (test2_builtin).
Mtac Do (M.print "Timings for [decompose_app] derived from [decompose_app'']:").
Time Mtac Do (test2_derived).


Mtac Do (M.print "[decompose_ForallT/ForallP]").
Definition test3_iter := Nat.iter 5000 (fun r => test3;; r) (M.ret tt).
Definition test3_Prop_iter := Nat.iter 5000 (fun r => test3_Prop;; r) (M.ret tt).

Mtac Do (M.print "[decompose_forallT]").
Time Mtac Do (test3_iter).
Mtac Do (M.print "[decompose_forallP]").
Time Mtac Do (test3_Prop_iter).

Mtac Do (M.print "[decompose_forallT], pre-reduced with [vm_compute]").
Definition test3_vm := Eval vm_compute in test3_iter.
Time Mtac Do (test3_vm).

Mtac Do (M.print "[decompose_forallP], pre-reduced with [vm_compute]").
Definition test3_Prop_vm := Eval vm_compute in test3_Prop_iter.
Time Mtac Do (test3_Prop_vm).