From Coq Require Import BinNums.
From Mtac2 Require Import List.
From Mtac2.intf Require Import Dyn.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Polymorphic Inductive Cumulativity.

Record Ind_dyn :=
  mkInd_dyn {
      ind_dyn_ind : dyn;
      ind_dyn_nparams : N;
      ind_dyn_nindices : N;
      ind_dyn_constrs : mlist dyn
    }.

Record Case :=
    mkCase {
        case_ind : Type;
        case_val : case_ind;
        case_return : dyn;
        case_branches : mlist dyn
        }.