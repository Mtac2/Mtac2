From Mtac2 Require Import List.
From Mtac2.intf Require Import Dyn.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Record Case :=
    mkCase {
        case_ind : Type;
        case_val : case_ind;
        case_return : dyn;
        case_branches : mlist dyn
        }.