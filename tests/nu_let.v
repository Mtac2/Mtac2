From Mtac2 Require Import Mtac2.
Require Import Bool.Bool.

Example hyp_well_formed : True.
MProof.
  (\nu x := I,
   l <- M.hyps;
   oeq <- M.unify l [m: ahyp x (Some I)] UniCoq;
   match oeq with
   | None => M.raise exception
   | _ => M.ret I
   end)%MC.
Qed.

Example env_well_formed : True.
MProof.
  (\nu x := I,
   oeq <- M.unify x I UniCoq;
   match oeq with
   | None => M.raise exception
   | _ => M.ret I
   end)%MC.
Qed.

Example fail_returning_var : True.
MProof.
  (mtry
    (\nu x := I, M.ret x);; M.raise exception
  with VarAppearsInValue => M.ret I
  end)%MC.
Qed.
