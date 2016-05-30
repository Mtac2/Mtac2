Require Import MetaCoq.MCTactics.
Require Import Bool.Bool.
Require Import Lists.List.

Import ListNotations.
Import MetaCoqNotations.
Import MCTacticsNotations.

Example hyp_well_formed : True.
MProof.
  nu x := I,
   l <- hypotheses;
   oeq <- munify l [ahyp x (Some I)] UniNormal;
   match oeq with
   | None => raise exception
   | _ => ret I
   end.
Qed.

Example env_well_formed : True.
MProof.
  nu x := I,
   oeq <- munify x I UniNormal;
   match oeq with
   | None => raise exception
   | _ => ret I
   end.
Qed.
