Require Import MetaCoq.MCTactics.
Import MetaCoqNotations.

Example reduce_no_reduction : True.
MProof.
 let x := reduce RedNone ((fun x=>x) I) in ret x.
Defined.

Example reduce_simpl : True.
MProof.
 let x := reduce RedSimpl ((fun x=>x) I) in ret x.
Defined.

Example reduce_one_step : True.
MProof.
 let x := reduce RedOneStep ((fun x=>x) I) in ret x.
Defined.

Example reduce_whd : True.
MProof.
 let x := reduce RedHNF (id ((fun x=>x) I)) in ret x.
Defined.


Print reduce_no_reduction.
Print reduce_simpl.
Print reduce_one_step.
Print reduce_whd.


Example is_not_breaking_letins : True.
MProof.
  let x := ret _ in x.
  let x := id I in ret x.
Qed.
Print is_not_breaking_letins.

Example reduce_beta : True.
MProof.
 let x := reduce (RedWhd (RedBeta::nil)) (id ((fun x=>x) I)) in ret x.
Defined.

Example reduce_beta2 : True.
MProof.
 let x := reduce (RedWhd (RedBeta::nil)) ((fun x=>x) (fun x=>x) I) in ret x.
Defined.
