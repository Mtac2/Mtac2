Require Import MetaCoq.MetaCoq.
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
 let x := reduce RedWhd (id ((fun x=>x) I)) in ret x.
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