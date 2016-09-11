Require Import MetaCoq.MCTactics.
Import MetaCoqNotations.

(** assert x y e asserts that y is syntactically equal to x. Since we
need to make sure the convertibility check is not triggered, we assume
the terms x and/or y contains an evar e that is instantiated with
tt. *)
Definition assert {A} (x y: A) (e: unit) :=
  o1 <- munify x y UniMatchNoRed;
  o2 <- munify y x UniMatchNoRed;
  match o1, o2 with
    | Some _, Some _ => munify e tt UniCoq;; ret e
    | _, _ => raise (NotUnifiable x y)
  end.

Example reduce_no_reduction : unit.
MProof.
e <- evar unit;
let x := reduce RedNone ((fun x=>x) e) in
assert ((fun x=>x) e) x e.
Qed.

Example reduce_simpl : unit.
MProof.
e <- evar unit;
let x := reduce RedSimpl ((fun x=>x) e) in
assert e x e.
Qed.

Example reduce_one_step : unit.
MProof.
e <- evar unit;
let x := reduce RedOneStep ((fun x y=>x) e e) in
assert ((fun y=>e) e) x e.
Qed.

Example reduce_whd : unit.
MProof.
e <- evar unit;
let x := reduce RedHNF (id ((fun x=>x) tt)) in
assert e x e.
Qed.

Example is_not_breaking_letins : True.
MProof.
  let x := ret _ in x.
  let x := id I in ret x.
Qed.
Print is_not_breaking_letins.

Example reduce_beta : unit.
MProof.
e <- evar unit;
let x := reduce (RedWhd (RedBeta::nil)) (id ((fun x=>x) e)) in
assert (id ((fun x=>x) e)) x e.
Qed.

Example reduce_beta2 : unit.
MProof.
e <- evar unit;
let x := reduce (RedWhd (RedBeta::nil)) ((fun x=>x) (fun x=>x) e) in
assert e x e.
Qed.

Example reduce_BetaDeltaIota : unit.
MProof.
e <- evar unit;
let x := reduce (RedWhd (RedBeta::RedDelta::RedIota::nil)) (elem (Dyn (let t := e in t))) in
assert (let t := e in t) x e.
Qed.

Section ASection.
  Let p := 0.

Example reduce_BetaDeltaIotaP : unit.
MProof.
e <- evar unit;
let x := reduce (RedWhd (RedBeta::RedDelta::RedIota::nil)) (elem (Dyn (fst (p, e)))) in
  print_term x;;
assert 0 x e.
Qed.

 Example reduce_OneStepDyn : nat.
MProof.
let x := rone_step (elem (Dyn p)) in
let x := reduce (RedWhd (RedBeta::RedIota::nil)) x in ret x.
Defined.

Example reduce_deltac : unit.
MProof.
e <- evar unit;
  let x := reduce (RedWhd (RedBeta::RedIota::RedDeltaC::nil)) (elem (Dyn (fst (p, e)))) in
  print_term x;;
assert x 0 e.
Qed.