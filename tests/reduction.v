From MetaCoq
  Require Import Mtac2 Tactics Plist.

Import MtacNotations.
Import PlistNotations.

(** assert x y e asserts that y is syntactically equal to x. Since we
need to make sure the convertibility check is not triggered, we assume
the terms x and/or y contains an evar e that is instantiated with
tt. *)
Definition assert_eq {A} (x y: A) :=
  o1 <- munify x y UniMatchNoRed;
  match o1 with
    | Some _ => ret tt
    | _ => raise (NotUnifiable x y)
  end.

Example reduce_no_reduction : unit.
MProof.
(* testing the eq check: it should fail *)
Fail let x := reduce RedNone ((fun x=>x) tt) in
assert_eq x tt.
Fail let x := reduce RedNone ((fun x=>x) tt) in
assert_eq tt x.

let x := reduce RedNone ((fun x=>x) tt) in
assert_eq ((fun x=>x) tt) x.
Qed.

Example reduce_simpl : unit.
MProof.
let x := reduce RedSimpl ((fun x=>x) tt) in
assert_eq x tt.
Qed.

Example reduce_one_step : unit.
MProof.
let x := reduce RedOneStep ((fun x y=>x) tt tt) in
assert_eq x ((fun y=>tt) tt).
Qed.

Example reduce_whd : unit.
MProof.
let x := reduce RedHNF (id ((fun x=>x) tt)) in
assert_eq x tt.
Qed.

Example is_not_breaking_letins : True.
MProof.
  let x := ret _ in x.
  let x := id I in ret x.
Qed.
Print is_not_breaking_letins.

Example reduce_beta : unit.
MProof.
let x := reduce (RedWhd (RedBeta::pnil)) (id ((fun x=>x) tt)) in
assert_eq x (id ((fun x=>x) tt)).
Qed.

Example reduce_beta2 : unit.
MProof.
let x := reduce (RedWhd (RedBeta::pnil)) ((fun x=>x) (fun x=>x) tt) in
assert_eq x tt.
Qed.

Example reduce_BetaDeltaIota : unit.
MProof.
let x := reduce (RedWhd (RedBeta::RedDelta::RedMatch::pnil)) (elem (Dyn (let t := tt in t))) in
assert_eq x (let t := tt in t).
Qed.

Section ASection.
  Let p := 0.

Example reduce_BetaDeltaIotaP : unit.
MProof.
let x := reduce (RedWhd (RedBeta::RedDelta::RedMatch::pnil)) (elem (Dyn (fst (p, tt)))) in
assert_eq x 0.
Qed.

Example reduce_OneStepDyn : nat.
MProof.
let x := rone_step (elem (Dyn p)) in
let x := reduce (RedWhd (RedBeta::RedMatch::pnil)) x in ret x.
Qed.

Example reduce_deltac : unit.
MProof.
let x := reduce (RedWhd (RedBeta::RedMatch::RedDeltaC::pnil)) (elem (Dyn (fst (p, tt)))) in
assert_eq x p.
Qed.

Example reduce_deltax : unit.
MProof.
let x := reduce (RedStrong (RedBeta::RedMatch::RedDeltaX::pnil)) (elem (Dyn (fst (p, tt)))) in
assert_eq x (elem (Dyn (fst (0, tt)))).
Qed.

Definition test_opaque : nat. exact 0. Qed.
Example reduce_deltac_opaque : unit.
MProof.
let x := reduce (RedWhd (RedBeta::RedMatch::RedDeltaC::pnil)) (elem (Dyn (fst (test_opaque, tt)))) in
assert_eq x test_opaque.
Qed.

End ASection.

Example reduction_only : unit.
MProof.
  e <- evar unit;
  n <- evar nat;
  let x := reduce (RedStrong [RedDeltaOnly [Dyn (@id)]])
    (id ((fun x:nat=>x) n)) in
  assert_eq x ((fun A (x:A)=>x) nat ((fun x:nat=>x) n)).
  ret tt.
  ret 0.
Qed.

Example reduction_only2 : unit.
MProof.
  Fail
    e <- evar unit;
    n <- evar nat;
    let x := reduce (RedStrong [RedBeta; RedDeltaOnly [Dyn (@id)]])
      (id ((fun x=>x)) (n+0)) in
    assert_eq x ((fun A (x:A)=>x) nat ((fun x=>x) (n + 0))).
  e <- evar unit;
  n <- evar nat;
  let x := reduce (RedStrong [RedBeta; RedDeltaOnly [Dyn (@id)]])
    (id ((fun x=>x)) (n+0)) in
  ret tt.
  ret tt.
MQed.

Example reduction_but : unit.
MProof.
  e <- evar unit;
  n <- evar nat;
  let x := reduce (RedStrong [RedBeta;RedMatch;RedFix;RedDeltaBut [Dyn (@id)]])
    (id (fun x=>x) ((fun x=>x) (0 + n))) in
  assert_eq x (id (fun x=>x) n).
  ret tt. ret 0.
Qed.

Fixpoint fib (n : nat) :=
  match n with
  | 0 => 1
  | S n' =>
    match n' with
    | 0 => 1
    | S n'' => fib n' + fib n''
    end
  end.

Example reducion_cbv : nat.
MProof.
  Time let res := reduce RedNF (fib 20) in
  ret res.
Qed.

Example reducion_vm : nat.
MProof.
  Time let res := reduce RedVmCompute (fib 20) in
  ret res.
Qed.