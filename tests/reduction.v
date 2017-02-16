From MetaCoq
  Require Import Mtac2 Tactics.

Import MtacNotations.
Require Import Lists.List.
Import ListNotations.

(** assert x y e asserts that y is syntactically equal to x. Since we
need to make sure the convertibility check is not triggered, we assume
the terms x and/or y contains an evar e that is instantiated with
tt. *)
Definition assert_eq {A} (x y: A) (e: unit) :=
  o1 <- munify x y UniMatchNoRed;
  o2 <- munify y x UniMatchNoRed;
  match o1, o2 with
    | Some _, Some _ => munify e tt UniCoq;; ret e
    | _, _ => raise (NotUnifiable x y)
  end.

Example reduce_no_reduction : unit.
MProof.
Set Printing All.
e <- evar unit;
let x := reduce RedNone ((fun x=>x) e) in
assert_eq ((fun x=>x) e) x e.
Qed.

Example reduce_simpl : unit.
MProof.
e <- evar unit;
let x := reduce RedSimpl ((fun x=>x) e) in
assert_eq e x e.
Qed.

Example reduce_one_step : unit.
MProof.
e <- evar unit;
let x := reduce RedOneStep ((fun x y=>x) e e) in
assert_eq ((fun y=>e) e) x e.
Qed.

Example reduce_whd : unit.
MProof.
e <- evar unit;
let x := reduce RedHNF (id ((fun x=>x) tt)) in
assert_eq e x e.
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
assert_eq (id ((fun x=>x) e)) x e.
Qed.

Example reduce_beta2 : unit.
MProof.
e <- evar unit;
let x := reduce (RedWhd (RedBeta::nil)) ((fun x=>x) (fun x=>x) e) in
assert_eq e x e.
Qed.

Example reduce_BetaDeltaIota : unit.
MProof.
e <- evar unit;
let x := reduce (RedWhd (RedBeta::RedDelta::RedMatch::nil)) (elem (Dyn (let t := e in t))) in
assert_eq (let t := e in t) x e.
Qed.

Section ASection.
  Let p := 0.

Example reduce_BetaDeltaIotaP : unit.
MProof.
e <- evar unit;
let x := reduce (RedWhd (RedBeta::RedDelta::RedMatch::nil)) (elem (Dyn (fst (p, e)))) in
  print_term x;;
assert_eq 0 x e.
Qed.

Example reduce_OneStepDyn : nat.
MProof.
let x := rone_step (elem (Dyn p)) in
let x := reduce (RedWhd (RedBeta::RedMatch::nil)) x in ret x.
Qed.

Example reduce_deltac : unit.
MProof.
e <- evar unit;
  let x := reduce (RedWhd (RedBeta::RedMatch::RedDeltaC::nil)) (elem (Dyn (fst (p, e)))) in
  print_term x;;
assert_eq x 0 e.
Qed.

Definition test_opaque : nat. exact 0. Qed.
Example reduce_deltac_opaque : unit.
MProof.
e <- evar unit;
let x := reduce (RedWhd (RedBeta::RedMatch::RedDeltaC::nil)) (elem (Dyn (fst (test_opaque, e)))) in
assert_eq x test_opaque e.
Qed.

Unset Printing All.
Example reduce_deltax : unit.
MProof.
e <- evar unit;
let x := reduce (RedStrong (RedBeta::RedMatch::RedDeltaX::nil)) (elem (Dyn (fst (p, e)))) in
assert_eq (elem (Dyn (fst (0, e)))) x e.
Qed.


End ASection.

Unset Printing All.

Example reduction_only : unit.
MProof.
  e <- evar unit;
  n <- evar nat;
  let x := reduce (RedStrong [RedDeltaOnly [Dyn (@id)]])
    (id ((fun x:nat=>x) n)) in
  assert_eq x ((fun A (x:A)=>x) nat ((fun x:nat=>x) n)) e.
MQed.

Example reduction_only2 : unit.
MProof.
  Fail
    e <- evar unit;
    n <- evar nat;
    let x := reduce (RedStrong [RedBeta; RedDeltaOnly [Dyn (@id)]])
      (id ((fun x=>x)) (n+0)) in
    assert_eq x ((fun A (x:A)=>x) nat ((fun x=>x) (n + 0))) e.
  e <- evar unit;
  n <- evar nat;
  let x := reduce (RedStrong [RedBeta; RedDeltaOnly [Dyn (@id)]])
    (id ((fun x=>x)) (n+0)) in
  assert_eq x (n + 0) e.
MQed.

Example reduction_but : unit.
MProof.
  e <- evar unit;
  n <- evar nat;
  let x := reduce (RedStrong [RedBeta;RedMatch;RedFix;RedDeltaBut [Dyn (@id)]])
    (id (fun x=>x) ((fun x=>x) (0 + n))) in
  assert_eq x (id (fun x=>x) n) e.
MQed.

Abort.
Abort.
Abort. (* MQed is leaving definitions open somehow *)

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