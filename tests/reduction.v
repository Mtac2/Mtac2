From Mtac2 Require Import Datatypes Mtac2.

Require Import Lists.List.
Import ListNotations.

(** assert x y e asserts that y is syntactically equal to x. Since we
need to make sure the convertibility check is not triggered, we assume
the terms x and/or y contains an evar e that is instantiated with
tt. *)
Definition assert_eq {A} (x y: A) : M unit :=
  o1 <- M.unify x y UniMatchNoRed;
  match o1 with
    | mSome _ => M.ret tt
    | _ => M.raise (NotUnifiable x y)
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
let x := reduce (RedOneStep [rl:RedBeta]) ((fun x y=>x) tt tt) in
assert_eq x ((fun y=>tt) tt).
Qed.

Example reduce_one_wrong_step_does_nothing : unit.
MProof.
let x := reduce (RedOneStep [rl:RedDelta]) ((fun x y=>x) tt tt) in
assert_eq x ((fun x y=>x) tt tt).
Qed.

Example reduce_whd : unit.
MProof.
let x := reduce RedHNF (id ((fun x=>x) tt)) in
assert_eq x tt.
Qed.

Example is_not_breaking_letins : True.
MProof.
  let x := M.ret _ in x.
  Unshelve.
  let x := id I in M.ret x.
Qed.
Print is_not_breaking_letins.

Example reduce_beta : unit.
MProof.
let x := reduce (RedWhd [rl:RedBeta]) (id ((fun x=>x) tt)) in
assert_eq x (id ((fun x=>x) tt)).
Qed.

Example reduce_beta2 : unit.
MProof.
let x := reduce (RedWhd [rl:RedBeta]) ((fun x=>x) (fun x=>x) tt) in
assert_eq x tt.
Qed.

Example reduce_BetaDeltaIota : unit.
MProof.
let x := reduce (RedWhd [rl:RedBeta;RedDelta;RedMatch]) (elemr (Dynr (let t := tt in t))) in
assert_eq x (let t := tt in t).
Qed.

Section ASection.
  Let p := 0.

Example reduce_BetaDeltaIotaP : unit.
MProof.
let x := reduce (RedWhd [rl:RedBeta;RedDelta;RedMatch]) (elemr (Dynr (fst (p, tt)))) in
assert_eq x 0.
Qed.

Example reduce_OneStepDyn : nat.
MProof.
let x := reduce (RedOneStep [rl:RedDelta]) (elemr (Dynr p)) in
let x := reduce (RedWhd [rl:RedBeta;RedMatch]) x in M.ret x.
Qed.

Example reduce_deltac : unit.
MProof.
let x := reduce (RedWhd [rl:RedBeta;RedMatch;RedDeltaC]) (elemr (Dynr (fst (p, tt)))) in
assert_eq x p.
Qed.

Example reduce_deltax : unit.
MProof.
let x := reduce (RedStrong [rl:RedBeta;RedMatch;RedDeltaX]) (elemr (Dynr (fst (p, tt)))) in
assert_eq x (elemr (Dynr (fst (0, tt)))).
Qed.

Definition test_opaque : nat. exact 0. Qed.
Example reduce_deltac_opaque : unit.
MProof.
let x := reduce (RedWhd [rl:RedBeta;RedMatch;RedDeltaC]) (elemr (Dynr (fst (test_opaque, tt)))) in
assert_eq x test_opaque.
Qed.

End ASection.

Example reduction_only : unit.
MProof.
  (e <- M.evar unit;
  n <- M.evar nat;
  let x := reduce (RedStrong [rl:RedDeltaOnly [rl:Dyn (@id)]])
    (id ((fun x:nat=>x) n)) in
  assert_eq x ((fun A (x:A)=>x) nat ((fun x:nat=>x) n)))%MC.
  Unshelve.
  M.ret tt.
  M.ret 0.
Qed.

Example reduction_only2 : unit.
MProof.
  Fail
    (e <- evar unit;
    n <- evar nat;
    let x := reduce (RedStrong [RedBeta; RedDeltaOnly [Dyn (@id)]])
      (id ((fun x=>x)) (n+0)) in
    assert_eq x ((fun A (x:A)=>x) nat ((fun x=>x) (n + 0))))%MC.
  (e <- M.evar unit;
  n <- M.evar nat;
  let x := reduce (RedStrong [rl:RedBeta; RedDeltaOnly [rl:Dyn (@id)]])
    (id ((fun x=>x)) (n+0)) in
  M.ret tt)%MC.
  Unshelve.
  M.ret tt.
MQed.

Set Nested Proofs Allowed.

Example reduction_but : unit.
MProof.
  (e <- M.evar unit;
  n <- M.evar nat;
  let x := reduce (RedStrong [rl:RedBeta;RedMatch;RedFix;RedDeltaBut [rl:Dyn (@id)]])
    (id (fun x=>x) ((fun x=>x) (0 + n))) in
  assert_eq x (id (fun x=>x) n))%MC.
  Unshelve.
  M.ret tt. M.ret 0.
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
  M.ret res.
Qed.

Example reducion_vm : nat.
MProof.
  Time let res := reduce RedVmCompute (fib 20) in
  M.ret res.
Qed.

Example shouldn_t_fail_horribly_with_bad_ref : unit.
MProof.
  (mtry
    let x := reduce (RedStrong [rl: RedDeltaOnly [rl: Dyn "x"]]) 0 in M.failwith "Shouldn't be here"
  with ReductionFailure => M.ret tt end)%MC.
Qed.