From Mtac2 Require Import Base DecomposeApp.

Mtac Do Check ltac:(mrun (MTele_of (nat) _ (@plus))).

Definition pairs := <[decapp (3 + 5) @plus ]> (fun x y => M.ret (x,y)).
Definition pairs_eq : M.eval pairs = (3, 5) := eq_refl.

Fail Definition should_fail := <[decapp (String.append "a" "b") @plus ]> (fun x y => M.ret (x,y)).

Definition dyns := <[decapp (Dyn 5) @Dyn ]> (fun ty el => M.ret ty).
Definition dyns_eq : M.eval dyns = nat := eq_refl.
