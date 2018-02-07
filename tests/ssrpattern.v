Require Import ssrmatching.ssrmatching.

Require Import Mtac2.Mtac2.

Ltac ssrpattern p := ssrpattern p.
Definition ssrpattern {A} (x:A) := T.ltac "ssrpattern" [m: Dyn x].

Goal (3+5, 0) = (10, 0).
MProof.
  (* works with _ *)
  ssrpattern (_+_).
  T.treduce (RedOneStep [rl:RedZeta]).
  (* works with evars, but won't instantiate them *)
  e <- M.evar nat;
  f <- M.evar nat;
  ssrpattern (e+f);; (mif M.is_evar e then T.ret tt else M.failwith "evar instantiated"): tactic.
Abort.