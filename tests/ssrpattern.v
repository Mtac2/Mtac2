From Mtac2 Require Import Mtac2.

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

Import M.notations.
(* abstract _from_sort and _from_term *)
Goal True->True.
MProof.
  opf <- T.abstract_from_sort Propₛ 3 (3+3 = 6);
  match opf with
  | mSome f=> M.print_term f
  | mNone => M.failwith "abstract failed!"
  end;;
  M.ret _.
Unshelve.
  opf <- T.abstract_from_term 3 (_+3 = 6);
  match opf with
  | mSome f=> M.print_term f
  | mNone => M.failwith "abstract failed!"
  end;;
  M.ret _.
Abort.