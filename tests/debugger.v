From Mtac2 Require Import Mtac2 List Debugger.
Import Mtac2.List.ListNotations.

Import M.notations.

Definition test : unit := ltac:(mrun (debug true [m:] (M.ret I))).


Goal True.
MProof.
  debugT false [m: (*HAVE FUN Dyn (@M.ret) | Dyn (@M.unify) *)] (T.apply I).
Qed.

Goal unit.
MProof.
  (* Prints `6` *)
  Fail (let x := reduce (RedStrong RedAll) (3+3) in M.print_term x;; M.failwith "").
  (* Prints `rbcv (3+3)` *)
  Fail (debug true [m:Dyn (@M.ret)] (let x := reduce (RedStrong RedAll) (3+3) in M.print_term x;; M.failwith "")).
Abort.

Goal Exception.
  MProof.
  debugT true [m:] (mtry mmatch (forall x, x > 0) with
                      [? (A:Type) (P : A -> Prop)] forall y:A, P y => T.raise _ end with [? e] e => T.exact e end).
Abort.