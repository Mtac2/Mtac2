From Mtac2 Require Import Base List Exhaustive.
Import M.notations.

Check (mmatch 1 exhaustively_with
      | [#] S | n =n> M.print "S"
      | [#] O | =n> M.print "O"
      | _ => M.print "not in constructor normal form"
      end).

(* Test a different order *)
Check (mmatch 1 exhaustively_with
      | [#] O | =n> M.print "O"
      | [#] S | n =n> M.print "S"
      | _ => M.print "not in constructor normal form"
      end).

(* Test another order. This one makes no sense but it is exhaustive in the sense
of the checker. *)
Check (mmatch 1 exhaustively_with
      | _ => M.print "always triggered first"
      | [#] O | =n> M.print "O, never triggered"
      | [#] S | n =n> M.print "S, never triggered"
      end).

(* Forget a constructor *)
Fail Check (mmatch 1 exhaustively_with
      | [#] S | n =n> M.print "S"
      | _ => M.print "not in constructor normal form"
      end).

(* Forget another constructor *)
Fail Check (mmatch 1 exhaustively_with
      | [#] O | =n> M.print "O"
      | _ => M.print "not in constructor normal form"
      end).

(* Forget constructor, swap order. *)
Fail Check (mmatch 1 exhaustively_with
      | _ => M.print "not in constructor normal form"
      | [#] O | =n> M.print "O"
      end).

(* Check inductive type with parameter. *)
Check (mmatch cons 1 nil exhaustively_with
      | [#] @nil _ | =n> M.print "nil"
      | [#] @cons _ | a l =n> M.print "cons"
      | _ => M.print "not in constructor normal form"
      end).

(* Type inference works backworks so a syntactically different parameter later
in the list will be used for elided parameters earlier and thus might throw off
the exhaustiveness checker. Here, we make the parameter for [cons] [id nat]
instead of just [nat]. The [_] for the parameter of [nil] will also be [id nat]
and thus the checker will find neither constructor. *)
Fail Check (mmatch cons 1 nil exhaustively_with
      | [#] @nil _ | =n> M.print "nil"
      | [#] @cons (id nat) | a l =n> M.print "cons"
      | _ => M.print "not in constructor normal form"
      end).