From Mtac2 Require Import Base MTele DecomposeApp Tactics.
Import TeleNotation.
Definition test_tele : MTele := [tele (x y : nat)].

Check ltac:(mrun (
                M.decompose_app'
                  (B:=fun _ => (nat*nat)%type)
                  (m:=test_tele)
                  UniMatchNoRed
                  (3+5)
                  (@plus)
                  (fun x y => M.ret (x,y)))
           ).

(* This test will fail because the evar `_` given to `@plus` will not be unified
with 3 as requested by specifying `UniMatchNoRed`. *)
Fail Check ltac:(mrun (
                M.decompose_app'
                  (B:=fun _ => nat)
                  (m:=[tele _])
                  UniMatchNoRed
                  (3+5)
                  (@plus _)
                  (fun y => M.ret (y)))
           ).
(* Once we allow unification of evars the test succeeds *)
Check ltac:(mrun (
                M.decompose_app'
                  (B:=fun _ => nat)
                  (m:=[tele _])
                  UniCoq
                  (3+5)
                  (@plus _)
                  (fun y => M.ret (y)))
           ).

Definition prop_tele : MTele :=
  mTele (fun _ : Prop => mTele (fun _ : Prop => mBase)).

Check ltac:(mrun (
                M.decompose_app'
                  (B:=fun _ => (_*_)%type)
                  (m:=prop_tele)
                  UniMatchNoRed
                  (True \/ False)
                  (@or)
                  (fun x y => M.ret (x,y)))
           ).

Import T.notations.
Goal True.
MProof.
(<[decapp (3+5) with @plus]> UniMatchNoRed (fun x y => M.print_term (x,y);; T.idtac)).
Abort.

Example dep_type (n1 n2: nat) :
  match n1 with
  | O => bool
  | S _ => unit
  end -> n2 = n2 := fun _ => eq_refl n2.

Local Close Scope tactic_scope.
Local Open Scope M_scope.
Import M.notations.
Mtac Do (
       mtry
       <[decapp dep_type O 2 true with dep_type 1 2]> UniCoq (fun u => M.print_term u)
       with | WrongTerm => M.ret tt end
     ).