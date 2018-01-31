From Mtac2 Require Import Base.
Import M.notations.

Definition timer := ltac:(mrun M.new_timer).
Definition unused_timer := ltac:(mrun M.new_timer).

Definition slow := (mfix1 f (n : nat) : M unit :=
                      match n with
                      | S n => M.unify 1 1 UniCoq;; f n
                      | O => M.ret tt
                      end) 1000.
Mtac Do (
       M.start_timer true timer;;
                     slow;;
       M.stop_timer timer;;
       M.print_timer timer
     ).

Mtac Do (M.print_timer timer).

Mtac Do (
       M.start_timer false timer;;
                     slow;;
       M.stop_timer timer;;
       M.print_timer timer
     ).

Mtac Do (M.print_timer unused_timer). (* Should print 0.0 *)