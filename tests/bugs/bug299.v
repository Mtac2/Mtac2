Require Import Mtac2.Mtac2.
Import M.notations.
Import M.

Inductive tFalse : Type.
Definition omg_false (f:tFalse) : Exception. constructor. Qed.

Polymorphic Definition test : M unit :=
  a <- evar Type;
  \nu b : a,
  mtry' (
    eqp <- unify_or_fail UniCoq a tFalse;
    (* replace b eqp ( *)
      (* here b : nat *)
      let b' := rcbv (internal_meq_rew _ a (fun a => a) b tFalse eqp) in
      raise (omg_false b')
    (* ) *)
  )
  (fun e =>
     mif is_evar a then
       unify_or_fail UniCoq a nat;;
       dbg_term "a: " a;; print_term e;;
       failwith "a was not instantiated, although b has its type"
     else
       print "All good, a was instantiated with b's type (tFalse)";;
       ret tt).

Mtac Do test.
