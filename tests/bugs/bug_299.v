Require Import Mtac2.Mtac2.
Import M.notations.
Import M.

Inductive tFalse : Type.
Definition omg_false (f:tFalse) : Exception. constructor. Qed.

Polymorphic Definition test : M tFalse :=
  a <- evar Type;
  \nu b : a,
  mtry
    eqp <- unify_or_fail UniCoq a tFalse;
    replace b eqp (
      (* here b : nat *)
      let b' := rcbv (internal_meq_rew _ a (fun a => a) b tFalse eqp) in
      raise (omg_false b')
    )
  with
  | [? f] omg_false f => print_term f;; ret f
  end.

Fail Mtac Do test.
