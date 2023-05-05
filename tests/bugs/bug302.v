Require Import Mtac2.Mtac2.
Import M.notations.
Import M.

Inductive tFalse : Set.
Definition omg_false (f:tFalse) : Exception. constructor. Qed.

Polymorphic Definition test : M unit :=
  a <- evar Type;
  \nu b : a,
  mtry' (
    eqp <- unify_or_fail UniCoq a tFalse;
    replace b eqp (
      (* here b : nat *)
      let b' := rcbv (internal_meq_rew _ a (fun a => a) b tFalse eqp) in
      raise (omg_false b')
    )
  )
  (fun e =>
     hs <- hyps;
     match hs with
     | [m: h] =>
       mmatch h with
       | [#] @ahyp | a' b' o =n>
         mmatch a' with
         | [#] tFalse | =n>
           mif is_evar a then
             failwith "a is still an evar, but b has its type"
           else print "all good"
         | _ =>
           mif is_evar a then
             failwith "a is still an evar, but b has its type"
           else
             dbg_term "a' is " a';; failwith "No idea of what happened!"
         end
       end
     | _ => failwith "more than one hypothesis?"
     end).

Mtac Do test.
