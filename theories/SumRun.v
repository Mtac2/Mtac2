From Mtac2 Require Import Mtac2 Datatypes.

Module SumRunner.
  Inductive runner_sum A :=
  | success (a : A)
  | failure (e : Exception).
  Arguments success [_] _.
  Arguments failure [_] _.

  Set Primitive Projections.
  Class sum_runner A  (f : M.t A) := SR { sum_eval : runner_sum A }.
  Arguments sum_runner {A} _.
  Arguments SR {A} _ _.
  Arguments sum_eval {A} _ {_}.
  Unset Primitive Projections.
End SumRunner.

Import SumRunner.

Hint Extern 0 (sum_runner ?f) =>
(mrun (
     mtry
       (eres <- f;
        M.ret (SR f (success eres)))
       with
   | [?e : Exception] e => M.ret (SR f (failure e))
     end
   )%MC)  : typeclass_instances.

Notation "'[̇type'  T  'OR'  Exception ]" :=
                        (match _ with | success _ => T | failure _ => Exception end) : type_scope.
Notation "'[run'  t ]" :=
  (
  match sum_eval t as t' return
        (match t' with | success _ => _ | failure _ => Exception end)
  with
  | success a => a
  | failure e => e
  end).

(* Eval compute in sum_eval (@M.failwith unit ""). *)
(* Fail Eval compute in 1 + [run M.failwith (A:=nat) ""]. *)
(* Fail Eval compute in 1 + [run M.ret I]. *)
(* Eval compute in 1 + [run M.ret 1]. *)