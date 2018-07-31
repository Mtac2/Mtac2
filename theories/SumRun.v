From Mtac2 Require Import Mtac2 lib.Datatypes.

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


Polymorphic Cumulative Structure execV {A} (f : M A) B := ExecV { value : B } .

Canonical Structure the_value {A} (f : M A) v := ExecV _ f (lift f v) v.

Arguments value {A} f {B} {e}.

Global Set Use Unicoq.

Notation "'Σ' x .. y ,  t" :=
  (sigT (fun x => .. (sigT (fun y => t)) ..)) (at level 200, x binder, y binder).

(* Definition test {T} (t : T) : M (Σ X (x : X) f, f x = t) := *)
(*   mmatch T return M (Σ X x f, f x = t) with *)
(*   | [? X] (X -> T) => _ *)
(*   end. *)

(* Goal True. *)
(* refine (let H := _ in let _ : value (M.ret I) =m= H := meq_refl in H). *)
(* Qed. *)

Notation "'[run'  t ]" :=
  (let H := _ in let _ : value t = H := eq_refl in H).