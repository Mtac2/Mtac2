(** Load library "mtac2Plugin.cma". *)
Declare ML Module "mtac2Plugin".

Inductive Reduction : Type :=
| RedNone : Reduction
| RedSimpl : Reduction
| RedWhd : Reduction
| RedOneStep : Reduction.

Inductive Mtac2 : Type -> Prop :=
| tret : forall {A}, Reduction -> A -> Mtac2 A
| bind : forall {A B}, Mtac2 A -> (A -> Mtac2 B) -> Mtac2 B.

Module Mtac2Notations.

  Notation "'ret'" := (tret RedNone).

  Notation "r '<-' t1 ';' t2" := (@bind _ _ t1 (fun r => t2))
                                   (at level 81, right associativity).
  Notation "t1 ';;' t2" := (@bind _ _ t1 (fun _ => t2))
                             (at level 81, right associativity).
  Notation "f @@ x" := (bind f (fun r=>ret (r x))) (at level 70).
  Notation "f >> x" := (bind f (fun r=>x r)) (at level 70).

End Mtac2Notations.