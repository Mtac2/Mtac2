Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

Inductive dyn : Prop := mkdyn.
(* Definition Dyn : forall {sort : Sort} {type : stype_of sort} (elem : selem_of type), dyn. refine (fun _ _ _=> mkdyn). Qed. *)
Definition Dyn : forall {type : Type} (elem : type), dyn. refine (fun _ _=> mkdyn). Qed.

Record dynr := Dynr { typer: Type; elemr:> typer }.
Arguments Dynr {_} _.
