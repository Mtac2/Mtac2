Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

(** This module offers two types to encode an element with its type. *)

(** The type [dyn] is trivially constructed with [mkdyn], although it's not
    expected to be used by the user. Instead, the "constructor function" [Dyn]
    should be used. The reason for this seemingly weird construction is that we
    want [dyn] to not introduce new universes.  In order to inspect an element
    of type [dyn], we need to resort to the [decompose_app] primitive (which has
    specific notation for this case, see the [M] module). *)
Variant dyn : Prop := mkdyn.

Definition Dyn : forall {type : Type} (elem : type), dyn. refine (fun _ _=> mkdyn). Qed.

(** [dynr] is a traditional record, and it generates a universe and its restriction.  *)
Record dynr := Dynr { typer: Type; elemr:> typer }.
Arguments Dynr {_} _.
