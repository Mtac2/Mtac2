(* Need to load Unicoq to get the module dependency right *)
Declare ML Module "unicoq".
(** Load library "MetaCoqPlugin.cma". *)
Declare ML Module "MetaCoqPlugin".

Require Import Lists.List.
Import ListNotations.

Set Printing Universes.

Record dyn := Dyn { type : Type; elem :> type }.
(* Top.2 |=  *)
Arguments Dyn {_} _.

Inductive RedFlags :=
| RedBeta | RedDelta | RedMatch | RedFix | RedZeta
| RedDeltaC | RedDeltaX
| RedDeltaOnly : list dyn -> RedFlags
| RedDeltaBut : list dyn -> RedFlags.
(*  |= Top.2 < Coq.Init.Datatypes.44 (univ. from list)
        *)

Inductive Reduction :=
| RedNone
| RedSimpl
| RedOneStep
| RedWhd : list RedFlags -> Reduction
| RedStrong : list RedFlags -> Reduction
| RedVmCompute.

(* Reduction primitive. It throws [NotAList] if the list of flags is not a list.  *)
Definition reduce (r : Reduction) {A} (x : A) := x.

(** goal type *)
Inductive goal :=
  | Goal : forall {A}, A -> goal
  | AHyp : forall {A}, option A -> (A -> goal) -> goal
  | HypRem : forall {A}, A -> goal -> goal.
(* Top.11 Top.13 Top.15 |= Top.13 <= Coq.Init.Datatypes.13 (the univ from option)
                            *)

(** Convertion functions from [dyn] to [goal]. *)
Definition dyn_to_goal (d : dyn) : goal :=
  match d with
  | Dyn x => Goal x
  end.
(*  |= Top.2 <= Top.11
        *)

Set Use Unicoq.
Set Printing Universes.
Set Unicoq Debug.

(* Cannot enforce Top.11 < Top.25 because Top.25 <= Coq.Lists.List.167 (the type of elements in map) < Top.2 <= Top.11 *)
Definition rem_hyp {A B} (x : B) (l: list (A * goal)) : (list (A * goal)) :=
  reduce (RedStrong [RedDeltaOnly [Dyn (@List.map)]]) (List.map (fun '(y,g) => (y, HypRem x g)) l).
