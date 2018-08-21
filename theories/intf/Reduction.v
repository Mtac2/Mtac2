From Mtac2.intf Require Import Dyn.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Monomorphic Inductive redlist A := rlnil | rlcons : A -> redlist A -> redlist A.

Arguments rlnil {_}.
Arguments rlcons {_} _ _.

Notation "[rl: ]" := rlnil.
Notation "[rl: x ; .. ; y ]" := (rlcons x (.. (rlcons y rlnil) ..)).

Monomorphic Inductive RedFlags : Set :=
| RedBeta | RedDelta | RedMatch | RedFix | RedZeta
| RedDeltaC | RedDeltaX
| RedDeltaOnly : redlist dyn -> RedFlags
| RedDeltaBut : redlist dyn -> RedFlags.

Monomorphic Inductive Reduction : Set :=
| RedNone
| RedSimpl
| RedOneStep : redlist RedFlags -> Reduction
| RedWhd : redlist RedFlags -> Reduction
| RedStrong : redlist RedFlags -> Reduction
| RedVmCompute.

(* Reduction primitive. It throws [NotAList] if the list of flags is not a list.  *)
Definition reduce (r : Reduction) {A:Type} (x : A) := x.

Notation RedAll := ([rl:RedBeta;RedDelta;RedZeta;RedMatch;RedFix]).
Notation RedNF := (RedStrong RedAll).
Notation RedHNF := (RedWhd RedAll).

Notation rsimpl := (reduce RedSimpl).
Notation rhnf := (reduce RedHNF).
Notation rcbv := (reduce RedNF).
Notation "'dreduce' ( l1 , .. , ln )" :=
  (reduce (RedStrong [rl:RedBeta; RedFix; RedMatch;
           RedDeltaOnly (rlcons (Dyn (@l1)) ( .. (rlcons (Dyn (@ln)) rlnil) ..))]))
  (at level 0).
