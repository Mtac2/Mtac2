Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Inductive Unification : Set :=
| UniCoq : Unification
| UniMatch : Unification
| UniMatchNoRed : Unification
| UniEvarconv : Unification.