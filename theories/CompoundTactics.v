From Mtac2 Require Import Base Tactics ImportedTactics List Logic Abstract.

Import M. Import M.notations.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Definition simple_rewrite A {x y : A} (p : x = y) : tactic := fun g=>
  gT <- goal_type g;
  r <- abstract x gT;
  let reduced := dreduce (fu) (fu r y) in
  newG <- evar reduced;
  T.exact (eq_fu (r:=r) p newG) g;;
  ret [m: (tt, Goal newG)].

Import T.notations.
Definition variabilize {A} (t: A) name : tactic :=
  gT <- T.goal_type;
  r <- abstract t gT;
  T.cpose_base name t (fun x=>
    let reduced := dreduce (fu) (fu r x) in
    T.change reduced).
