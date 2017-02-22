From MetaCoq Require Import MetaCoq.

Goal forall x, True /\ x = 0.
MProof.
  intros x.
  match_goal with
  | [[? y |- context C [y = 0] ]] => change (C (y = 0 + 0))
  end.
  (* Result : True /\ (fun a : Prop => a) (x = 0 + 0)
  How to get rid of the identity? *)
Abort.

Goal forall x, x = 0.
MProof.
  intros x.
Fail  match_goal with
  | [[? y |- context C [y = 0] ]] => change (C (y = 0 + 0))
  end.
  (* Error: Uncaught exception: NoPatternMatchesGoal
  Why does this fail? *)
Abort.

Goal forall x y, True /\ (x = x + (y + 0)) /\ True.
MProof.
  intros x y.
  match_goal with
  | [[ y |- context C [y + 0] ]] => change (C (y + (0 * 0 * 0 * 0)))
  end.
  (* Result: True /\ x = x + (fun a : nat => a) (y + (0 * 0 * 0 * 0)) /\ True
  How to get rid of the identity? *)
Abort.
