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
  match_goal with
  | [[? y |- context C [y = 0 : Type] ]] => change (C (y = 0 + 0))
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

Goal True /\ True.
MProof.
  match_goal with
  | [[ |- context C [ True ] ]] => change (C (id True))
  end. (* works on Prop goals *)
Abort.

Goal nat * nat.
MProof.
  Fail match_goal with
  | [[ |- context C [ nat : Set ] ]] => idtac
  end. (* It fails on non Prop goals... *)
Abort.

Goal nat * nat.
MProof.
  match_goal with
  | [[ |- context C [ nat : Type ] ]] => idtac
  end. (* It works on Type *)
Abort.