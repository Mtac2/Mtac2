From Mtac2 Require Import Mtac2.

Goal forall x, True /\ x = 0.
MProof.
  intros x.
  match_goal with
  | [[? y |- context C [y = 0] ]] => T.change (C (y = 0 + 0))
  end.
Abort.

Goal forall x, x = 0.
MProof.
  intros x.
  match_goal with
  | [[? y |- context C [y = 0] ]] => T.change (C (y = 0 + 0))
  end.
Abort.

Goal forall x y, True /\ (x = x + (y + 0)) /\ True.
MProof.
  intros x y.
  match_goal with
  | [[ y |- context C [y + 0] ]] => T.change (C (y + (0 * 0 * 0 * 0)))
  end.
Abort.

Goal True /\ True.
MProof.
  match_goal with
  | [[ |- context C [ True ] ]] => T.change (C (id True))
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
  | [[ |- context C [ nat : Type ] ]] => T.idtac
  end. (* It works on Type *)
Abort.
