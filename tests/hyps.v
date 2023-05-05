From Mtac2 Require Import Mtac2.
Import Sorts.S.
Open Scope M_scope.
Unset Universe Minimization ToSet.

Lemma test_OK@{u1 u2 u3} : Type@{u1} -> mlist@{u3} Hyp@{u2}.
  intros.
  mrun (M.hyps).
Qed.

Lemma test_KO@{u1 u2 u3|u2 < u1} : Type@{u1} -> mlist@{u3} Hyp@{u2}.
  intros.
  (* With [u1] bigger than [u2] we can no longer fit [Type@{u1}] into [Hyp@{u2}].  *)
  Fail mrun M.hyps@{u3 u2}.
  (* Make sure we get the expected exception *)
  mrun (mtry M.hyps@{u3 u2};; M.raise exception with | HypsUniverseError => M.ret mnil end).
Qed.
