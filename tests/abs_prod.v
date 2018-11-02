Require Import Mtac2.Mtac2.

Goal forall x:nat, True.
MProof.
  intro x.
  (aP <- M.abs_prod_type x (x <= 0:Type);
   mmatch aP with (forall y, y <= 0:Type) =c> M.ret _ | _ => M.failwith "Didn't work" end)%MC.
Abort.

Import M.
Import M.notations.

Goal forall x:nat, True.
MProof.
  intro x.
  aP <- M.abs_prod_type x (x <= 0:Type);
  unify_or_fail UniCoq (forall y, y <= 0:Type) aP;;
  ret I.
Qed.

(* TODO: it fails with Unicoq, why?? *)
Goal forall x:nat, True.
MProof.
  intro x.
  pose (K := aP <- M.abs_prod_type x (x <= 0:Type);
  mmatch aP with (forall y, y <= 0):Type => M.ret I end).
  K.
Qed.

Fixpoint n_ary n :=
  match n with
  | 0 => True
  | S n' => True -> n_ary n'
  end.

Goal let x := 1 in Prop.
  intros x.
  pose (t := M.abs_prod_prop x (eq_refl = (eq_refl : n_ary x = (True -> True)))).
  Fail mrun (t >>= T.exact)%tactic.
  (* It should fail because otherwise it will create an ill-typed prop *)
Abort.
