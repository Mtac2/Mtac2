From Mtac2 Require Import Mtac2.
Import M.
Import M.notations.

Require Import Lists.List.
Import ListNotations.

Definition rew_hd_error : tactic :=
  match_goal with
  | [[? A (l: list A) |- context C[hd_error l] ]] =>
    match l with
    | [] => rewrite hd_error_nil
    | (_ :: _) => rewrite hd_error_cons
    end
  end.

Goal hd_error [1] = Some 1.
MProof.
  rew_hd_error.
  T.reflexivity.
Qed.