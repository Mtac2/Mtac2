Require Import MetaCoq.MCTactics.
Require Import MetaCoq.ImportedTactics.

Require Import Bool.Bool.
Require Import Lists.List.

Import ListNotations.
Import MetaCoqNotations.
Import MCTacticsNotations.

(** A bug with destruct *)
Goal forall n:nat, 0 <= n.
MProof.
  intros.
  (* destruct n. *) (* the type of the match seems to be wrong *)
Abort.

(** A bug with the call to UniCoq *)
Example fubar (T : Type) (A : T) : M Prop:=
  oeq <- munify Prop T UniNormal;
  match oeq with
  | Some eq => ret (eq_rect Prop (fun T=>T -> Prop) id T eq A)
  | _ => raise exception
end.

Definition fubarType :=
  Eval compute in
  ltac:(mrun (mtry fubar Type (True <-> True) with _ => ret True end)).

(** With mmatch should be the same *)
Example fubar_mmatch (T : Type) (A : T) : M Prop:=
  mmatch T with
  | Prop => [eq] ret (eq_rect Prop (fun T=>T -> Prop) id T (eq_sym eq) A)
  | _ => raise exception
  end.

Definition fubarType_mmatch :=
  Eval compute in
  ltac:(mrun (mtry fubar_mmatch Type (True <-> True) with _ => ret True end)).
