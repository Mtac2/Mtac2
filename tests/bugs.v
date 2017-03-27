Require Import MetaCoq.MetaCoq.

Require Import Bool.Bool.
Import T.

(** A bug with destruct *)
Goal forall n:nat, 0 <= n.
MProof.
  intros.
  (* destruct n. *) (* the type of the match seems to be wrong *)
Abort.

(** It was throwing an exception, but now it works *)
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
MProof.
intros n. cintros m {- destruct m -}.
Abort.

(** A bug with the call to UniCoq (solved) *)
Example fubar (T : Type) (A : T) : M Prop:=
  oeq <- M.unify Prop T UniCoq;
  match oeq with
  | Some eq => M.ret (eq_rect Prop (fun T=>T -> Prop) id T eq A)
  | _ => M.raise exception
end.

Definition fubarType :=
  Eval compute in
  ltac:(mrun (mtry fubar Type (True <-> True) with _ => M.ret True end)%MC).

(** With mmatch should be the same *)
Example fubar_mmatch (T : Type) (A : T) : M Prop:=
  mmatch T with
  | Prop => [eq] M.ret (eq_rect Prop (fun T=>T -> Prop) id T (eq_sym eq) A)
  | _ => M.raise exception
  end.

Definition fubarType_mmatch :=
  Eval compute in
  ltac:(mrun (mtry fubar_mmatch Type (True <-> True) with _ => M.ret True end)%MC).

(** the bind overloaded notation was reducing terms using typeclasses. destcase expects a match, but it finds false *)
Definition destcase_fail := ltac:(mrun (r <- M.ret (match 3 with 0 => true | _ => false end); _ <- M.destcase r; M.ret I)%MC).

(** with the bind construct it works. this proves that the <- ; notation is reducing *)
Definition destcase_work := ltac:(mrun (M.bind (M.destcase (match 3 with 0 => true | _ => false end)) (fun _=> M.ret I))).
