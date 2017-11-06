From Mtac2 Require Import Datatypes List Mtac2.
Import T.
Import Mtac2.List.ListNotations.

(** This files defines a useful tactic to kill subgoals on groups
    based on the (position) of the constructors. For instance, for a
    variable x of some inductive type I with constructors c1, ..., cn,
    the following code applies tactic t to only constructors c1, c3,
    c5:

    [induction x &> case c5, c1, c3 do t]

    Note that there is no check on the type of x and the constructors,
    nor any check that the first tactic (induction above) will produce
    exactly n subgoals.  *)

(** Obtains the list of constructors of a type I from a type of the
   form A1 -> ... -> An -> I *)
Definition get_constrs :=
  mfix1 fill (T : Type) : M (list dyn) :=
    mmatch T with
    | [? A B] A -> B => fill B
    | [? A (P:A->Type)] forall x:A, P x =>
      name <- M.fresh_binder_name T;
      M.nu name None (fun x=>
        fill (P x)
      )
    | _ =>
      l <- M.constrs T;
      let (_, l') := l in
      M.ret l'
    end.

(** Given a constructor c, it returns its index. *)
Definition index {A} (c: A) : M _ :=
  l <- get_constrs A;
  (mfix2 f (i : nat) (l : list dyn) : M nat :=
    mmatch l with
    | [? l'] (Dyn c :: l') => M.ret i
    | [? d' l'] (d' :: l') => f (S i) l'
    end) 0 l.

Definition snth_index {A:Type} (c:A) (t:tactic) : T.selector unit := fun l =>
  (i <- index c; S.nth i t l)%MC.

Notation "'case' c 'do' t" := (snth_index c t) (at level 40).

Definition snth_indices (l:list dyn) (t:tactic) : selector unit := fun goals=>
  M.fold_left (fun (accu : list (unit * goal)) (d : dyn)=>
    let (_, c) := d in
    i <- index c;
    let ogoal := nth_error goals i in
    match ogoal with
    | Some (_, g) =>
      newgoals <- open_and_apply t g;
      let res := dreduce (app, map) (accu++newgoals) in
      T.filter_goals res
    | None => M.failwith "snth_indices"
    end)%MC l goals.

Notation "'case' c , .. , d 'do' t" :=
  (snth_indices (Dyn c :: .. (Dyn d :: nil) ..) t) (at level 40).
