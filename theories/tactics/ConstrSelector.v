From Mtac2 Require Import Datatypes List Mtac2.
Import TacticsBase.T.
Import Mtac2.lib.List.ListNotations.
Import ProdNotations.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

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
  mfix1 fill (T : Type) : M (mlist dyn) :=
    mmatch T return M (mlist dyn) with
    | [? A B] A -> B => fill B
    | [? A (P:A->Type)] forall x, P x =>
      M.nu (FreshFrom T) mNone (fun x=>
        fill (P x)
      )
    | _ =>
      l <- M.constrs T;
      let (_, l') := l in
      M.ret l'
    end%MC.

(** Given a constructor c, it returns its index. *)
Definition index {A} (c: A) : M _ :=
  l <- get_constrs A;
  (mfix2 f (i : nat) (l : mlist dyn) : M nat :=
    mmatch l with
    | [? l'] (Dyn c :m: l') => M.ret i
    | [? d' l'] (d' :m: l') => f (S i) l'
    end)%MC 0 l.

Definition snth_index {A:Type} (c:A) (t:tactic) : T.selector unit := fun l =>
  (i <- index c; S.nth i t l)%MC.

Notation "'case' c 'do' t" := (snth_index c t) (at level 40).
Import M.notations.
Local Close Scope tactic_scope.
Definition snth_indices (l : mlist dyn) (t : tactic) : selector unit := fun goals=>
  M.fold_left (fun (accu : mlist (unit *m goal)) (d : dyn)=>
    dcase d as c in
    i <- index c;
    let ogoal := mnth_error goals i in
    match ogoal with
    | mSome (m: _, g) =>
      newgoals <- open_and_apply t g;
      let res := dreduce (@mapp, @mmap) (accu +m+ newgoals) in
      T.filter_goals res
    | mNone => M.failwith "snth_indices"
    end) l goals.

Definition apply_except (l : mlist dyn) (t : tactic) : selector unit := fun goals=>
  a_constr <- match mhd_error l with mSome d=> M.ret d | _ => M.failwith "apply_except: empty list" end;
  dcase a_constr as T, c in
  constrs <- get_constrs T;
  M.fold_left (fun (accu : mlist (unit *m goal)) (d : dyn)=>
      dcase d as c in
      i <- index c;
      let ogoal := mnth_error goals i in
      match ogoal with
      | mSome (m: _, g) =>
         mif M.find (fun d'=>M.bunify d d' UniCoq) l then
           M.ret ((m:tt, g) :m: accu)
         else
           newgoals <- open_and_apply t g;
           let res := dreduce (@mapp, @mmap) (accu +m+ newgoals) in
           T.filter_goals res
      | mNone => M.failwith "snth_indices"
      end) constrs goals.

Open Scope tactic_scope.

Notation "'case' c , .. , d 'do' t" :=
  (snth_indices (Dyn c :m: .. (Dyn d :m: [m:]) ..) t) (at level 40).

Notation "'except' c , .. , d 'do' t" :=
  (apply_except (Dyn c :m: .. (Dyn d :m: [m:]) ..) t) (at level 40).
