From Mtac2 Require Import Base Tactics Datatypes List Sorts.
Import Sorts.
Import ListNotations.
Set Implicit Arguments.
Import ProdNotations.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

(** This is a simple example tighting up a bit the types of tactics in order to
    ensure a property.  In this case, we make sure that a variation of `apply`
    is composed with as many tactics as the number required by the number of
    hypotheses of the type. *)

(** We won't statically check that the tactic isn't cheating. If the tactic
    produce a different number of subgoals, that is not our problem here. *)

(** For that reason, we use the following record instead of a Vector.t: we want
    to easily embed tactics into ntactics and back. *)
Record PackedVec (A: Type) (count: nat) := mkPackedVec {
  goals : TTs A
}.

Definition ntactic A n := goal -> M (PackedVec A n).

Import M.
Import M.notations.

Coercion n_to_g A n (nt : ntactic A n) : gtactic A := fun g=>pv <- nt g; M.ret pv.(goals).

(** For the composition, we can't be generic here: we produce a gtactic out of
    the composition of an ntactic with nth tactics. *)
Class NSeq n (nt: ntactic unit n) (l: mlist tactic) (pf: mlength l = n) :=
  nseq : tactic.
Arguments nseq {n} nt%tactic l%tactic _ {_}.

Import Mtac2.List.

Instance nseq_list n (nt: ntactic unit n) (l: mlist tactic) pf: NSeq nt l pf := fun g=>
  gs <- nt g;
  ls <- T.gmap l (msnd gs.(goals));
  let res := dreduce (@mconcat, @mapp, @msnd, @mmap) (mconcat (mmap msnd ls)) in
  gs <- T.filter_goals res;
  M.ret (m: tt, gs).

Notation "t1 '&n>' ts" :=
  (nseq t1 ts eq_refl) (at level 41, left associativity) : tactic_scope.

Import Datatypes.

(** [max_apply t] applies theorem t to the current goal.
    It generates a subgoal for each non-dependent hypothesis in the theorem. *)
Definition max_apply {T} (c : T) : tactic := fun g=>
  match g with @Goal SType gT eg =>
    (mfix1 go (d : dyn) : M (mlist goal) :=
      (* let (_, el) := d in *)
      (* mif M.unify_cumul el eg UniCoq then M.ret [m:] else *)
        mmatch d return M (mlist goal) with
        | [? T1 T2 f] @Dyn (T1 -> T2) f =>
          e <- M.evar T1;
          r <- go (Dyn (f e));
          M.ret ((Goal SType e) :m: r)
        | [? T1 T2 f] @Dyn (forall x:T1, T2 x) f =>
          e <- M.evar T1;
          r <- go (Dyn (f e));
          M.ret r
        | Dyn eg =u> M.ret [m:]
        | _ =>
          dcase d as ty, el in
          M.raise (CantApply ty gT)
        end) (Dyn c) >>= (fun gs=>M.ret (m:tt, gs))
  | Goal SProp _ => M.failwith "It's a prop!"
  | _ => M.raise NotAGoal
  end.

Definition count_nondep_binders (T: Type) : M nat :=
  (mfix1 go (T : Type) : M nat :=
    mmatch T return M nat with
    | [? T1 T2] (T1 -> T2) =>
      r <- go T2;
      M.ret (S r)
    | [? T1 T2] (forall x:T1, T2 x) =>
      name <- M.fresh_name "Z";
      nu name mNone (fun e:T1=>go (T2 e))
    | _ => M.ret 0
    end) T.

Definition napply {T} {e: runner (count_nondep_binders T)} (c : T) : ntactic unit (@eval _ _ e) := fun g=>
  ls <- max_apply c g;
  M.ret (mkPackedVec (@eval _ _ e) ls).


Import T.
Import T.notations.

Goal forall P Q, (P -> Q -> P) -> P -> Q -> P.
MProof.
  intros P Q H x y.
Fail napply H &n> [m: assumption].
Fail napply H &n> [m: ].
  pose (T := napply H &n> [m: assumption | assumption]).
  T.
Qed.

Goal forall P Q, (P -> Q -> P) -> P -> Q -> P.
MProof.
  intros P Q H x.
Fail napply H &n> [m: assumption].
Fail napply H &n> [m: ].
  pose (tac := napply H &n> [m: assumption | assumption]).
  Fail tac. (* ok, we can define the tactic, but it now fails to apply *)
  intro y.
  tac.
Qed.
