From Mtac2 Require Import Base Tactics Datatypes List Sorts.
Import Sorts.S.
Import ListNotations.
Set Implicit Arguments.
Import ProdNotations.
Require Import Strings.String.

Set Universe Polymorphism.
(** This is a simple example tighting up a bit the types of tactics in order to
    ensure a property.  In this case, we make sure that a variation of `apply`
    is composed with as many tactics as the number required by the number of
    hypotheses of the type. *)

(** We won't statically check that the tactic isn't cheating. If the tactic
    produce a different number of subgoals, that is not our problem here. *)

(** For that reason, we use the following record instead of a Vector.t: we want
    to easily embed tactics into ntactics and back. *)
Record PackedVec (A: Type) (count: nat) := mkPackedVec {
  goals : mlist (A *m goal gs_any)
}.

Definition ntactic A n := goal gs_open -> M (PackedVec A n).

Import M.
Import M.notations.

Coercion n_to_g A n (nt : ntactic A n) : gtactic A := fun g=>pv <- nt g; M.ret pv.(goals).

(** For the composition, we can't be generic here: we produce a gtactic out of
    the composition of an ntactic with nth gtactics. *)
Class NSeq (A B : Type) n (nt: ntactic A n) (l: mlist (gtactic B)) (pf: mlength l = n) :=
  nseq : gtactic B.
Arguments nseq {A B _} _%tactic _%tactic _ {_}.

Import Mtac2.lib.List.

Instance nseq_list {A B} n (nt: ntactic A n) (l: mlist (gtactic B)) pf: NSeq nt l pf := fun g =>
  gs <- nt g;
  ls <- T.gmap l gs.(goals);
  let res := dreduce (@mconcat, @mapp) (mconcat ls) in
  T.filter_goals res.

Notation "t1 '&n>' ts" :=
  (nseq t1 ts eq_refl) (at level 41, left associativity) : tactic_scope.

Import Datatypes.

(** [max_apply t] applies theorem t to the current goal.
    It generates a subgoal for each non-dependent hypothesis in the theorem. *)
Definition max_apply {T} (c : T) : tactic := fun g=>
  match g with Metavar Typeₛ gT eg =>
    (mfix1 go (d : dyn) : M (mlist (unit *m goal _)) :=
      (* let (_, el) := d in *)
      (* mif M.unify_cumul el eg UniCoq then M.ret [m:] else *)
        mmatch d return M (mlist (unit *m goal _)) with
        | [? T1 T2 f] @Dyn (T1 -> T2) f =>
          e <- M.evar T1;
          r <- go (Dyn (f e));
          M.ret ((m: tt, AnyMetavar Typeₛ _ e) :m: r)
        | [? T1 T2 f] @Dyn (forall x:T1, T2 x) f =>
          e <- M.evar T1;
          r <- go (Dyn (f e));
          M.ret r
        | Dyn eg =u> M.ret [m:]
        | _ as _catchall =>
          dcase d as ty, el in
          M.raise (T.CantApply ty gT)
        end) (Dyn c)
  | Metavar Propₛ _ _ => M.failwith "It's a prop!"
  end.

Definition count_nondep_binders (T: Type) : M nat :=
  (mfix1 go (T : Type) : M nat :=
    mmatch T return M nat with
    | [? T1 T2] (T1 -> T2) =>
      r <- go T2;
      M.ret (S r)
    | [? T1 T2] (forall x:T1, T2 x) =>
      nu (FreshFromStr "name") mNone (fun e:T1=>go (T2 e))
    | _ as _catchall => M.ret 0
    end) T.

Definition napply {T} {e: runner (count_nondep_binders T)} (c : T) : ntactic unit (@eval _ _ e) := fun g=>
  ls <- max_apply c g;
  M.ret (mkPackedVec (@eval _ _ e) ls).


Import TacticsBase.T.
Import TacticsBase.T.notations.

(* Goal forall P Q, (P -> Q -> P) -> P -> Q -> P. *)
(* MProof. *)
(*   intros P Q H x y. *)
(* Fail napply H &n> [m: assumption]. *)
(* Fail napply H &n> [m: ]. *)
(*   pose (T := napply H &n> [m: assumption | assumption]). *)
(*   T. *)
(* Qed. *)

(* Goal forall P Q, (P -> Q -> P) -> P -> Q -> P. *)
(* MProof. *)
(*   intros P Q H x. *)
(* Fail napply H &n> [m: assumption]. *)
(* Fail napply H &n> [m: ]. *)
(*   pose (tac := napply H &n> [m: assumption | assumption]). *)
(*   Fail tac. (* ok, we can define the tactic, but it now fails to apply *) *)
(*   intro y. *)
(*   tac. *)
(* Qed. *)
