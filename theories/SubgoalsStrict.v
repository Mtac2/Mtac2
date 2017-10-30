From Mtac2 Require Import Base Tactics List.
Set Implicit Arguments.

Record PackedVec (A: Type) (count: nat) := mkPackedVec {
  goals : list (A * goal)
}.

Definition ntactic A n := goal -> M (PackedVec A n).

Import M.
Import M.notations.

Coercion n_to_g A n (nt : ntactic A n) : gtactic A := fun g=>pv <- nt g; M.ret pv.(goals).

Class NSeq (A B : Type) n (nt: ntactic A n) (l: list (gtactic B)) (pf: length l = n) :=
  nseq : gtactic B.
Arguments nseq {A B _} _%tactic _%tactic _ {_}.

Import Mtac2.List.
Instance nseq_list {A B} n (nt: ntactic A n) (l: list (gtactic B)) pf: NSeq nt l pf := fun g =>
  gs <- nt g;
  ls <- T.gmap l (map snd gs.(goals));
  let res := dreduce (List.concat, List.app) (concat ls) in
  T.filter_goals res.

Notation "t1 '&n>' ts" :=
  (nseq t1 ts eq_refl) (at level 41, left associativity) : tactic_scope.


Definition count_nondep_binders (T: Type) : M nat :=
  (mfix1 go (T : Type) : M nat :=
    mmatch T return M nat with
    | [? T1 T2] (T1 -> T2) =>
      r <- go T2;
      M.ret (S r)
    | [? T1 T2] (forall x:T1, T2 x) =>
      name <- M.fresh_name "Z";
      nu name None (fun e:T1=>go (T2 e))
    | _ => M.ret 0
    end) T.

Definition napply {T} {e: runner (count_nondep_binders T)} (c : T) : ntactic unit (@eval _ _ e) := fun g=>
  ls <- T.apply c g;
  M.ret (mkPackedVec (@eval _ _ e) ls).
Import T.
Import T.notations.
Import ListNotations.
Goal forall P Q, (P -> Q -> P) -> P -> Q -> P.
MProof.
  intros P Q H x y.
Fail napply H &n> [m: assumption].
Fail napply H &n> [m: ].
  napply H &n> [m: assumption | assumption].
Qed.
