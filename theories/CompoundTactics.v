From Mtac2 Require Import Base Tactics ImportedTactics Datatypes List Logic Abstract Sorts.
Import Sorts.
Import M. Import M.notations.
Import ListNotations.
Import ProdNotations.

Require Import Strings.String.

Set Implicit Arguments.
Unset Strict Implicit.

Module CT.

Definition SimpleRewriteNoOccurrence : Exception. constructor. Qed.
Definition simple_rewrite A {x y : A} (p : x = y) : tactic := fun g=>
  gT <- goal_type g;
  r <- abstract x gT;
  match r with
  | mSome r =>
    let reduced := dreduce (fu) (fu r y) in
    newG <- evar reduced;
    T.exact (eq_fu (r:=r) p newG) g;;
    ret [m: (m: tt, Goal SType newG)]
  | mNone => M.raise SimpleRewriteNoOccurrence
  end.

Import T.notations.
Definition CVariablizeNoOccurrence : Exception. constructor. Qed.
Definition cvariabilize_base {A} (t: A) name (cont: A -> tactic) : tactic :=
  gT <- T.goal_type;
  r <- abstract t gT;
  match r with
  | mSome r =>
    T.cpose_base name t (fun x=>
      let reduced := dreduce (fu) (fu r x) in
      T.change reduced;;
      cont x
    )
  | mNone => M.raise CVariablizeNoOccurrence
  end.

Definition destruct {A : Type} (n : A) : tactic :=
  mif M.is_var n then
    T.destruct n
  else
    cvariabilize_base n (FreshFromStr "dn") (fun x=>T.destruct x).

Program Definition destruct_eq {A} (t: A) : tactic :=
  cvariabilize_base t (FreshFromStr "v") (fun var=>
    T.cassert_base (FreshFromStr "eqn") (fun (eqnv : t = var)=>
      T.cmove_back eqnv (T.destruct var))
      |1> T.reflexivity
  ).

Module notations.

Notation "'uid' v" := (fun v:unit=>unit) (at level 0).
Notation "'variabilize' t 'as' v" :=
  (
    cvariabilize_base t (FreshFrom (uid v)) (fun _=>T.idtac)
  ) (at level 0, t at next level, v at next level).

End notations.
End CT.