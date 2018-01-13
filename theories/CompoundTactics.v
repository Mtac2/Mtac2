From Mtac2 Require Import Base Tactics ImportedTactics Datatypes List Logic Abstract.

Import M. Import M.notations.
Import ListNotations.
Import ProdNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Module CT.

Definition simple_rewrite A {x y : A} (p : x = y) : tactic := fun g=>
  gT <- goal_type g;
  r <- abstract x gT;
  let reduced := dreduce (fu) (fu r y) in
  newG <- evar reduced;
  T.exact (eq_fu (r:=r) p newG) g;;
  ret [m: (m: tt, Goal newG)].

Import T.notations.
Definition cvariabilize_base {A} (t: A) name (cont: A -> tactic) : tactic :=
  gT <- T.goal_type;
  r <- abstract t gT;
  T.cpose_base name t (fun x=>
    let reduced := dreduce (fu) (fu r x) in
    T.change reduced;;
    cont x
  ).

Definition destruct {A : Type} (n : A) : tactic :=
  mif M.is_var n then
    T.destruct n
  else
    dn <- M.fresh_name "dn";
    cvariabilize_base n dn (fun x=>T.destruct x).

Program Definition destruct_eq {A} (t: A) : tactic :=
  vn <- M.fresh_name "v"; (* will be removed by destruct below *)
  cvariabilize_base t vn (fun var=>
    eqn <- M.fresh_name "eqn";
    T.cassert_base eqn (fun (eqnv : t = var)=>
      T.cmove_back eqnv (T.destruct var))
      |1> T.reflexivity
  ).

Module notations.

Notation "'uid' v" := (fun v:unit=>unit) (at level 0).
Notation "'variabilize' t 'as' v" :=
  (
    vn <- M.get_binder_name (uid v);
    cvariabilize_base t vn (fun _=>T.idtac)
  ) (at level 0, t at next level, v at next level).

End notations.
End CT.