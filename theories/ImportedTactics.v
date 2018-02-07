From Mtac2 Require Import Base Tactics.
Require Import ssrmatching.ssrmatching.

Import M.notations.
Import T.notations.

Require Import Strings.String.
Require Import Mtac2.List.
Import Mtac2.List.ListNotations.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

Definition qualify s := String.append "Mtac2.ImportedTactics." s.

Ltac Mtrivial := trivial.
Definition trivial : tactic := T.ltac (qualify "Mtrivial") [m:].

Ltac Mdiscriminate := discriminate.
Definition discriminate : tactic := T.ltac (qualify "Mdiscriminate") [m:].

Ltac Mintuition := intuition.
Definition intuition : tactic := T.ltac (qualify "Mintuition") [m:].

Ltac Mauto := auto.
Definition auto : tactic := T.ltac (qualify "Mauto") [m:].

Ltac Meauto := eauto.
Definition eauto : tactic := T.ltac (qualify "Meauto") [m:].

Ltac Msubst := subst.
Definition subst : tactic := T.ltac (qualify "Msubst") [m:].

Ltac Mcontradiction := contradiction.
Definition contradiction : tactic := T.ltac (qualify "Mcontradiction") [m:].

Ltac Mtauto := tauto.
Definition tauto : tactic := T.ltac (qualify "Mtauto") [m:].

Ltac Munfold x := unfold x.
Definition unfold {A} (x: A) := T.ltac (qualify "Munfold") [m:Dyn x].

Ltac rrewrite1 a := rewrite a.
Ltac rrewrite2 a b := rewrite a, b.
Ltac rrewrite3 a b c := rewrite a, b, c.
Ltac rrewrite4 a b c d := rewrite a, b, c, d.
Ltac rrewrite5 a b c d e := rewrite a, b, c, d, e.

Definition compute_terminator {A} (l: mlist A) : M string :=
  match l with
  | [m:] => M.failwith "At least one required"
  | [m: _] => M.ret "1"
  | _ :m: [m:_] => M.ret "2"
  | _ :m: _ :m: [m:_] => M.ret "3"
  | _ :m: _ :m: _ :m: [m:_] => M.ret "4"
  | _ :m: _ :m: _ :m: _ :m: [m:_] => M.ret "5"
  | _ => M.failwith "Unsupported"
  end%string.

Ltac lrewrite1 a := rewrite <- a.
Ltac lrewrite2 a b := rewrite <- a, b.
Ltac lrewrite3 a b c := rewrite <- a, b, c.
Ltac lrewrite4 a b c d := rewrite <- a, b, c, d.
Ltac lrewrite5 a b c d e := rewrite <- a, b, c, d, e.

Inductive RewriteDirection := LeftRewrite | RightRewrite.

Definition trewrite (d : RewriteDirection) (args : mlist dyn) : tactic := fun g =>
  (ter <- compute_terminator args;
  let prefix := match d with LeftRewrite => "l"%string | RightRewrite => "r"%string end in
  let name := reduce RedNF (qualify (prefix++"rewrite"++ter)) in
  T.ltac name args g)%MC.

Notation "'rewrite' '->' x , .. , z" :=
  (trewrite RightRewrite (mcons (Dyn x) .. (mcons (Dyn z) [m:]) ..))
    (at level 0, x at next level, z at next level).
Notation "'rewrite' '<-' x , .. , z" :=
  (trewrite LeftRewrite (mcons (Dyn x) .. (mcons (Dyn z) [m:]) ..))
    (at level 0, x at next level, z at next level).
Notation "'rewrite' x , .. , z" :=
  (trewrite RightRewrite (mcons (Dyn x) .. (mcons (Dyn z) [m:]) ..))
    (at level 0, x at next level, z at next level).

Ltac Melim h := elim h.
Definition elim {A} (x:A) : tactic :=
  T.ltac (qualify "Melim") [m: Dyn x].

Ltac Minduction v := induction v.
Definition induction {A} (x:A) : tactic :=
  T.ltac (qualify "Minduction") [m: Dyn x].

Definition injection {A} (x: A) : tactic :=
  T.ltac ("Coq.Init.Notations.injection") [m:Dyn x].

Ltac Minversion H := inversion H.
Definition inversion {A} (x: A) : tactic :=
  T.ltac (qualify "Minversion") [m:Dyn x].

Ltac Mtypeclasses_eauto := typeclasses eauto.
Definition typeclasses_eauto : tactic :=
  T.ltac (qualify "Mtypeclasses_eauto") [m:].

Ltac Mapply x := apply x.
Definition ltac_apply {A} (x:A) := T.ltac (qualify "Mapply") [m:Dyn x].

Ltac Mdestruct x := destruct x.
Definition ltac_destruct {A} (x:A) := T.ltac (qualify "Mdestruct") [m:Dyn x].

Ltac Mssrpattern p := ssrpattern p.
Definition ssrpattern {A} (x:A) := T.ltac "Mssrpattern" [m: Dyn x].

(** We wrap "pattern" in two functions: one that abstracts a term from a type
    (the usual use of pattern), and another one which abstracts a term from
    another term. For the latter, we need to wrap the term in a type to make
    it work. *)
(** NOTE that it won't work if there are evars inside *)
Ltac Mpattern n := pattern n.

Require Import Mtac2.Sorts.
Import Sorts. Import ProdNotations.
Import M.notations.
Definition abstract_from_sort {s:Sort} {A} (x:A) (B:s) : M (A -> s) :=
  t <- M.evar B;
  gs <- T.ltac (qualify "Mpattern") [m: Dyn x] (Goal s t);
  mmatch gs with
  | [? (f:A->s) t] [m: (m: tt, @Goal s (f x) t)] => M.ret f
  end.
Definition abstract_from_type := @abstract_from_sort SType.

Definition wrapper {A} (t: A) : Prop. exact False. Qed.

(* FIXME: change mmatchs with decompose_app *)
Definition abstract_from_term {A B} (x:A) (t : B) : M (A -> B) :=
  wt <- M.evar (wrapper t);
  gs <- T.ltac (qualify "Mpattern") [m: Dyn x] (Goal SProp wt);
  mmatch gs with
  | [? (f:A->Prop) t] [m: (m: tt, @Goal SProp (f x) t)] =>
    name <- M.fresh_binder_name f;
    M.nu name mNone (fun a:A=>
      let fa := reduce (RedOneStep [rl:RedBeta]) (f a) in
      mmatch fa return M (A -> B) with
      | [? (body:B)] wrapper body =n>
        M.abs_fun a body
      end
    )
  end.
