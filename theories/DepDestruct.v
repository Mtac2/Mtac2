From MetaCoq
Require Export MetaCoq MCListUtils MCTactics.
Import MetaCoqNotations.
Import MCTacticsNotations.

Require Import Strings.String.

Require Import Lists.List.
Import ListNotations.

Inductive Bla : Prop := Ble.

Inductive Sort := SType | SProp.
Polymorphic Definition stype_of s := match s with SType => Type | SProp => Prop end.
Polymorphic Definition selem_of {s} (x : stype_of s) : Type :=
  match s return stype_of s -> Type with
  | SType => id
  | SProp => id
  end x.

Polymorphic Inductive ITele (sort : Sort) : Type :=
| iBase : stype_of sort -> ITele sort
| iTele : forall {T}, (T -> ITele sort) -> ITele sort.

Arguments iBase {_} _.
Arguments iTele {_ _} _.

Polymorphic Inductive CTele {sort} : ITele sort -> Type :=
| cBase : forall {T: stype_of sort}, selem_of T -> CTele (iBase T)
| cInst : forall {T f} (t:T), CTele (f t) -> CTele (iTele f)
| cProd : forall {T it}, (T -> CTele it) -> CTele it.

Arguments cBase {_ _} _.
Arguments cInst {_ _ _} _ _.
Arguments cProd {_ _ _} _.

Polymorphic Inductive ATele {sort} : ITele sort -> Type :=
| aBase : forall {T: stype_of sort}, ATele (iBase T)
| aTele : forall {T f} (a:T), ATele (f a) -> ATele (iTele f).

Arguments aBase {_ _}.
Arguments aTele {_ _ _} _ _.

Polymorphic Inductive RTele {isort} rsort : ITele isort -> Type :=
| rBase : forall {T : stype_of isort}, (selem_of T -> stype_of rsort) -> RTele rsort (iBase T)
| rTele : forall {T f}, (forall (t : T), RTele rsort (f t)) -> RTele rsort (iTele f).

Arguments rBase {_ _ _} _.
Arguments rTele {_ _ _ _} _.

Section ExampleReflect.

Inductive reflect (P :Prop) : bool -> Type :=
| RTrue : P -> reflect P true
| RFalse : ~P -> reflect P false.

Example reflect_reflect P : ITele SType := iTele (fun b=>@iBase SType (reflect P b)).

Example reflect_RTrue P : CTele (reflect_reflect P) :=
  cInst true (cProd (fun p=>@cBase SType _ (RTrue P p))).

Example reflect_RFalse P : CTele (reflect_reflect P) :=
  cInst _ (cProd (fun p=>cBase (sort:=SType) (RFalse P p))).

Example reflect_args P b : ATele (reflect_reflect P) :=
  aTele b aBase.

End ExampleReflect.


(*
Require Import Program.
Program Fixpoint abstract_goal (it : ITele) (args : ATele it) (G : Type) : M (RTele it) :=
  match it, args with
  | iBase t, aBase => ret (rBase G)
  | iTele f, aTele v args =>
    nu x,
      r <- abstract_goal (f x) args G;
      r <- abs x r;
      ret (rTele r)
  | _, _ => failwith "WHAAA??"
  end.
*)

Polymorphic Fixpoint ITele_App {sort} {it : ITele sort} (args : ATele it) : stype_of sort :=
  match args with
  | @aBase _ T => T
  | @aTele _ _ f v args =>
     ITele_App args
  end.

Example reflect_app P b := Eval compute in ITele_App (reflect_args P b).

Definition type_of {A} (x : A) := A.

(* We need to handle Prop (maybe) *)
Polymorphic Fixpoint abstract_goal {isort} {rsort} {it : ITele isort} (args : ATele it) (G : stype_of rsort) :
  selem_of (ITele_App args) -> M (RTele rsort it) :=
  match args with
  | @aBase _ T => fun t =>
    b <- is_var t;
    if b then
      r <- abs t G;
      ret (rBase r)
    else
      failwith "Argument t should be a variable"
  | @aTele _ _ f v args => fun t=>
      r <- abstract_goal args G t;
      b <- is_var v;
      if b then
        r <- abs (P:=fun v'=>RTele rsort (f v')) v r;
        ret (rTele r)
      else
        failwith "All indices need to be variables"
  end.

Polymorphic Fixpoint get_type_of_branch {isort} {rsort} {it : ITele isort} (ct : CTele it) : RTele rsort it -> stype_of rsort :=
  match ct in CTele it' return RTele _ it' -> _ with
  | @cBase _ T b =>
    fun rt : RTele _ (iBase T) =>
      match rt in RTele _ it'' return match it'' with iTele _ => True | iBase T' => selem_of T' -> _ end with
      | rTele _ => I
      | rBase f => f
      end b
  | cProd f =>
    match rsort as sort' return RTele sort' _ -> stype_of sort' with
    | SProp => fun rt=>forall x, get_type_of_branch (f x) rt : Prop
    | SType => fun rt=>forall x, get_type_of_branch (f x) rt
    end
  | @cInst _ T f v ct' =>
    let rec := get_type_of_branch ct' in
    fun rt : RTele _ (iTele f) =>
      match rt in RTele _ it'' return
            match it'' with
              | iBase _ => True
              | iTele f => forall v, (RTele _ (f v) -> _) -> _
            end
      with
        | rBase G => I
        | rTele rt' => fun v' rec' => rec' (rt' v')
      end v rec
  end.


(*
Polymorphic Definition get_type_of_branch {it : ITele} (rt : RTele it) (ct : CTele it) : Type.
Proof.
  induction ct as [T t|T f t ct' IH|T it f IH].
  - inversion rt.
    exact t1.
  - inversion rt.
    rewrite <- (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1) in IH.
    exact (IH (X t)).
  - exact (forall x, IH x rt).
Defined.
*)

Example bla P : RTele _ (reflect_reflect P) :=
  Eval simpl in rTele (fun b=>rBase (rsort:=SProp) (fun _=>P <-> b = true)).
Example bla_branch P := Eval simpl in get_type_of_branch (reflect_RTrue P) (bla P).

Definition new_destruct_goals {i : IndType} (g : RTele (ind_type i)) :=
  map (fun cs => get_type_of_branch g cs) (ind_constructors i).


Example bla_RTele P b :=
  Eval compute in eval (abstract_goal (reflect_args P b) ((P <-> b = true))).

Example bla_goals P b : list dyn :=
  Eval compute in
    map (fun cs => Dyn (get_type_of_branch (bla_RTele P b) cs))
        (reflect_RTrue P :: reflect_RFalse P :: nil).

Example reflectP_it : ITele :=
  iTele (fun P => iTele (fun b => iBase (reflect P b))).
Example reflectP_RTrue : CTele reflectP_it :=
  cProd (fun P => cProd (fun p => cInst P (cInst true (cBase (@RTrue P p))))).
Example reflectP_RFalse : CTele reflectP_it :=
  cProd (fun P => cProd (fun p => cInst P (cInst false (cBase (@RFalse P p))))).
Example reflectP_args P b : ATele reflectP_it :=
  aTele P (aTele b (aBase)).

Example blaP_RTele P b :=
  Eval compute in eval (abstract_goal (reflectP_args P b) ((P <-> b = true))).

Example blaP_goals P b : list dyn :=
  Eval compute in
    map (fun cs => Dyn (get_type_of_branch (blaP_RTele P b) cs))
        (reflectP_RTrue :: reflectP_RFalse :: nil).

Polymorphic Definition RTele_App : forall {it}, RTele it -> ATele it -> Type :=
  fix rec it r :=
    match r with
    | rBase t => fun _ => t
    | @rTele T f r =>
      let rec' := fun t => rec _ (r t) in
      fun a : ATele (iTele f) =>
        match a in ATele it' return
              match it' with
              | iBase _ => True
              | iTele f => _ -> _
              end
        with
        | aBase => I
        | aTele t a => fun rec => rec t a
        end rec'
    end
.

Goal True.
MProof.
  (fun g =>
  r <- destcase (match 3 with 0 => true | S _ => false end);
  print_term r;;
  cpose r (fun r=>idtac) g) : tactic.
  (fun g=>
  case <- makecase r;
  cpose case (fun y=>idtac) g) : tactic.
Abort.

Require Import Vector.

Goal forall n (v : t nat n), n = length (to_list v).

Goal forall P b, reflect P b -> P <-> b = true.
MProof.
  intros P b.
  (fun g=>
   G <- goal_type g;
   rG <- abstract_goal (reflectP_args P b) G;
   pose (rG := rG) g) : tactic.
  select (reflect _ _) (fun x=>
  case <- makecase {|
    case_val := x;
    case_type := RTele_App (
;
  cpose case (fun y=>idtac) g) : tactic.
Abort.


Definition new_destruct {A : Type} (n : A) : tactic := fun g=>
  b <- is_var n;
  ctx <- if b then hyps_except n else hypotheses;
  P <- Cevar (A->Type) ctx;
  let Pn := P n in
  gT <- goal_type g;
  unify_or_fail Pn gT;;
  l <- get_inductive A;
  l <- MCListUtils.mmap (fun d : dyn =>
    (* a constructor c has type (forall x, ... y, A) and we return
       (forall x, ... y, P (c x .. y)) *)
    t' <- copy_ctx P d;
    e <- evar t';
    ret {| elem := e |}) l;
  let c := {| case_ind := A;
              case_val := n;
              case_type := Pn;
              case_return := {| elem := P |};
              case_branches := l
           |} in
  d <- makecase c;
  d <- coerce (elem d);
  let d := hnf d in
  unify_or_fail (@TheGoal Pn d) g;;
  let l := hnf (List.map dyn_to_goal l) in
  ret l.
