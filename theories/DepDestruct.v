From MetaCoq
Require Export MetaCoq MCListUtils MCTactics.
Import MetaCoqNotations.
Import MCTacticsNotations.

Require Import Strings.String.

Require Import Lists.List.
Import ListNotations.

Inductive Bla : Prop := Ble.

Polymorphic Inductive Sort := SType | SProp.
Polymorphic Definition stype_of s := match s with SType => Type | SProp => Prop end.
Polymorphic Definition selem_of {s} (x : stype_of s) : Type :=
  match s return stype_of s -> Type with
  | SType => fun x => x
  | SProp => fun x => x
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

Polymorphic Definition type_of {A} (x : A) := A.

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

Polymorphic Definition ForAll {sort} {A} : (A -> stype_of sort) -> stype_of sort :=
  match sort with
  | SProp => fun F => forall (a : A), F a
  | SType => fun F => forall (a : A), F a
  end.

Polymorphic Definition Fun {sort} {A} :
  forall {F : A -> stype_of sort}, (forall a, selem_of (F a)) -> selem_of (ForAll F) :=
  match sort as sort' return
  forall {F : A -> stype_of sort'}, (forall a, selem_of (F a)) -> selem_of (ForAll F)
  with
  | SProp => fun _ f => f
  | SType => fun _ f => f
  end.

Polymorphic Fixpoint RTele_Type {isort} {it : ITele isort} {rsort} (rt : RTele rsort it) : Type :=
  match rt with
  | @rBase _ _ s r =>
    (forall (t : selem_of s), stype_of rsort) : Type
  | rTele rt => forall t, RTele_Type (rt t)
  end.

Polymorphic Fixpoint RTele_Fun {isort} {it : ITele isort} {rsort} (rt : RTele rsort it) : RTele_Type rt :=
  match rt with
  | rBase r => r
  | rTele rt => fun t => (RTele_Fun (rt t))
  end.

Example bla P : RTele _ (reflect_reflect P) :=
  Eval simpl in rTele (fun b=>rBase (rsort:=SProp) (fun _=>P <-> b = true)).
Example bla_branch P := Eval simpl in get_type_of_branch (reflect_RTrue P) (bla P).

Definition new_destruct_goals {isort} {it : ITele isort} {rsort} (g : RTele rsort it) :=
  map (fun ct => get_type_of_branch ct g).


Example bla_RTele P b (r : reflect P b) :=
  Eval compute in eval (abstract_goal (rsort := SProp) (reflect_args P b) ((P <-> b = true)) r).

Example bla_goals P b r : list dyn :=
  Eval compute in
    map (fun cs => Dyn (get_type_of_branch (rsort := SProp) cs (bla_RTele P b r)))
        (reflect_RTrue P :: reflect_RFalse P :: nil).

Example reflectP_it : ITele _ :=
  iTele (fun P => iTele (fun b => iBase (sort := SType) (reflect P b))).
Example reflectP_RTrue : CTele reflectP_it :=
  cProd (fun P => cProd (fun p => cInst P (cInst true (cBase (sort := SType) (@RTrue P p))))).
Example reflectP_RFalse : CTele reflectP_it :=
  cProd (fun P => cProd (fun p => cInst P (cInst false (cBase (sort := SType) (@RFalse P p))))).
Example reflectP_args P b : ATele reflectP_it :=
  aTele P (aTele b (aBase)).

Example blaP_RTele P b r :=
  Eval compute in eval (abstract_goal (rsort := SProp) (reflectP_args P b) ((P <-> b = true)) r).

Example blaP_goals P b r : list dyn :=
  Eval compute in
    map (fun cs => Dyn (get_type_of_branch cs (blaP_RTele P b r)))
        (reflectP_RFalse :: reflectP_RTrue :: nil).

Polymorphic Fixpoint RTele_App {isort rsort} {it : ITele isort} (rt : RTele rsort it) : forall (a : ATele it), selem_of (ITele_App a) -> stype_of rsort :=
  match rt in RTele _ it'
  with
  | @rBase _ _ T t =>
    fun (a : ATele (iBase T)) =>
      match a as a' in ATele it' return
            match it' with
            | iBase T' => (selem_of T' -> stype_of rsort) -> selem_of (ITele_App a') -> stype_of rsort
            | iTele f => True
            end
      with
      | aBase => fun f => f
      | aTele _ _ => I
      end t
  | @rTele _ _ _ f r =>
    let rec t := RTele_App (r t) in
    fun (a : ATele (iTele f)) =>
      match a as a' in ATele it' return
            match it' with
            | iBase _ => True
            | @iTele _ T' f => (forall (t:T') (a:ATele (f t)), selem_of (ITele_App a) -> _) -> selem_of (ITele_App a') -> stype_of rsort
            end
      with
      | aBase => I
      | aTele v a => fun rec => rec v a
      end rec
  end.


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

Goal forall P b, reflect P b -> P <-> b = true.
Proof.
  intros P b r.
  pose (rG := eval (abstract_goal (rsort := SType) (reflect_args P b) (P <-> b = true) r)).
  simpl in rG.
  assert (T : get_type_of_branch (reflect_RTrue P) rG).
  { now firstorder. }
  assert (F : get_type_of_branch (reflect_RFalse P) rG).
  { compute. firstorder. now discriminate. }
  pose (mc :=
          makecase {|
              case_val := r;
              case_type := RTele_App rG (reflect_args P b) r;
              case_return := Dyn (RTele_Fun rG);
              case_branches := (Dyn T) :: (Dyn F) :: nil
            |}).
  unfold blaP_goals in mc.
  compute in mc.
  pose (c := eval mc).
  exact (elem c).
Qed.


Section VectorExample.
Require Import Vector.
Goal forall n (v : t nat n), n = length (to_list v).
Proof.
  pose (it := iTele (fun n => @iBase SType (t nat n))).
  pose (vnil := (cInst 0 (@cBase SType _ (nil nat))) : CTele it).
  pose (vcons := (cProd (fun a => cProd (fun n => cProd (fun (v : t nat n) => cInst (S n) (@cBase SType _ (cons _ a _ v)))))) : CTele it).
  fix f 2.
  intros n v.
  pose (a := (aTele n (aBase)) : ATele it).
  pose (rt := eval (abstract_goal (rsort := SProp) a (n = length (to_list v)) v)).
  simpl in vcons, rt.
  assert (N : get_type_of_branch vnil rt).
  { now auto. }
  assert (C : get_type_of_branch vcons rt).
  { intros x k v'. cbv. f_equal. exact (f _ _). }
  pose (mc :=
          makecase {|
              case_val := v;
              case_type := RTele_App rt a v;
              case_return := Dyn (RTele_Fun rt);
              case_branches := Dyn N :: Dyn C :: List.nil
            |}
       ).
  simpl RTele_Fun in mc.
  (* pose (ma := (match v as v' in t _ k return k = length (to_list v') with *)
  (*              | nil _ => N *)
  (*              | cons _ a k v => C a k v *)
  (*              end)). *)
  (* pose (c' := eval (destcase ma)). *)
  (* unfold eval in c'. *)
  pose (c := eval mc).
  exact (elem c).
Qed.
End VectorExample.

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
