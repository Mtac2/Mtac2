Require Export MetaCoq.MetaCoq.
Require Import MetaCoq.MCListUtils.
Import MetaCoqNotations.

Require Import Strings.String.

Require Import Lists.List.
Import ListNotations.



(* Polymorphic Inductive ITele : Type := *)
(* | iBase : forall {T}, T -> ITele *)
(* | iTele : forall {T}, (T -> ITele) -> ITele. *)

(* Polymorphic Inductive CTele : ITele -> Type := *)
(* | cBase : forall {T:Type}, T -> CTele (iBase T) *)
(* | cInst : forall {T f} (t:T), CTele (f t) -> CTele (iTele f) *)
(* | cProd : forall {T it}, (T -> CTele it) -> CTele it. *)

(* Polymorphic Inductive ATele : ITele -> Type := *)
(* | aBase : forall {T:Type}, ATele (iBase T) *)
(* | aTele : forall {T f} (a:T), ATele (f a) -> ATele (iTele f). *)

(* Polymorphic Inductive RTele : ITele -> Type := *)
(* | rBase : forall {T} {t:T}, Type -> RTele (iBase t) *)
(* | rTele : forall {T f}, (forall (t : T), RTele (f t)) -> RTele (iTele f). *)

Section ExampleReflect.

Inductive reflect (P :Prop) : bool -> Type :=
| RTrue : P -> reflect P true
| RFalse : ~P -> reflect P false.

Example reflect_reflect P := iTele (fun b=>iBase (reflect P b)).

Example reflect_RTrue P : CTele (reflect_reflect P) :=
  cInst true (cProd (fun p=>cBase (RTrue P p))).

Example reflect_RFalse P : CTele (reflect_reflect P) :=
  cInst _ (cProd (fun p=>cBase (RFalse P p))).

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

Polymorphic Fixpoint abstract_goal {it : ITele} (args : ATele it) (G : Type) : M (RTele it) :=
  match args with
  | aBase => ret (rBase G)
  | @aTele _ f v args =>
      r <- abstract_goal args G;
      b <- is_var v;
      if b then
        r <- abs v r;
        ret (rTele r)
      else
        failwith "All indices need to be variables"
  end.

Example bla P b := Eval hnf in eval (abstract_goal (reflect_args P b) (P <-> b = true)).

Definition outer_type_of (it : ITele) :=
  match it with
  | @iBase T _ => T
  | @iTele T _ => T
  end.

Require Import Program.

Polymorphic Fixpoint get_type_of_branch {it : ITele} (rt : RTele it) (ct : CTele it) : Type :=
  match ct in CTele it' return RTele it' -> Type with
  | cBase b => fun rt=>match rt with rBase g => g | rTele _ => False end
  | cProd f =>
    fun rt=>forall x, get_type_of_branch rt (f x)
  | @cInst T f v ct' =>
    let rec := fun rt => get_type_of_branch rt ct' in
    fun rt : RTele (iTele f) =>
      match rt in RTele it'' return
            match it'' with
              | iBase _ => True
              | iTele f => forall v, (RTele (f v) -> Type) -> Type
            end
      with
        | rBase G => I
        | @rTele T' f' rt' => fun v' rec' => rec' (rt' v')
      end v rec
  end rt.

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

Example bla_branch P b := Eval simpl in get_type_of_branch (bla P b) (reflect_RTrue P).

Definition new_destruct_goals {i : IndType} (g : RTele (ind_type i)) :=
  map (fun cs => get_type_of_branch g cs) (ind_constructors i).

Polymorphic Definition RTele_of_goal {it} (a : ATele it) (g : Type) : M (RTele it) :=
  (fix rec it g : ATele it -> M (RTele it) :=
    match it as it' return ATele it' -> M (RTele it') with
    | iBase t => fun _ => ret (rBase g)
    | @iTele T f =>
      fun a =>
        let
          rec
          (* : forall t : T, Type -> ATele (f t) -> M (RTele (f t)) *)
          := fun t => rec (f t)
        in
        (match a in ATele it'' return
               match it'' with
               | iBase _ => True
               | @iTele T' f =>
                 forall (rec : (forall t : T', Type -> ATele (f t) -> M (RTele (f t)))),
                   M (RTele (iTele f))
               end
         with
         | aBase => I
         | @aTele T f t a =>
           fun rec =>
             r <- (rec t g a) : M (RTele (f t));
               r' <- @abs T (fun t => RTele (f t)) t r;
               ret (rTele r')
         end)
          rec
    end) it g a.

Example bla_RTele P b :=
  Eval compute in eval (RTele_of_goal (reflect_args P b) ((P <-> b = true))).

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
  Eval compute in eval (RTele_of_goal (reflectP_args P b) ((P <-> b = true))).

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
