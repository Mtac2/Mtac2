Require Import Strings.String.
From MetaCoq Require Export Mtac2.
Require Import MetaCoq.ListUtils.
Require Import Lists.List.
Import MtacNotations.
Import ListNotations.

Require Import Strings.String.

Local Set Universe Polymorphism.

Notation "'dreduce' ( l1 , .. , ln )" := (reduce (RedStrong [RedBeta;RedFix;RedMatch;RedDeltaOnly (Dyn (@l1) :: .. (Dyn (@ln) :: nil) ..)])) (at level 0).

Definition CantCoerce : Exception. exact exception. Qed.

(** [coerce x] coreces element [x] of type [A] into
    an element of type [B], assuming [A] and [B] are
    unifiable. It raises [CantCoerce] if it fails. *)
Definition coerce {A B : Type} (x : A) : M B :=
  oH <- munify A B UniCoq;
  match oH with
  | Some H => match H with eq_refl => ret x end
  | _ => raise CantCoerce
  end.

(** The type for tactics *)
Definition tactic := goal -> M (list goal).

(** Executing a tactic in Mtac. It is called by
    the MProof environment. *)
Definition run_tac {P} (t : tactic) : M P :=
  e <- evar P;
  t (Goal e);;
  ret e.


Definition NotAGoal : Exception. exact exception. Qed.
(** [goal_type g] extracts the type of the goal or raises [NotAGoal]
    if [g] is not [Goal]. *)
Definition goal_type (g : goal) : M Type :=
  match g with
    | @Goal A _ => ret A
    | _ => raise NotAGoal
  end.

(** Convertion functions from [dyn] to [goal]. *)
Definition dyn_to_goal (d : dyn) : goal :=
  match d with
  | Dyn x => Goal x
  end.

Definition goal_to_dyn : goal -> M dyn := fun g =>
  match g with
  | Goal d => ret (Dyn d)
  | _ => raise NotAGoal
  end.

(** no-op tactic *)
Definition idtac : tactic := fun g => ret [g].

(** fail tactic *)
Definition fail (e : Exception) : tactic := fun g=>raise e.

(** Unifies [x] with [y] and raises [NotUnifiable] if it they
    are not unifiable. *)
Definition unify_or_fail {A} (x y : A) : M (x = y) :=
  oeq <- munify x y UniCoq;
  match oeq with
  | None => raise (NotUnifiable x y)
  | Some eq => ret eq
  end.

(** Unifies [x] with [y] using cumulativity and raises
    [NotCumul] if it they
    are not unifiable. *)
Definition NotCumul {A B} (x: A) (y: B) : Exception. exact exception. Qed.
Definition cumul_or_fail {A B} (x: A) (y: B) : M unit :=
  b <- munify_cumul x y UniCoq;
  if b then ret tt else raise (NotCumul x y).

Definition exact {A} (x:A) : tactic := fun g=>
  match g with
  | Goal g => cumul_or_fail x g;; ret nil
  | _ => raise NotAGoal
  end.

Definition try (t:tactic) : tactic := fun g=>
  mtry t g with _ => ret ( g :: nil) end.

Definition or (t u : tactic) : tactic := fun g=>
  mtry t g with _ => u g end.

(** [close_goals x l] takes the list of goals [l] and appends
    hypothesis [x] to each of them. *)
Definition close_goals {A} (x:A) : list goal -> M (list goal) :=
  mmap (fun g'=>r <- abs_fun x g'; ret (@AHyp A None r)).

(** [let_close_goals x l] takes the list of goals [l] and appends
    hypothesis [x] with its definition to each of them (it assumes it is defined). *)
Definition let_close_goals {A} (x: A) : list goal -> M (list goal) :=
  let t := rone_step x in (* to obtain x's definition *)
  mmap (fun g':goal=>
          r <- abs_fun x g';
          ret (@AHyp A (Some t) r)
       ).

Definition NotAnEvar {A} (x: A) : Exception. exact exception. Qed.
Definition CantInstantiate {A} (x t: A) : Exception. exact exception. Qed.

(** [decompose x] decomposes value [x] into a head and a spine of
    arguments. For instance, [decompose (3 + 3)] returns
    [(Dyn add, [Dyn 3; Dyn 3])] *)
Definition decompose {A} (x: A) :=
  (mfix2 f (d : dyn) (args: list dyn) : M (dyn * list dyn)%type :=
    mmatch d with
    | [? A B (t1: A -> B) t2] Dyn (t1 t2) => f (Dyn t1) (Dyn t2 :: args)
    | [? A B (t1: forall x:A, B x) t2] Dyn (t1 t2) => f (Dyn t1) (Dyn t2 :: args)
    | _ => ret (d, args)
    end) (Dyn x) [].

(** [instantiate x t] tries to instantiate meta-variable [x] with [t].
    It fails with [NotAnEvar] if [x] is not a meta-variable (applied to a spine), or
    [CantInstantiate] if it fails to find a suitable instantiation. [t] is beta-reduced
    to avoid false dependencies. *)
Definition instantiate {A} (x t : A) : M unit :=
  k <- decompose x;
  let (h, _) := k in
  let h := rcbv h.(elem) in
  b <- is_evar h;
  let t := reduce (RedWhd [RedBeta]) t in
  if b then
    r <- munify x t UniEvarconv;
    match r with
    | Some _ => ret tt
    | _ => raise (CantInstantiate x t)
    end
  else
    raise (NotAnEvar h).

Definition NotAProduct : Exception. exact exception. Qed.

(** [intro_base n t] introduces variable or definition named [n]
    in the context and executes [t n].
    Raises [NotAProduct] if the goal is not a product or a let-binding. *)
Definition intro_base {A} (var : string) (t: A->tactic) : tactic := fun g=>
  mmatch g return M list goal with
  | [? B (def: B) P e] @Goal (let x := def in P x) e =n>
    (* normal match will not instantiate meta-variables from the scrutinee, so we do the inification here*)
    eqBA <- unify_or_fail B A;
    nu var (Some def) (fun x=>
      let Px := reduce (RedWhd [RedBeta]) (P x) in
      e' <- evar Px;
      nG <- abs_let (P:=P) x def e';
      exact nG g;;
      let x := reduce (RedWhd [RedMatch]) (match eqBA with eq_refl => x end) in
      t x (Goal e') >>= let_close_goals x)

  | [? P e] @Goal (forall x:A, P x) e =u>
    nu var None (fun x=>
      let Px := reduce (RedWhd [RedBeta]) (P x) in
      e' <- evar Px;
      nG <- abs_fun (P:=P) x e';
      exact nG g;;
      t x (Goal e') >>= close_goals x)
  | _ => raise NotAProduct
  end.

Definition intro_cont {A} (t: A->tactic) : tactic := fun g=>
  n <- get_binder_name t;
  intro_base n t g.

(** Given a name of a variable, it introduces it in the context *)
Definition intro_simpl (var: string) : tactic := fun g=>
  A <- evar Type;
  intro_base var (fun _:A=>idtac) g.

(** Returns if a goal is open, i.e., a meta-variable. *)
Fixpoint is_open (g : goal) : M bool :=
  match g with
  | Goal e => is_evar e
  | @AHyp C _ f =>
    x <- fresh_binder_name f;
    (* we get the name in order to avoid inserting existing names
      (nu will raise an exception otherwise) *)
    nu x None (fun x : C=>is_open (f x))
  end.

(** removes the goals that were solved *)
Definition filter_goals : list goal -> M (list goal) := mfilter is_open.

(** [open_and_apply t] is a tactic that "opens" the current goal
    (pushes all the hypotheses in the context) and applies tactic [t]
    to the so-opened goal. The result is "closed" back. *)
Definition open_and_apply (t : tactic) : tactic :=
  fix open g :=
    match g return M _ with
    | Goal _ => t g
    | @AHyp C None f =>
      x <- fresh_binder_name f;
      nu x None (fun x : C=>
        open (f x) >>= close_goals x)
    | @AHyp C (Some t) f =>
      x <- fresh_binder_name f;
      nu x (Some t) (fun x : C=>
        open (f x) >>= let_close_goals x)
    end.

(** given a string s it appends a marker to avoid collition with user
    provided names *)
Definition anonymize (s : string) : M string :=
  let s' := rcbv ("__"++s) in
  ret s'.

(** Introduces an anonymous name based on a binder *)
Definition intro_anonymous {A} (T: A) f (g: goal) : M goal :=
  name <- get_binder_name T;
  axn <- anonymize name;
  axn <- f axn;
  intro_simpl axn g >>= hd_exception.

(** Introduces all hypotheses. Does not fail if there are 0. *)
Definition intros_all : tactic :=
  mfix1 f (g : goal) : M (list goal) :=
    open_and_apply (fun g =>
      match g return M (list goal) with
      | @Goal T e =>
        mtry
          intro_anonymous T mid g >>= f
        with WrongTerm =>
          ret [g]
        | NotAProduct =>
          ret [g]
        | [? s] NameExistsInContext s =>
          intro_anonymous T fresh_name g >>= f
        end
      | _ => raise NotAGoal
      end) g.

(** Introduces up to n binders. Throws [NotAProduct] if there
    aren't enough products in the goal.  *)
Definition introsn : nat -> tactic :=
  mfix2 f (n : nat) (g : goal) : M (list goal) :=
    open_and_apply (fun g =>
      match (n, g) with
      | (0, g) => ret [g]
      | (S n', @Goal T e) =>
        mtry
          intro_anonymous T mid g >>= f n'
        with WrongTerm => raise NotAProduct
        | [? s] NameExistsInContext s =>
          intro_anonymous T fresh_name g >>= f n'
        end
      | (_, _) => failwith "Should never get here"
      end) g.

(** Applies reflexivity *)
Definition prim_reflexivity : tactic := fun g=>
  A <- evar Type;
  x <- evar A;
  unify_or_fail g (Goal (eq_refl x));; ret nil.

(** Fist introduces the hypotheses and then applies reflexivity *)
Definition reflexivity : tactic := fun g=>
  l <- intros_all g;
  g <- hd_exception l;
  open_and_apply prim_reflexivity g.

Definition NotSameSize (l : list tactic) (l' : list goal) : Exception. exact exception. Qed.
Fixpoint gmap (funs : list tactic) (ass : list goal) : M (list (list goal)) :=
  match funs, ass with
  | nil, nil => ret nil
  | f::funs', g::ass' =>
    fa <- open_and_apply f g;
    rest <- gmap funs' ass';
    ret (fa :: rest)
  | l, l' => raise (NotSameSize l l')
  end.

Definition is_empty {A} (l: list A) :=
  match l with [] => true | _ => false end.

Definition NoGoalsLeft : Exception. exact exception. Qed.

Definition tactic_tactics (t:tactic) (l:list tactic) : tactic := fun g=>
  l' <- t g;
  ls <- gmap l l';
  let res := dreduce (concat, List.app) (concat ls) in
  ret res.

Definition tactic_tactic (t u:tactic) : tactic := fun g=>
  l <- t g;
  if is_empty l then
    raise NoGoalsLeft
  else
    r <- mmap (open_and_apply u) l;
    let res := dreduce (concat, @List.app) (concat r) in
    ret res.

(* Polymorphic CS are broken *)
Monomorphic Structure semicolon (left_type compose_type : Type) := SemiColon {
  right_type : Type;
  the_value : left_type -> right_type -> compose_type
}.
Arguments SemiColon {_ _ _} _.
Arguments the_value {_ _ _}.

Monomorphic Canonical Structure semicolon_tactic_tactics :=
  SemiColon tactic_tactics.

Monomorphic Canonical Structure semicolon_tactic_tactic :=
  SemiColon tactic_tactic.

(** Overloaded binding *)
(* Polymorphic CS are broken *)
Monomorphic Structure binding  (left_type middle_type compose_type : Type) :=
  Binding {
      bright_type : Type;
      the_bvalue : left_type -> (middle_type -> bright_type) -> compose_type }.
Arguments Binding {_ _ _ _} _.
Arguments the_bvalue {_ _ _ _}.

Monomorphic Canonical Structure binding_mtac A B :=
  Binding (@bind A B).

Monomorphic Definition mtac_tactic {A} (t: M A) (u: A -> tactic) : tactic :=
  fun g=> x <- t; u x g.

Monomorphic Canonical Structure binding_tactic A :=
  Binding (@mtac_tactic A).

Definition SomethingNotRight {A} (t : A) : Exception. exact exception. Qed.
Definition copy_ctx {A} (B : A -> Type) :=
  mfix1 rec (d : dyn) : M Type :=
    mmatch d with
    | [? c : A] Dyn c =>
        let Bc := reduce (RedWhd [RedBeta]) (B c) in
        ret Bc
    | [? C (D : C -> Type) (c : forall y:C, D y)] Dyn c =>
        n <- fresh_binder_name c;
        nu n None (fun y=>
          r <- rec (Dyn (c y));
          abs_prod y r)
    | [? C D (c : C->D)] Dyn c =>
        n <- fresh_binder_name c;
        nu n None (fun y=>
          r <- rec (Dyn (c y));
          abs_prod y r)
    | _ => print_term A;; raise (SomethingNotRight d)
    end.

Definition hyps_except {A} (x : A) : M (list Hyp) :=
  l <- hypotheses;
  mfilter (fun y=>mmatch y with
    | [? b] ahyp x b => ret false
    | _ => ret true
    end) l.

Definition find_hyp_index {A} (x : A) : M (option nat) :=
  l <- hypotheses;
  mindex_of (fun y=>mmatch y with
    | [? b] ahyp x b => ret true
    | _ => ret false
    end) l.

Definition type_of {A} (x:A) : Type := A.

Fixpoint but_last {A} (l : list A) : list A :=
  match l with
  | [] => []
  | [a] => []
  | (a :: ls) => a :: but_last ls
  end.

(** Generalizes a goal given a certain hypothesis [x]. It does not
    remove [x] from the goal. *)
Definition generalize {A} (x:A) : tactic := fun g=>
  P <- goal_type g;
  aP <- abs_prod x P; (* aP = (forall x:A, P) *)
  e <- evar aP;
  mmatch aP with
  | [? Q : A -> Type] (forall z:A, Q z) =n> [H]
    let e' := rcbv match H in _ = Q return Q with
      | eq_refl _ => e
      end
    in
    exact (e' x) g;;
    ret [Goal e]
  | _ => failwith "generalize: should never happen"
  end.

(** Clear hypothesis [x] and continues the execution on [cont] *)
Definition cclear {A} (x:A) (cont: tactic) : tactic := fun g=>
  gT <- goal_type g;
  r <- Mtac2.remove x (
    e <- evar gT;
    l <- cont (Goal e);
    ret (e, l) );
  let (e, l) := r in
  exact e g;;
  ret l.

Definition clear {A} (x:A) : tactic := cclear x idtac.

Definition cprint {A} (s: string) (c: A) : M unit :=
  x <- pretty_print c;
  let s := reduce RedNF (s++x)%string in
  print s.

Definition destruct {A : Type} (n : A) : tactic := fun g=>
  let A := rhnf A in
  b <- let n := rcbv n in is_var n;
  ctx <- if b then hyps_except n else hypotheses;
  P <- Cevar (A->Type) ctx;
  let Pn := P n in
  gT <- goal_type g;
  unify_or_fail Pn gT;;
  l <- constrs A;
  l <- mmap (fun d : dyn =>
    (* a constructor c has type (forall x, ... y, A) and we return
       (forall x, ... y, P (c x .. y)) *)
    t' <- copy_ctx P d;
    e <- Cevar t' ctx;
    ret {| elem := e |}) (snd l);
  let c := {| case_ind := A;
              case_val := n;
              case_return := {| elem := P |};
              case_branches := l
           |} in
  case <- makecase c;
  case <- unfold_projection (elem case);
  exact case g;;
  let res := dreduce (List.map, dyn_to_goal) (List.map dyn_to_goal l) in
  ret res.

(** Destructs the n-th hypotheses in the goal (counting from 0) *)
Definition destructn (n : nat) : tactic := fun g=>
  goals <- introsn (S n) g;
  goal <- hd_exception goals;
  open_and_apply (fun g=>
    hyps <- hypotheses;
    var <- hd_exception hyps;
    let (_, var, _) := var in
    destruct var g
  ) goal.

Local Obligation Tactic := idtac.

Definition CantApply {T1 T2} (x:T1) (y:T2) : Exception. exact exception. Qed.

Definition apply {T} (c : T) : tactic := fun g=>
  match g with Goal eg =>
    (mfix1 app (d : dyn) : M (list goal) :=
      let (_, el) := d in
      mif munify_cumul el eg UniCoq then
        ret []
      else
        mmatch d return M (list goal) with
        | [? T1 T2 f] @Dyn (forall x:T1, T2 x) f =>
          e <- evar T1;
          r <- app (Dyn (f e));
          mif is_evar e then
            ret (Goal e :: r)
          else ret r
        | _ =>
          gT <- goal_type g;
          raise (CantApply T gT)
        end) (Dyn c)
  | _ => raise NotAGoal
  end.

Definition change_hyp {P Q} (H: P) (newH: Q) : tactic := fun g=>
  gT <- goal_type g;
  n <- get_binder_name H;
  f <- Mtac2.remove H (
    nu n None (fun H': Q =>
      e <- evar gT;
      a <- abs_fun H' e;
      b <- abs_fun H' (Goal e);
      ret (a, b)));
  let (f, g') := f in
  unify_or_fail (Goal (f newH)) g;;
  ret [AHyp None g'].

Definition apply_in {P Q} (c: P -> Q) (H: P) : tactic :=
  change_hyp H (c H).

Definition transitivity {B : Type} (y : B) : tactic :=
  apply (fun x => @eq_trans B x y).

Definition symmetry : tactic :=
  apply eq_sym.

Definition exfalso : tactic :=
  apply False_ind.

Definition CantFindConstructor : Exception. exact exception. Qed.
Definition ConstructorsStartsFrom1 : Exception. exact exception. Qed.

Definition constructor (n : nat) : tactic := fun g=>
  A <- goal_type g;
  match n with
  | 0 => raise ConstructorsStartsFrom1
  | S n =>
      l <- constrs A;
      match nth_error (snd l) n with
        | Some (@Dyn A x) => apply x g
        | None => fail CantFindConstructor g
      end
  end.

Definition Not1Constructor : Exception. exact exception. Qed.

Definition split : tactic := fun g=>
  A <- goal_type g;
  l <- constrs A;
  match snd l with
  | [_] => constructor 1 g
  | _ => raise Not1Constructor
  end.

Definition Not2Constructor : Exception. exact exception. Qed.

Definition left : tactic := fun g=>
  A <- goal_type g;
  l <- constrs A;
  match snd l with
  | [Dyn x; _] => apply x g
  | _ => raise Not2Constructor
  end.

Definition right : tactic := fun g=>
  A <- goal_type g;
  l <- constrs A;
  match snd l with
  | [_; Dyn x] => apply x g
  | _ => raise Not2Constructor
  end.

Monomorphic Inductive goal_pattern : Type :=
| gbase : forall {A}, A -> tactic -> goal_pattern
| gtele : forall {C}, (C -> goal_pattern) -> goal_pattern.

Definition DoesNotMatchGoal : Exception. exact exception. Qed.

Fixpoint match_goal' (p : goal_pattern) : list Hyp -> list Hyp -> tactic :=
  fix go l1 l2 g :=
  match p, l2 with
  | gbase P t, _ =>
    gT <- goal_type g;
    mif munify_cumul P gT UniCoq then t g
    else raise DoesNotMatchGoal
  | @gtele C f, (@ahyp A a d :: l2') =>
    oeqCA <- munify C A UniCoq;
    match oeqCA with
    | Some eqCA =>
      let a' := rcbv match eq_sym eqCA with eq_refl => a end in
      mtry match_goal' (f a') [] (List.rev_append l1 l2')%list g
      with DoesNotMatchGoal =>
        go (ahyp a d :: l1) l2' g
      end
    | None => go (ahyp a d :: l1) l2' g end
  | _, _ => raise DoesNotMatchGoal
  end.

Definition match_goal (p : goal_pattern) : tactic := fun g=>
  r <- hypotheses; match_goal' p [] (List.rev' r) g.

Definition ltac (t : string) (args : list dyn) : tactic := fun g=>
  d <- goal_to_dyn g;
  let (ty, el) := d in
  v <- @call_ltac ty t args;
  let (v, l) := v in
  unify_or_fail v el;;
  b <- is_evar v;
  if b then
    ret [Goal v] (* it wasn't solved *)
  else
    ret l.

Definition option_to_bool {A} (ox : option A) :=
  match ox with Some _ => true | _ => false end.

Definition destruct_all (T : Type) : tactic := fun g=>
  l <- hypotheses;
  l <- mfilter (fun h:Hyp=>
    let (Th, _, _) := h in
    r <- munify Th T UniCoq;
    ret (option_to_bool r)) l;
  (fix f (l : list Hyp) : tactic :=
    match l with
    | [] => idtac
    | (ahyp x _ :: l) => tactic_tactic (destruct x) (f l)
    end) l g.

Definition treduce (r : Reduction) : tactic := fun g=>
  T <- goal_type g;
  let T := reduce r T in
  e <- evar T;
  oeq <- munify g (Goal e) UniMatch;
  match oeq with
  | Some _ => ret [Goal e]
  | _ => failwith "It should never fail here"
  end.

Definition NotThatType : Exception. exact exception. Qed.
Definition typed_intro (T : Type) : tactic := fun g=>
  U <- goal_type g;
  mmatch U with
  | [? P:T->Type] forall x:T, P x =>
    xn <- get_binder_name U;
    intro_simpl xn g
  | _ => raise NotThatType
  end.

Definition typed_intros (T : Type) : tactic := fun g=>
  (mfix1 f (g : goal) : M _ :=
    mtry
      (tactic_tactic (typed_intro T) f) g
    with NotThatType =>
      idtac g
    end) g.

Definition cpose_base {A} (name : string) (t: A) (cont: A -> tactic) : tactic := fun g=>
  nu name (Some t) (fun x=>
    gT <- goal_type g;
    r <- evar gT;
    value <- abs_let x t r;
    exact value g;;
    cont x (Goal r) >>= let_close_goals x).

Definition cpose {A} (t: A) (cont: A -> tactic) : tactic := fun g=>
  n <- get_binder_name cont;
  cpose_base n t cont g.

Definition cassert_base {A} (name : string) (cont: A -> tactic) : tactic := fun g=>
  a <- evar A; (* [a] will be the goal to solve [A] *)
  nu name None (fun x=>
    gT <- goal_type g;
    r <- evar gT; (* The new goal now referring to n *)
    value <- abs_fun x r;
    exact (value a) g;; (* instantiate the old goal with the new one *)
    v <- cont x (Goal r) >>= close_goals x;
    ret (Goal a :: v)). (* append the goal for a to the top of the goals *)

Definition cassert {A} (cont: A -> tactic) : tactic := fun g=>
  n <- get_binder_name cont;
  cassert_base n cont g.

(* performs simpl in each hypothesis and in the goal *)
Definition simpl_in_all : tactic := fun g=>
  l <- hypotheses;
  l <- mfold_right (fun (hyp : Hyp) hyps =>
    let (A, x, ot) := hyp in
    let A := rsimpl A in
    ret (@ahyp A x ot :: hyps)
  ) [] l;
  T <- goal_type g;
  let T := rsimpl T in
  e <- Cevar T l; (* create the new goal in the new context *)
  (* we need normal unification since g might be a compound value *)
  oeq <- munify g (Goal e) UniCoq;
  match oeq with
  | Some (eq_refl _) => ret [Goal e]
  | _ => raise exception (* should never happen *)
  end.

Definition reduce_in r {P} (H: P) : tactic := fun g=>
  l <- hypotheses;
  l' <- mmap (fun hyp : Hyp =>
    let (T, v, def) := hyp in
    mif munify_cumul H v UniMatchNoRed then
     let T' := reduce r T in ret (@ahyp T' v def)
    else ret hyp) l;
  gT <- goal_type g;
  e <- Cevar gT l';
  oeq <- munify (Goal e) g UniCoq;
  match oeq with
  | Some (eq_refl _) => ret [Goal e]
  | _ => raise exception (* should never happen *)
  end.

Definition simpl_in {P} (H: P) : tactic :=
  reduce_in RedSimpl H.

(** exists tactic *)
Definition mexists {A} (x: A) : tactic := fun g=>
  P <- evar _;
  e <- evar _;
  oeq <- munify g (Goal (@ex_intro _ P x e)) UniCoq;
  match oeq with
  | Some (eq_refl _) => ret [Goal e]
  | _ => raise (NotUnifiable g (Goal (@ex_intro _ P x e)))
  end.

(** Printing of a goal *)
Require Import Strings.String.

Definition print_hypothesis (a:Hyp) : M unit :=
  let (A, x, ot) := a in
  sA <- pretty_print A;
  sx <- pretty_print x;
  match ot with
  | Some t =>
    st <- pretty_print t;
    print (sx ++ " := " ++ st ++ " : " ++ sA)
  | None => print (sx ++ " : " ++ sA)
  end.

Definition print_hypotheses : M unit :=
  l <- hypotheses;
  let l := rev' l in
  miterate print_hypothesis l.

Definition print_goal : tactic := fun g=>
  let repeat c := (fix repeat s n :=
    match n with
    | 0 => s
    | S n => repeat (c++s)%string n
    end) "" in
  G <- goal_type g;
  sg <- pretty_print G;
  let sep := repeat "=" 20 in
  print_hypotheses;;
  print sep;;
  print sg;;
  idtac g.

(** [n_etas n f] takes a function f with type [forall x1, ..., xn, T]
    and returns its eta-expansion: [fun x1, ..., xn=>f x1 .. xn].
    Raises [NotAProduct] if there aren't that many absractions. *)
Definition n_etas (n : nat) {A} (f:A) : M A :=
  (fix loop (n : nat) (d : dyn) : M (type d) :=
    match n with
    | 0 =>
      (* we remove the wrapper of the element in [d] *)
      unfold_projection (elem d)
    | S n' =>
       mmatch d with
       | [? B (T:B->Type) f] @Dyn (forall x:B, T x) f =>
         ty <- unfold_projection (type d);
         name <- get_binder_name ty;
         nu name None (fun x:B =>
           loop n' (Dyn (f x)) >>= abs_fun x
         )
       | _ => raise NotAProduct
       end
    end) n (Dyn f).


Require Import NArith.BinNat.
Require Import NArith.BinNatDef.

(** [fix_tac f n] is like Coq's [fix] tactic: it generates a fixpoint
    with a new goal as body, containing a variable named [f] with
    the current goal as type. The goal is expected to have at least
    [n] products. *)
Definition fix_tac (f : string) (n : N) : tactic := fun g=>
  gT <- goal_type g;
  r <- nu f None (fun f:gT=>
    (* We introduce the recursive definition f and create the new
       goal having it. *)
    new_goal <- evar gT;
    (* We need to enclose the body with n-abstractions as
     required by the fix operator. *)
    fixp <- n_etas (N.to_nat n) new_goal;
    fixp <- abs_fix f fixp n;
    (* fixp is now the fixpoint with the evar as body *)
    (* The new goal is enclosed with the definition of f *)
    new_goal <- abs_fun f (Goal new_goal);
    ret (fixp, AHyp None new_goal)
  );
  let (f, new_goal) := r in
  exact f g;;
  ret [new_goal].

(** [repeat t] applies tactic [t] to the goal several times
    (it should only generate at most 1 subgoal), until no
    changes or no goal is left. *)
Definition repeat (t : tactic) : tactic := fun g=>
  (mfix1 f (g : goal) : M (list goal) :=
    r <- try t g; (* if it fails, the execution will stop below *)
    match r with
    | [] => ret []
    | [g'] =>
      mmatch g with
      | g' => ret [g] (* the goal is the same, return *)
      | _ => f g'
      end
    | _ => print_term r;; failwith "The tactic generated more than a goal"
    end) g.

Definition is_prop_or_type (d: dyn) : M bool :=
  mmatch d with
  | Dyn Prop => ret true
  | Dyn Type => ret true
  | _ => ret false
  end.

Require Import Bool.Bool.

Definition map_term (f : forall d:dyn, M d.(type)) :=
  mfix1 rec (d : dyn) : M d.(type) :=
    let (ty, el) := d in
    mmatch d as d return M d.(type) with
    | [? B A (b: B) (a: B -> A)] Dyn (a b) =n>
      d1 <- rec (Dyn a);
      d2 <- rec (Dyn b);
      ret (d1 d2)
    | [? B (A: B -> Type) (a: forall x, A x)] Dyn (fun x:B=>a x) =n>
      n <- get_binder_name el;
      nu n None (fun x:B=>
        d1 <- rec (Dyn (a x));
        abs_fun x d1)
    | [? B (A: B -> Type) a] Dyn (forall x:B, a x) =n>
      n <- get_binder_name el;
      nu n None (fun x:B=>
        d1 <- rec (Dyn (a x));
        abs_prod x d1)
    | [? d'] d' =n> f d'
    end.

Definition unfold_slow {A} (x: A) : tactic := fun g=>
  let def := rone_step x in
  gT <- goal_type g;
  gT' <- map_term (fun d=>
   let (ty, el) := d in
   mmatch d as d return M d.(type) with
   | Dyn x =n> ret def
   | [? A (d': A)] Dyn d' =n> ret d'
   end) (Dyn gT);
  e <- evar gT';
  exact e g;;
  ret [Goal e].

Definition unfold {A} (x: A) : tactic := fun g=>
  gT <- goal_type g;
  let gT' := dreduce (x) gT in
  ng <- evar gT';
  exact ng g;;
  ret [Goal ng].

Definition unfold_in {A B} (x: A) (h: B) : tactic :=
  reduce_in (RedStrong [RedBeta; RedMatch; RedFix; RedDeltaOnly [Dyn x]]) h.

Monomorphic Fixpoint intros_simpl (l: list string) : tactic :=
  match l with
  | [] => idtac
  | (n :: l) => tactic_tactic (intro_simpl n) (intros_simpl l)
  end.

Monomorphic Fixpoint name_pattern (l: list (list string)) : list tactic :=
  match l with
  | [] => []
  | (ns :: l) => intros_simpl ns :: name_pattern l
  end.

Definition NameNotFound (n: string) : Exception. exact exception. Qed.
Definition WrongType (T: Type) : Exception. exact exception. Qed.

Definition mwith {A} {B} (c: A) (n: string) (v: B) : M dyn :=
  (mfix1 app (d : dyn) : M _ :=
    let (ty, el) := d in
    mmatch d with
    | [? T1 T2 f] @Dyn (forall x:T1, T2 x) f =>
      binder <- get_binder_name ty;
      oeq <- munify binder n UniMatchNoRed;
      if oeq then
        oeq' <- munify B T1 UniCoq;
        match oeq' with
        | Some eq' =>
          let v' := reduce (RedWhd [RedMatch]) match eq' as x in _ = x with eq_refl=> v end in
          ret (Dyn (f v'))
        | _ => raise (WrongType T1)
        end
      else
        e <- evar T1;
        app (Dyn (f e))
    | _ =>
        raise (NameNotFound n)
    end
  ) (Dyn c).

(** Type for goal manipulation primitives *)
Definition selector := list goal -> M (list goal).

Fixpoint nsplit {A} (n : nat) (l : list A) : list A * list A :=
  match n, l with
  | 0, l => ([], l)
  | S n', (x :: l') =>
    let (l1, l2) := nsplit n' l' in
    (x :: l1, l2)
  | _, _ => ([], [])
  end.

Definition snth (n : nat) (t : tactic) : selector := fun l=>
  let (l1, l2) := dreduce (@nsplit) (nsplit n l) in
  match hd_error l2 with
  | None => raise NoGoalsLeft
  | Some g =>
    goals <- open_and_apply t g;
    let res := dreduce (@List.app) (l1 ++ goals ++ l2)%list in
    ret res
  end.

Definition slast (t : tactic) : selector := fun l=>
  let n := dreduce (pred, List.length) (pred (List.length l)) in
  snth n t l.

Definition sfirst (t : tactic) : selector := snth 0 t.

Definition srev : selector := fun l=>
  let res := dreduce (rev', rev_append, app) (rev' l) in ret res.

Definition tactic_selector (t: tactic) (s: selector) : tactic :=
  fun g=> l <- t g; l' <- filter_goals l; s l'.

Monomorphic Canonical Structure semicolon_tactic_selector :=
  SemiColon tactic_selector.

Definition mtac_selector {A} (t: M A) (u: A -> selector) : selector :=
  fun g=>x <- t; u x g.

Monomorphic Canonical Structure binding_selector A :=
  Binding (@mtac_selector A).

Module TacticsNotations.

Notation "t 'or' u" := (or t u) (at level 50).

(* We need a fresh evar to be able to use intro with ;; *)
Notation "'intro' x" :=
  ((fun g=>T <- evar Type; @intro_cont T (fun x=>idtac) g) : tactic) (at level 40).
Notation "'intros' x .. y" :=
  (intro_cont (fun x=>.. (intro_cont (fun y=>idtac)) ..))
    (at level 0, x binder, y binder, right associativity).
Notation "'intros'" := (intros_all).

Notation "'cintro' x '{-' t '-}'" := (intro_cont (fun x=>t)) (at level 0, right associativity).
Notation "'cintros' x .. y '{-' t '-}'" :=
  (intro_cont (fun x=>.. (intro_cont (fun y=>t)) ..))
    (at level 0, x binder, y binder, t at next level, right associativity).

Notation "'simpl'" := (treduce RedSimpl).
Notation "'hnf'" := (treduce RedHNF).
Notation "'cbv'" := (treduce RedNF).

Notation "'pose' ( x := t )" := (cpose t (fun x=>idtac)) (at level 40, x at next level).
Notation "'assert' ( x : T )" := (cassert (fun x:T=>idtac)) (at level 40, x at next level).

Notation "t 'asp' n" := (tactic_tactics t (name_pattern n)) (at level 40).

Notation "[[ |- ps ] ] => t" :=
  (gbase ps t)
  (at level 202, ps at next level) : goal_match_scope.

Notation "[[ x .. y |- ps ] ] => t" :=
  (gtele (fun x=> .. (gtele (fun y=>gbase ps t)).. ))
  (at level 202, x binder, y binder, ps at next level) : goal_match_scope.
Delimit Scope goal_match_scope with goal_match.

Arguments match_goal _%goal_match _.

Notation "t 'mwhere' m := u" := (elem (ltac:(mrun (v <- mwith t m u; ret v)))) (at level 0).

Notation "t1 '&>' t2" := (the_value t1 t2) (at level 41, left associativity).
Notation "t1 '|1>' t2" := (t1 &> snth 0 t2) (at level 41, left associativity, t2 at level 100).
Notation "t1 '|2>' t2" := (t1 &> snth 1 t2) (at level 41, left associativity, t2 at level 100).
Notation "t1 '|3>' t2" := (t1 &> snth 2 t2) (at level 41, left associativity, t2 at level 100).
Notation "t1 '|4>' t2" := (t1 &> snth 3 t2) (at level 41, left associativity, t2 at level 100).
Notation "t1 '|5>' t2" := (t1 &> snth 4 t2) (at level 41, left associativity, t2 at level 100).
Notation "t1 '|6>' t2" := (t1 &> snth 5 t2) (at level 41, left associativity, t2 at level 100).

Notation "t1 'l>' t2" := (t1 &> slast t2) (at level 41, left associativity, t2 at level 100).

End TacticsNotations.

Module TacticOverload.
Notation "r '<-' t1 ';' t2" := (the_bvalue t1 (fun r=>t2)).
Notation "t1 ';;' t2" := (the_bvalue t1 (fun _=>t2)).
End TacticOverload.

Module TacticUnoverload.
Notation "r '<-' t1 ';' t2" := (bind t1 (fun r=>t2)).
Notation "t1 ';;' t2" := (bind t1 (fun _=>t2)).
End TacticUnoverload.

Import TacticsNotations.

Definition assumption : tactic := fun g=>
  P <- goal_type g;
  match_goal ([[ x:P |- P ]] => exact x) g.

(** Given a type [T] it searches for a hypothesis with that type and
    executes the [cont]inuation on it.  *)
Definition select T (cont: T -> tactic) : tactic := fun g=>
  G <- goal_type g;
  match_goal ([[(x : T) |- G ]] => cont x) g.

(** [cut U] creates two goals with types [U -> T] and [U], where
    [T] is the type of the current goal. *)
Definition cut U : tactic := fun g=>
  T <- goal_type g;
  ut <- evar (U -> T);
  u <- evar U;
  exact (ut u) g;;
  ret [Goal ut; Goal u].


(** generalize with clear *)
Definition move_back {A} (x:A) (cont: tactic) : tactic :=
  generalize x &> cclear x cont.
