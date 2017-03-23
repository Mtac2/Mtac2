Require Import Strings.String.
From MetaCoq Require Export Mtac2.
Require Import MetaCoq.ListUtils MetaCoq.Utils.
Require Import Lists.List.
Import MtacNotations.
Import ListNotations.

Require Import Strings.String.
Require Import NArith.BinNat.
Require Import NArith.BinNatDef.

Local Set Universe Polymorphism.

(** The type for tactics *)
Definition gtactic (A : Type) := goal -> M (list (A * goal)).
Definition tactic := gtactic unit.

Coercion Mtac_to_gtactic {A} (x : M A) : gtactic A := fun g =>
  y <- x; ret [(y,g)].

Definition tret {A} (x : A) : gtactic A := fun g => ret [(x,g)].

(** no-op tactic *)
Definition idtac : tactic := tret tt.

(** fail tactic *)
Definition fail (e : Exception) : tactic := fun g => raise e.

Definition exact {A} (x:A) : tactic := fun g =>
  match g with
  | Goal g => cumul_or_fail x g;; ret []
  | _ => raise NotAGoal
  end.

Definition try (t : tactic) : tactic := fun g=>
  mtry t g with _ => ret [(tt, g)] end.

Definition or {A} (t u : gtactic A) : gtactic A := fun g=>
  mtry t g with _ => u g end.

(** [close_goals x l] takes the list of goals [l] and appends
    hypothesis [x] to each of them. *)
Definition close_goals {A B} (y : B) : list (A * goal) -> M (list (A * goal)) :=
  mmap (fun '(x,g') => r <- abs_fun y g'; ret (x, @AHyp B None r)).

(** [let_close_goals x l] takes the list of goals [l] and appends
    hypothesis [x] with its definition to each of them (it assumes it is defined). *)
Definition let_close_goals {A B} (y : B) : list (A * goal) -> M (list (A * goal)) :=
  let t := rone_step y in (* to obtain x's definition *)
  mmap (fun '(x,g') => r <- abs_fun y g'; ret (x, @AHyp B (Some t) r)).

(** Returns if a goal is open, i.e., a meta-variable. *)
Fixpoint is_open (g : goal) : M bool :=
  match g with
  | Goal e => is_evar e
  | @AHyp C _ f =>
    x <- fresh_binder_name f;
    (* we get the name in order to avoid inserting existing names
      (nu will raise an exception otherwise) *)
    nu x None (fun x : C => is_open (f x))
  end.

(** removes the goals that were solved *)
Definition filter_goals {A} : list (A * goal) -> M (list (A * goal)) :=
  mfilter (fun '(x,g) => is_open g).

(** [open_and_apply t] is a tactic that "opens" the current goal
    (pushes all the hypotheses in the context) and applies tactic [t]
    to the so-opened goal. The result is "closed" back. *)
Definition open_and_apply {A} (t : gtactic A) : gtactic A :=
  fix open g :=
    match g return M _ with
    | Goal _ => t g
    | @AHyp C None f =>
      x <- fresh_binder_name f;
      nu x None (fun x : C =>
        open (f x) >>= close_goals x)
    | @AHyp C (Some t) f =>
      x <- fresh_binder_name f;
      nu x (Some t) (fun x : C =>
        open (f x) >>= let_close_goals x)
    end.

Definition NoGoalsLeft : Exception. exact exception. Qed.

Definition tbind {A B} (t : gtactic A) (f : A -> gtactic B) : gtactic B := fun g=>
  gs <- t g;
  if is_empty gs then
    raise NoGoalsLeft
  else
    r <- mmap (fun '(x,g') => open_and_apply (f x) g') gs;
    let res := dreduce (concat, @List.app) (concat r) in
    ret res.

Definition NotSameSize : Exception. exact exception. Qed.

Fixpoint gmap {A} (tacs : list (gtactic A)) (gs : list goal) : M (list (list (A * goal))) :=
  match tacs, gs with
  | [], [] => ret []
  | tac :: tacs', g :: gs' =>
    fa <- open_and_apply tac g;
    rest <- gmap tacs' gs';
    ret (fa :: rest)
  | l, l' => raise NotSameSize
  end.

Definition tbind_list {A} (t : tactic) (f : list (gtactic A)) : gtactic A := fun g =>
  gs <- t g;
  ls <- gmap f (map snd gs);
  let res := dreduce (List.concat, List.app) (concat ls) in
  ret res.

Definition tgoal_type : gtactic Type := fun g =>
  gT <- goal_type g;
  ret [(gT, g)].

Definition NotAnEvar {A} (x: A) : Exception. exact exception. Qed.
Definition CantInstantiate {A} (x t: A) : Exception. exact exception. Qed.

(** [decompose x] decomposes value [x] into a head and a spine of
    arguments. For instance, [decompose (3 + 3)] returns
    [(Dyn add, [Dyn 3; Dyn 3])] *)
Definition decompose {A} (x : A) :=
  (mfix2 f (d : dyn) (args: list dyn) : M (dyn * list dyn) :=
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
  else raise (NotAnEvar h).

Definition NotAProduct : Exception. exact exception. Qed.

(** [intro_base n t] introduces variable or definition named [n]
    in the context and executes [t n].
    Raises [NotAProduct] if the goal is not a product or a let-binding. *)
Definition intro_base {A B} (var : string) (t : A -> gtactic B) : gtactic B := fun g=>
  mmatch g with
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

Definition intro_cont {A B} (t : A -> gtactic B) : gtactic B := fun g=>
  n <- get_binder_name t;
  intro_base n t g.

(** Given a name of a variable, it introduces it in the context *)
Definition intro_simpl (var : string) : tactic := fun g =>
  A <- evar Type;
  intro_base var (fun _ : A => idtac) g.

(** given a string s it appends a marker to avoid collition with user
    provided names *)
Definition anonymize (s : string) : M string :=
  let s' := rcbv ("__" ++ s) in
  ret s'.

(** Introduces an anonymous name based on a binder *)
Definition intro_anonymous {A} (T : A) (f : string -> M string) (g : goal) : M goal :=
  name <- get_binder_name T;
  axn <- anonymize name;
  axn <- f axn;
  res <- intro_simpl axn g >>= hd_exception;
  ret (snd res).

(** Introduces all hypotheses. Does not fail if there are 0. *)
Definition intros_all : tactic :=
  mfix1 f (g : goal) : M (list (unit * goal)) :=
    open_and_apply (fun g =>
      match g return M (list (unit * goal)) with
      | @Goal T e =>
        mtry intro_anonymous T ret g >>= f with
        | WrongTerm => ret [(tt,g)]
        | NotAProduct => ret [(tt,g)]
        | [? s] NameExistsInContext s => intro_anonymous T fresh_name g >>= f
        end
      | _ => raise NotAGoal
      end) g.

(** Introduces up to n binders. Throws [NotAProduct] if there
    aren't enough products in the goal.  *)
Definition introsn : nat -> tactic :=
  mfix2 f (n : nat) (g : goal) : M (list (unit * goal)) :=
    open_and_apply (fun g =>
      match n, g with
      | 0, g => ret [(tt,g)]
      | S n', @Goal T e =>
        mtry intro_anonymous T ret g >>= f n' with
        | WrongTerm => raise NotAProduct
        | [? s] NameExistsInContext s => intro_anonymous T fresh_name g >>= f n'
        end
      | _, _ => failwith "Should never get here"
      end) g.

(** Applies reflexivity *)
Definition prim_reflexivity : tactic := fun g =>
  A <- evar Type;
  x <- evar A;
  unify_or_fail g (Goal (eq_refl x));; ret [].

(** Fist introduces the hypotheses and then applies reflexivity *)
Definition reflexivity : tactic := fun g =>
  l <- intros_all g;
  g <- hd_exception l;
  open_and_apply prim_reflexivity (snd g).

(** Overloaded binding *)
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
  mfilter (fun y =>
    mmatch y with
    | [? b] ahyp x b => ret false
    | _ => ret true
    end) l.

Definition find_hyp_index {A} (x : A) : M (option nat) :=
  l <- hypotheses;
  mindex_of (fun y =>
    mmatch y with
    | [? b] ahyp x b => ret true
    | _ => ret false
    end) l.

(** Generalizes a goal given a certain hypothesis [x]. It does not
    remove [x] from the goal. *)
Definition generalize {A} (x : A) : tactic := fun g =>
  P <- goal_type g;
  aP <- abs_prod x P; (* aP = (forall x:A, P) *)
  e <- evar aP;
  mmatch aP with
  | [? Q : A -> Type] (forall z:A, Q z) =n> [H]
    let e' :=
      rcbv match H in _ = Q return Q with eq_refl _ => e end in
    exact (e' x) g;;
    ret [(tt, Goal e)]
  | _ => failwith "generalize: should never happen"
  end.

(** Clear hypothesis [x] and continues the execution on [cont] *)
Definition cclear {A B} (x:A) (cont : gtactic B) : gtactic B := fun g=>
  gT <- goal_type g;
  r <- Mtac2.remove x (
    e <- evar gT;
    l <- cont (Goal e);
    ret (e, l));
  let (e, l) := r in
  exact e g;;
  ret l.

Definition clear {A} (x:A) : tactic := cclear x idtac.

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
  let res := dreduce (List.map, dyn_to_goal)
                     (List.map (fun d => (tt, dyn_to_goal d)) l) in
  ret res.

(** Destructs the n-th hypotheses in the goal (counting from 0) *)
Definition destructn (n : nat) : tactic :=
  tbind (introsn n) (fun _ g =>
    A <- evar Type;
    n <- fresh_name "tmp";
    @intro_base A _ n destruct g).

Definition CantApply {T1 T2} (x:T1) (y:T2) : Exception. exact exception. Qed.

Definition apply {T} (c : T) : tactic := fun g=>
  match g with Goal eg =>
    (mfix1 app (d : dyn) : M (list (unit * goal)) :=
      let (_, el) := d in
      mif munify_cumul el eg UniCoq then
        ret []
      else
        mmatch d return M (list (unit * goal)) with
        | [? T1 T2 f] @Dyn (forall x:T1, T2 x) f =>
          e <- evar T1;
          r <- app (Dyn (f e));
          mif is_evar e then
            ret ((tt, Goal e) :: r)
          else ret r
        | _ =>
          gT <- goal_type g;
          raise (CantApply T gT)
        end) (Dyn c)
  | _ => raise NotAGoal
  end.

Definition change (P : Type) : tactic := fun g =>
  gT <- goal_type g;
  unify_or_fail P gT;;
  e <- evar P;
  exact e g;;
  ret [(tt, Goal e)].

Definition change_hyp {P Q} (H : P) (newH: Q) : tactic := fun g =>
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
  ret [(tt, AHyp None g')].

Definition apply_in {P Q} (c : P -> Q) (H : P) : tactic :=
  change_hyp H (c H).

Definition transitivity {B} (y : B) : tactic :=
  apply (fun x => @eq_trans B x y).

Definition symmetry : tactic :=
  apply eq_sym.

Definition exfalso : tactic :=
  apply False_ind.

Definition CantFindConstructor : Exception. exact exception. Qed.
Definition ConstructorsStartsFrom1 : Exception. exact exception. Qed.

Definition constructor (n : nat) : tactic := fun g =>
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

Definition split : tactic := fun g =>
  A <- goal_type g;
  l <- constrs A;
  match snd l with
  | [_] => constructor 1 g
  | _ => raise Not1Constructor
  end.

Definition Not2Constructor : Exception. exact exception. Qed.

Definition left : tactic := fun g =>
  A <- goal_type g;
  l <- constrs A;
  match snd l with
  | [Dyn x; _] => apply x g
  | _ => raise Not2Constructor
  end.

Definition right : tactic := fun g =>
  A <- goal_type g;
  l <- constrs A;
  match snd l with
  | [_; Dyn x] => apply x g
  | _ => raise Not2Constructor
  end.

Inductive goal_pattern : Type :=
| gbase : forall {A}, A -> tactic -> goal_pattern
| gtele : forall {C}, (C -> goal_pattern) -> goal_pattern
| gtele_evar : forall {C}, (C -> goal_pattern) -> goal_pattern.

Definition DoesNotMatchGoal : Exception. exact exception. Qed.
Definition NoPatternMatchesGoal : Exception. exact exception. Qed.

Fixpoint match_goal_pattern'
    (u : Unification) (p : goal_pattern) : list Hyp -> list Hyp -> tactic :=
  fix go l1 l2 g :=
  match p, l2 with
  | gbase P t, _ =>
    gT <- goal_type g;
    mif munify_cumul P gT u then t g
    else raise DoesNotMatchGoal
  | @gtele C f, (@ahyp A a d :: l2') =>
    oeqCA <- munify C A u;
    match oeqCA with
    | Some eqCA =>
      let a' := rcbv match eq_sym eqCA with eq_refl => a end in
      mtry match_goal_pattern' u (f a') [] (List.rev_append l1 l2')%list g
      with DoesNotMatchGoal =>
        go (ahyp a d :: l1) l2' g
      end
    | None => go (ahyp a d :: l1) l2' g end
  | @gtele_evar C f, _ =>
    e <- evar C;
    match_goal_pattern' u (f e) l1 l2 g
  | _, _ => raise DoesNotMatchGoal
  end.

Definition match_goal_pattern (u : Unification) (p : goal_pattern) : tactic := fun g=>
  r <- hypotheses; match_goal_pattern' u p [] (List.rev' r) g.

Fixpoint match_goal_base (u : Unification) (ps : list goal_pattern) : tactic := fun g =>
  match ps with
  | [] => raise NoPatternMatchesGoal
  | p :: ps' =>
    mtry match_goal_pattern u p g
    with DoesNotMatchGoal => match_goal_base u ps' g end
  end.

Definition ltac (t : string) (args : list dyn) : tactic := fun g =>
  d <- goal_to_dyn g;
  let (ty, el) := d in
  v <- @call_ltac ty t args;
  let (v, l) := v in
  unify_or_fail v el;;
  b <- is_evar v;
  if b then
    ret [(tt, Goal v)] (* it wasn't solved *)
  else
    let l' := dreduce (@List.map) (map (pair tt) l) in
    ret l'.

Definition destruct_all (T : Type) : tactic := fun g=>
  l <- hypotheses;
  l <- mfilter (fun h:Hyp=>
    let (Th, _, _) := h in
    r <- munify Th T UniCoq;
    ret (option_to_bool r)) l;
  (fix f (l : list Hyp) : tactic :=
    match l with
    | [] => idtac
    | ahyp x _ :: l => tbind (destruct x) (fun _ => f l)
    end) l g.

Definition treduce (r : Reduction) : tactic := fun g=>
  T <- goal_type g;
  let T' := reduce r T in
  e <- evar T';
  b <- munify_cumul g (@Goal T e) UniMatch;
  match b with
  | true => ret [(tt, Goal e)]
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
    mtry tbind (typed_intro T) (fun _ => f) g with
    | NotThatType => idtac g
    end) g.

Definition cpose_base {A B} (name : string) (t : A)
    (cont: A -> gtactic B) : gtactic B := fun g =>
  nu name (Some t) (fun x=>
    gT <- goal_type g;
    r <- evar gT;
    value <- abs_let x t r;
    exact value g;;
    cont x (Goal r) >>= let_close_goals x).

Definition cpose {A} (t: A) (cont: A -> tactic) : tactic := fun g =>
  n <- get_binder_name cont;
  cpose_base n t cont g.

Definition cassert_base {A} (name : string)
    (cont : A -> tactic) : tactic := fun g =>
  a <- evar A; (* [a] will be the goal to solve [A] *)
  nu name None (fun x =>
    gT <- goal_type g;
    r <- evar gT; (* The new goal now referring to n *)
    value <- abs_fun x r;
    exact (value a) g;; (* instantiate the old goal with the new one *)
    v <- cont x (Goal r) >>= close_goals x;
    ret ((tt,Goal a) :: v)). (* append the goal for a to the top of the goals *)

Definition cassert {A} (cont: A -> tactic) : tactic := fun g=>
  n <- get_binder_name cont;
  cassert_base n cont g.

(* performs simpl in each hypothesis and in the goal *)
Definition simpl_in_all : tactic := fun g =>
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
  | Some (eq_refl _) => ret [(tt,Goal e)]
  | _ => raise exception (* should never happen *)
  end.

Definition reduce_in r {P} (H: P) : tactic := fun g =>
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
  | Some (eq_refl _) => ret [(tt,Goal e)]
  | _ => raise exception (* should never happen *)
  end.

Definition simpl_in {P} (H: P) : tactic :=
  reduce_in RedSimpl H.

(** exists tactic *)
Definition mexists {A} (x: A) : tactic := fun g =>
  P <- evar _;
  e <- evar _;
  oeq <- munify g (Goal (@ex_intro _ P x e)) UniCoq;
  match oeq with
  | Some (eq_refl _) => ret [(tt,Goal e)]
  | _ => raise (NotUnifiable g (Goal (@ex_intro _ P x e)))
  end.

(** Printing of a goal *)
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

Definition print_goal : tactic := fun g =>
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
Definition n_etas (n : nat) {A} (f : A) : M A :=
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

(** [fix_tac f n] is like Coq's [fix] tactic: it generates a fixpoint
    with a new goal as body, containing a variable named [f] with
    the current goal as type. The goal is expected to have at least
    [n] products. *)
Definition fix_tac (f : string) (n : N) : tactic := fun g =>
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
  ret [(tt,new_goal)].

(** [repeat t] applies tactic [t] to the goal several times
    (it should only generate at most 1 subgoal), until no
    changes or no goal is left. *)
Definition repeat (t : tactic) : tactic := fun g =>
  (mfix1 f (g : goal) : M (list (unit * goal)) :=
    r <- try t g; (* if it fails, the execution will stop below *)
    match r with
    | [] => ret []
    | [(_,g')] =>
      mmatch g with
      | g' => ret [(tt,g)] (* the goal is the same, return *)
      | _ => f g'
      end
    | _ => print_term r;; failwith "The tactic generated more than a goal"
    end) g.

Definition map_term (f : forall d:dyn, M d.(type)) : forall d : dyn, M d.(type) :=
  mfix1 rec (d : dyn) : M d.(type) :=
    let (ty, el) := d in
    mmatch d as d return M d.(type) with
    | [? B A (b: B) (a: B -> A)] Dyn (a b) =n>
      d1 <- rec (Dyn a);
      d2 <- rec (Dyn b);
      ret (d1 d2)
    | [? B (A: B -> Type) (a: forall x, A x)] Dyn (fun x:B=>a x) =n>
      n <- get_binder_name el;
      nu n None (fun x : B =>
        d1 <- rec (Dyn (a x));
        abs_fun x d1)
    | [? B (A: B -> Type) a] Dyn (forall x:B, a x) =n>
      n <- get_binder_name el;
      nu n None (fun x : B =>
        d1 <- rec (Dyn (a x));
        abs_prod x d1)
    | [? d'] d' =n> f d'
    end.

Definition unfold_slow {A} (x : A) : tactic := fun g =>
  let def := rone_step x in
  gT <- goal_type g;
  gT' <- map_term (fun d =>
    let (ty, el) := d in
    mmatch d as d return M d.(type) with
    | Dyn x =n> ret def
    | [? A (d': A)] Dyn d' =n> ret d'
    end) (Dyn gT);
  e <- evar gT';
  exact e g;;
  ret [(tt,Goal e)].

Definition unfold {A} (x : A) : tactic := fun g =>
  gT <- goal_type g;
  let gT' := dreduce (x) gT in
  ng <- evar gT';
  exact ng g;;
  ret [(tt, Goal ng)].

Definition unfold_in {A B} (x : A) (h : B) : tactic :=
  reduce_in (RedStrong [RedBeta; RedMatch; RedFix; RedDeltaOnly [Dyn x]]) h.

Fixpoint intros_simpl (l : list string) : tactic :=
  match l with
  | [] => idtac
  | n :: l => tbind (intro_simpl n) (fun _ => intros_simpl l)
  end.

Fixpoint name_pattern (l : list (list string)) : list tactic :=
  match l with
  | [] => []
  | ns :: l => intros_simpl ns :: name_pattern l
  end.

(** Type for goal manipulation primitives *)
Definition selector := list (unit * goal) -> M (list (unit * goal)).

Definition snth (n : nat) (t : tactic) : selector := fun l =>
  let (l1, l2) := dreduce (@nsplit) (nsplit n l) in
  match hd_error l2 with
  | None => raise NoGoalsLeft
  | Some (_, g) =>
    goals <- open_and_apply t g;
    let res := dreduce (@List.app, @List.tail) (l1 ++ goals ++ tail l2)%list in
    ret res
  end.

Definition slast (t : tactic) : selector := fun l =>
  let n := dreduce (pred, List.length) (pred (List.length l)) in
  snth n t l.

Definition sfirst (t : tactic) : selector := snth 0 t.

Definition srev : selector := fun l =>
  let res := dreduce (rev', rev_append, app) (rev' l) in ret res.

Definition tactic_selector (t: tactic) (s: selector) : tactic := fun g =>
  l <- t g;
  filter_goals l >>= s.

Module TacticsNotations.
Delimit Scope tactic_scope with tactic.
Bind Scope tactic_scope with tactic.
Open Scope tactic_scope.

(* This notation makes sure that [t] is in [MC] scope ands casts the resulting
lambda into a [tactic] to make sure that it can be ran. *)
Notation "\tactic g => t" :=
  ((fun g => t%MC) : tactic) (at level 200, g at level 0, right associativity).

Notation "r '<-' t1 ';' t2" := (tbind t1 (fun r=> t2%tactic))
  (at level 81, right associativity, format "'[' r  '<-'  '[' t1 ;  ']' ']' '/' t2 ") : tactic_scope.
Notation "t1 ';;' t2" := (tbind t1 (fun _=>t2%tactic))
  (at level 81, right associativity, format "'[' '[' t1 ;;  ']' ']' '/' t2 ") : tactic_scope.
Notation "t >>= f" := (tbind t f) (at level 70) : tactic_scope.

Notation "t 'or' u" := (or t u) (at level 50) : tactic_scope.

(* We need a fresh evar to be able to use intro with ;; *)
Notation "'intro' x" :=
  (T <- evar Type; @intro_cont T _ (fun x=>idtac))
  (at level 40) : tactic_scope.
Notation "'intros' x .. y" :=
  (intro_cont (fun x=>.. (intro_cont (fun y=>idtac)) ..))
  (at level 0, x binder, y binder, right associativity) : tactic_scope.
Notation "'intros'" := intros_all : tactic_scope.

Notation "'cintro' x '{-' t '-}'" :=
  (intro_cont (fun x=>t)) (at level 0, right associativity) : tactic_scope.
Notation "'cintros' x .. y '{-' t '-}'" :=
  (intro_cont (fun x=>.. (intro_cont (fun y=>t)) ..))
  (at level 0, x binder, y binder, t at next level, right associativity) : tactic_scope.

Notation "'simpl'" := (treduce RedSimpl) : tactic_scope.
Notation "'hnf'" := (treduce RedHNF) : tactic_scope.
Notation "'cbv'" := (treduce RedNF) : tactic_scope.

Notation "'pose' ( x := t )" :=
  (cpose t (fun x=>idtac)) (at level 40, x at next level) : tactic_scope.
Notation "'assert' ( x : T )" :=
  (cassert (fun x:T=>idtac)) (at level 40, x at next level) : tactic_scope.

Notation "t 'asp' n" :=
  (tbind_list t (name_pattern n)) (at level 40) : tactic_scope.

Notation "[[ |- ps ] ] => t" :=
  (gbase ps t)
  (at level 202, ps at next level) : match_goal_pattern_scope.

Notation "[[? a .. b | x .. y |- ps ] ] => t" :=
  (gtele_evar (fun a => .. (gtele_evar (fun b =>
     gtele (fun x=> .. (gtele (fun y=>gbase ps t)).. ))).. ))
  (at level 202, a binder, b binder,
   x binder, y binder, ps at next level) : match_goal_pattern_scope.

Notation "[[? a .. b |- ps ] ] => t" :=
  (gtele_evar (fun a => .. (gtele_evar (fun b => gbase ps t)).. ))
  (at level 202, a binder, b binder, ps at next level) : match_goal_pattern_scope.

Notation "[[ x .. y |- ps ] ] => t" :=
  (gtele (fun x=> .. (gtele (fun y=>gbase ps t)).. ))
  (at level 202, x binder, y binder, ps at next level) : match_goal_pattern_scope.

Delimit Scope match_goal_pattern_scope with match_goal_pattern.

Notation "'with' | p1 | .. | pn 'end'" :=
  ((@cons goal_pattern p1%match_goal_pattern (.. (@cons goal_pattern pn%match_goal_pattern nil) ..)))
    (at level 91, p1 at level 210, pn at level 210) : match_goal_with_scope.
Notation "'with' p1 | .. | pn 'end'" :=
  ((@cons goal_pattern p1%match_goal_pattern (.. (@cons goal_pattern pn%match_goal_pattern nil) ..)))
    (at level 91, p1 at level 210, pn at level 210) : match_goal_with_scope.

Delimit Scope match_goal_with_scope with match_goal_with.

Notation "'match_goal' ls" := (match_goal_base UniCoq ls%match_goal_with)
  (at level 90, ls at level 91) : tactic_scope.
Notation "'match_goal_nored' ls" := (match_goal_base UniMatchNoRed ls%match_goal_with)
  (at level 90, ls at level 91) : tactic_scope.

Notation "t1 '&>' ts" :=
  (tbind_list t1 ts) (at level 41, left associativity) : tactic_scope.
Notation "t1 '|1>' t2" :=
  (tactic_selector t1 (snth 0 t2))
  (at level 41, left associativity, t2 at level 100) : tactic_scope.
Notation "t1 '|2>' t2" :=
  (tactic_selector t1 (snth 1 t2))
  (at level 41, left associativity, t2 at level 100) : tactic_scope.
Notation "t1 '|3>' t2" :=
  (tactic_selector t1 (snth 2 t2))
  (at level 41, left associativity, t2 at level 100) : tactic_scope.
Notation "t1 '|4>' t2" :=
  (tactic_selector t1 (snth 3 t2))
  (at level 41, left associativity, t2 at level 100) : tactic_scope.
Notation "t1 '|5>' t2" :=
  (tactic_selector t1 (snth 4 t2))
  (at level 41, left associativity, t2 at level 100) : tactic_scope.
Notation "t1 '|6>' t2" :=
  (tactic_selector t1 (snth 5 t2))
  (at level 41, left associativity, t2 at level 100) : tactic_scope.

Notation "t1 'l>' t2" :=
  (t1 &> slast t2)
  (at level 41, left associativity, t2 at level 100) : tactic_scope.
End TacticsNotations.

Import TacticsNotations.

Definition assumption : tactic :=
  G <- tgoal_type;
  match_goal with [[ x : G |- G ]] => exact x end.

(** Given a type [T] it searches for a hypothesis with that type and
    executes the [cont]inuation on it.  *)
Definition select (T : Type) (cont : T -> tactic) : tactic :=
  G <- tgoal_type;
  match_goal with [[ x : T |- G ]] => cont x end.

(** [cut U] creates two goals with types [U -> T] and [U], where
    [T] is the type of the current goal. *)
Definition cut (U : Type) : tactic := \tactic g =>
  T <- goal_type g;
  ut <- evar (U -> T);
  u <- evar U;
  exact (ut u) g;;
  ret [(tt,Goal ut); (tt,Goal u)].

(** generalize with clear *)
Definition move_back {A} (x : A) (cont : tactic) : tactic :=
  generalize x ;; cclear x cont.
