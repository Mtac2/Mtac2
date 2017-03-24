Require Import Strings.String.
From MetaCoq Require Export Mtac2.
Require Import MetaCoq.Utils.
Require Import Lists.List.
Import M.notations.
Import ListNotations.

Require Import Strings.String.
Require Import NArith.BinNat.
Require Import NArith.BinNatDef.

Local Set Universe Polymorphism.

(** Exceptions *)
Definition NoGoalsLeft : Exception. exact exception. Qed.
Definition NotSameSize : Exception. exact exception. Qed.

Definition NotAnEvar {A} (x: A) : Exception. exact exception. Qed.
Definition CantInstantiate {A} (x t: A) : Exception. exact exception. Qed.

Definition NotAProduct : Exception. exact exception. Qed.

Definition SomethingNotRight {A} (t : A) : Exception. exact exception. Qed.

Definition CantApply {T1 T2} (x:T1) (y:T2) : Exception. exact exception. Qed.

Definition CantFindConstructor : Exception. exact exception. Qed.
Definition ConstructorsStartsFrom1 : Exception. exact exception. Qed.

Definition Not1Constructor : Exception. exact exception. Qed.
Definition Not2Constructor : Exception. exact exception. Qed.

Definition DoesNotMatchGoal : Exception. exact exception. Qed.
Definition NoPatternMatchesGoal : Exception. exact exception. Qed.

Definition NotThatType : Exception. exact exception. Qed.

(** The type for tactics *)
Definition gtactic (A : Type) := goal -> M (list (A * goal)).
Definition tactic := gtactic unit.

Delimit Scope tactic_scope with tactic.
Bind Scope tactic_scope with tactic.
Bind Scope tactic_scope with gtactic.

Module T.
Definition with_goal {A} (f : goal -> M A) := fun g =>
  y <- f g; M.ret [(y,g)].

Coercion of_M {A} (x : M A) : gtactic A := with_goal (fun _ => x).

Definition mtry' {A} (t : gtactic A)
    (f : Exception -> gtactic A) : gtactic A := fun g =>
  M.mtry' (t g) (fun e => f e g).

Definition raise {A} (e : Exception) : gtactic A := M.raise e.

Definition fix0 (B : Type) : (gtactic B -> gtactic B) -> gtactic B :=
  @M.fix1 goal (fun _ => list (B * goal)).

Definition fix1 {A} (B : A -> Type) :
    ((forall x : A, gtactic (B x)) -> (forall x : A, gtactic (B x))) ->
    forall x : A, gtactic (B x) :=
  @M.fix2 A (fun _ => goal) (fun x _ => list (B x * goal)).

Definition fix2 {A1} {A2 : A1 -> Type} (B : forall a1 : A1, A2 a1 -> Type) :
    ((forall (x1 : A1) (x2 : A2 x1), gtactic (B x1 x2)) ->
      forall (x1 : A1) (x2 : A2 x1), gtactic (B x1 x2)) ->
    forall (x1 : A1) (x2 : A2 x1), gtactic (B x1 x2) :=
  @M.fix3 A1 A2 (fun _ _ => goal) (fun x y _ => list (B x y * goal)).

Definition fix3 {A1} {A2 : A1 -> Type} {A3 : forall a1 : A1, A2 a1 -> Type}
  (B : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type) :
    ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), gtactic (B x1 x2 x3)) ->
      forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), gtactic (B x1 x2 x3)) ->
    forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), gtactic (B x1 x2 x3) :=
  @M.fix4 A1 A2 A3 (fun _ _ _ => goal) (fun x y z _ => list (B x y z * goal)).

Definition fix4 {A1} {A2 : A1 -> Type} {A3 : forall a1 : A1, A2 a1 -> Type}
    {A4 : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type}
    (B : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2), A4 a1 a2 a3 -> Type) :
    ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), gtactic (B x1 x2 x3 x4)) ->
      forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), gtactic (B x1 x2 x3 x4)) ->
    forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), gtactic (B x1 x2 x3 x4) :=
  @M.fix5 A1 A2 A3 A4 (fun _ _ _ _ => goal) (fun x y z z' _ => list (B x y z z' * goal)).

(* TODO: copy paste should be avoided *)
Polymorphic Fixpoint open_pattern {A P y} (p : pattern gtactic A P y)
    (g : goal) : M (list (P y * goal)) :=
  match p with
  | pbase x f u =>
    oeq <- M.unify x y u;
    match oeq return M (list (P y * goal)) with
    | Some eq =>
      (* eq has type x = t, but for the pattern we need t = x.
         we still want to provide eq_refl though, so we reduce it *)
      let h := reduce (RedStrong [RedBeta;RedDelta;RedMatch]) (eq_sym eq) in
      let 'eq_refl := eq in
      (* For some reason, we need to return the beta-reduction of the pattern, or some tactic fails *)
      let b := reduce (RedStrong [RedBeta]) (f h g) in b
    | None => M.raise DoesNotMatch
    end
  | @ptele _ _ _ _ C f => e <- M.evar C; open_pattern (f e) g
  end.

Polymorphic Fixpoint mmatch' {A P} (y : A) (ps : list (pattern gtactic A P y)) : gtactic (P y) :=
  match ps with
  | [] => raise NoPatternMatches
  | p :: ps' => fun g =>
    M.mtry' (open_pattern p g) (fun e =>
      mif M.unify e DoesNotMatch UniMatchNoRed then mmatch' y ps' g else M.raise e)
  end.

Definition ret {A} (x : A) : gtactic A := fun g => M.ret [(x,g)].
Definition idtac : tactic := ret tt.

Definition try (t : tactic) : tactic := fun g=>
  mtry t g with _ => M.ret [(tt, g)] end.

Definition or {A} (t u : gtactic A) : gtactic A := fun g=>
  mtry t g with _ => u g end.

(** [close_goals x l] takes the list of goals [l] and appends
    hypothesis [x] to each of them. *)
Definition close_goals {A B} (y : B) : list (A * goal) -> M (list (A * goal)) :=
  M.map (fun '(x,g') => r <- M.abs_fun y g'; M.ret (x, @AHyp B None r)).

(** [let_close_goals x l] takes the list of goals [l] and appends
    hypothesis [x] with its definition to each of them (it assumes it is defined). *)
Definition let_close_goals {A B} (y : B) : list (A * goal) -> M (list (A * goal)) :=
  let t := rone_step y in (* to obtain x's definition *)
  M.map (fun '(x,g') => r <- M.abs_fun y g'; M.ret (x, @AHyp B (Some t) r)).

(** Returns if a goal is open, i.e., a meta-variable. *)
Fixpoint is_open (g : goal) : M bool :=
  match g with
  | Goal e => M.is_evar e
  | @AHyp C _ f =>
    x <- M.fresh_binder_name f;
    (* we get the name in order to avoid inserting existing names
      (nu will raise an exception otherwise) *)
    M.nu x None (fun x : C => is_open (f x))
  end.

(** removes the goals that were solved *)
Definition filter_goals {A} : list (A * goal) -> M (list (A * goal)) :=
  M.filter (fun '(x,g) => is_open g).

(** [open_and_apply t] is a tactic that "opens" the current goal
    (pushes all the hypotheses in the context) and applies tactic [t]
    to the so-opened goal. The result is "closed" back. *)
Definition open_and_apply {A} (t : gtactic A) : gtactic A :=
  fix open g :=
    match g return M _ with
    | Goal _ => t g
    | @AHyp C None f =>
      x <- M.fresh_binder_name f;
      M.nu x None (fun x : C =>
        open (f x) >>= close_goals x)
    | @AHyp C (Some t) f =>
      x <- M.fresh_binder_name f;
      M.nu x (Some t) (fun x : C =>
        open (f x) >>= let_close_goals x)
    end.

Definition bind {A B} (t : gtactic A) (f : A -> gtactic B) : gtactic B := fun g =>
  gs <- t g;
  r <- M.map (fun '(x,g') => open_and_apply (f x) g') gs;
  let res := dreduce (concat, @List.app) (concat r) in
  M.ret res.

Fixpoint gmap {A} (tacs : list (gtactic A)) (gs : list goal) : M (list (list (A * goal))) :=
  match tacs, gs with
  | [], [] => M.ret []
  | tac :: tacs', g :: gs' =>
    fa <- open_and_apply tac g;
    rest <- gmap tacs' gs';
    M.ret (fa :: rest)
  | l, l' => M.raise NotSameSize
  end.

Definition bind_list {A} (t : tactic) (f : list (gtactic A)) : gtactic A := fun g =>
  gs <- t g;
  ls <- gmap f (map snd gs);
  let res := dreduce (List.concat, List.app) (concat ls) in
  M.ret res.


Definition exact {A} (x:A) : tactic := fun g =>
  match g with
  | Goal g => M.cumul_or_fail x g;; M.ret []
  | _ => M.raise NotAGoal
  end.

Definition goal_type : gtactic Type := with_goal M.goal_type.

(** [instantiate x t] tries to instantiate meta-variable [x] with [t].
    It fails with [NotAnEvar] if [x] is not a meta-variable (applied to a spine), or
    [CantInstantiate] if it fails to find a suitable instantiation. [t] is beta-reduced
    to avoid false dependencies. *)
Definition instantiate {A} (x t : A) : M unit :=
  k <- M.decompose x;
  let (h, _) := k in
  let h := rcbv h.(elem) in
  b <- M.is_evar h;
  let t := reduce (RedWhd [RedBeta]) t in
  if b then
    r <- M.unify x t UniEvarconv;
    match r with
    | Some _ => M.ret tt
    | _ => M.raise (CantInstantiate x t)
    end
  else M.raise (NotAnEvar h).

(** [intro_base n t] introduces variable or definition named [n]
    in the context and executes [t n].
    Raises [NotAProduct] if the goal is not a product or a let-binding. *)
Definition intro_base {A B} (var : string) (t : A -> gtactic B) : gtactic B := fun g=>
  mmatch g with
  | [? B (def: B) P e] @Goal (let x := def in P x) e =n>
    (* normal match will not instantiate meta-variables from the scrutinee, so we do the inification here*)
    eqBA <- M.unify_or_fail B A;
    M.nu var (Some def) (fun x=>
      let Px := reduce (RedWhd [RedBeta]) (P x) in
      e' <- M.evar Px;
      nG <- M.abs_let (P:=P) x def e';
      exact nG g;;
      let x := reduce (RedWhd [RedMatch]) (match eqBA with eq_refl => x end) in
      t x (Goal e') >>= let_close_goals x)
  | [? P e] @Goal (forall x:A, P x) e =u>
    M.nu var None (fun x=>
      let Px := reduce (RedWhd [RedBeta]) (P x) in
      e' <- M.evar Px;
      nG <- M.abs_fun (P:=P) x e';
      exact nG g;;
      t x (Goal e') >>= close_goals x)
  | _ => M.raise NotAProduct
  end.

Definition intro_cont {A B} (t : A -> gtactic B) : gtactic B := fun g=>
  n <- M.get_binder_name t;
  intro_base n t g.

(** Given a name of a variable, it introduces it in the context *)
Definition intro_simpl (var : string) : tactic := fun g =>
  A <- M.evar Type;
  intro_base var (fun _ : A => idtac) g.

(** Introduces an anonymous name based on a binder *)
Definition intro_anonymous {A} (T : A) (f : string -> M string) (g : goal) : M goal :=
  name <- M.get_binder_name T;
  axn <- M.anonymize name;
  axn <- f axn;
  res <- intro_simpl axn g >>= M.hd;
  M.ret (snd res).

(** Introduces all hypotheses. Does not fail if there are 0. *)
Definition intros_all : tactic :=
  mfix1 f (g : goal) : M (list (unit * goal)) :=
    open_and_apply (fun g =>
      match g return M (list (unit * goal)) with
      | @Goal T e =>
        mtry intro_anonymous T M.ret g >>= f with
        | WrongTerm => M.ret [(tt,g)]
        | NotAProduct => M.ret [(tt,g)]
        | [? s] NameExistsInContext s => intro_anonymous T M.fresh_name g >>= f
        end
      | _ => M.raise NotAGoal
      end) g.

(** Introduces up to n binders. Throws [NotAProduct] if there
    aren't enough products in the goal.  *)
Definition introsn : nat -> tactic :=
  mfix2 f (n : nat) (g : goal) : M (list (unit * goal)) :=
    open_and_apply (fun g =>
      match n, g with
      | 0, g => M.ret [(tt,g)]
      | S n', @Goal T e =>
        mtry intro_anonymous T M.ret g >>= f n' with
        | WrongTerm => M.raise NotAProduct
        | [? s] NameExistsInContext s => intro_anonymous T M.fresh_name g >>= f n'
        end
      | _, _ => M.failwith "Should never get here"
      end) g.

(** Applies reflexivity *)
Definition prim_reflexivity : tactic := fun g =>
  A <- M.evar Type;
  x <- M.evar A;
  M.unify_or_fail g (Goal (eq_refl x));; M.ret [].

(** Fist introduces the hypotheses and then applies reflexivity *)
Definition reflexivity : tactic := fun g =>
  l <- intros_all g;
  g <- M.hd l;
  open_and_apply prim_reflexivity (snd g).

(** Overloaded binding *)
Definition copy_ctx {A} (B : A -> Type) : dyn -> M Type :=
  mfix1 rec (d : dyn) : M Type :=
    mmatch d with
    | [? c : A] Dyn c =>
      let Bc := reduce (RedWhd [RedBeta]) (B c) in
      M.ret Bc
    | [? C (D : C -> Type) (c : forall y:C, D y)] Dyn c =>
      n <- M.fresh_binder_name c;
      M.nu n None (fun y=>
        r <- rec (Dyn (c y));
        M.abs_prod y r)
    | [? C D (c : C->D)] Dyn c =>
      n <- M.fresh_binder_name c;
      M.nu n None (fun y=>
        r <- rec (Dyn (c y));
        M.abs_prod y r)
    | _ => M.print_term A;; M.raise (SomethingNotRight d)
    end.

(** Generalizes a goal given a certain hypothesis [x]. It does not
    remove [x] from the goal. *)
Definition generalize {A} (x : A) : tactic := fun g =>
  P <- M.goal_type g;
  aP <- M.abs_prod x P; (* aP = (forall x:A, P) *)
  e <- M.evar aP;
  mmatch aP with
  | [? Q : A -> Type] (forall z:A, Q z) =n> [H]
    let e' :=
      rcbv match H in _ = Q return Q with eq_refl _ => e end in
    exact (e' x) g;;
    M.ret [(tt, Goal e)]
  | _ => M.failwith "generalize: should never happen"
  end.

(** Clear hypothesis [x] and continues the execution on [cont] *)
Definition cclear {A B} (x:A) (cont : gtactic B) : gtactic B := fun g=>
  gT <- M.goal_type g;
  r <- M.remove x (
    e <- M.evar gT;
    l <- cont (Goal e);
    M.ret (e, l));
  let (e, l) := r in
  exact e g;;
  M.ret l.

Definition clear {A} (x : A) : tactic := cclear x idtac.

Definition destruct {A : Type} (n : A) : tactic := fun g=>
  let A := rhnf A in
  b <- let n := rcbv n in M.is_var n;
  ctx <- if b then M.hyps_except n else M.hyps;
  P <- M.Cevar (A->Type) ctx;
  let Pn := P n in
  gT <- M.goal_type g;
  M.unify_or_fail Pn gT;;
  l <- M.constrs A;
  l <- M.map (fun d : dyn =>
    (* a constructor c has type (forall x, ... y, A) and we return
       (forall x, ... y, P (c x .. y)) *)
    t' <- copy_ctx P d;
    e <- M.Cevar t' ctx;
    M.ret {| elem := e |}) (snd l);
  let c := {| case_ind := A;
              case_val := n;
              case_return := {| elem := P |};
              case_branches := l
           |} in
  case <- M.makecase c;
  case <- M.unfold_projection (elem case);
  exact case g;;
  let res := dreduce (map, M.dyn_to_goal)
                     (map (fun d => (tt, M.dyn_to_goal d)) l) in
  M.ret res.

(** Destructs the n-th hypotheses in the goal (counting from 0) *)
Definition destructn (n : nat) : tactic :=
  bind (introsn n) (fun _ g =>
    A <- M.evar Type;
    n <- M.fresh_name "tmp";
    @intro_base A _ n destruct g).

Definition apply {T} (c : T) : tactic := fun g=>
  match g with Goal eg =>
    (mfix1 app (d : dyn) : M (list (unit * goal)) :=
      let (_, el) := d in
      mif M.unify_cumul el eg UniCoq then M.ret [] else
        mmatch d return M (list (unit * goal)) with
        | [? T1 T2 f] @Dyn (forall x:T1, T2 x) f =>
          e <- M.evar T1;
          r <- app (Dyn (f e));
          mif M.is_evar e then M.ret ((tt, Goal e) :: r) else M.ret r
        | _ =>
          gT <- M.goal_type g;
          M.raise (CantApply T gT)
        end) (Dyn c)
  | _ => M.raise NotAGoal
  end.

Definition change (P : Type) : tactic := fun g =>
  gT <- M.goal_type g;
  M.unify_or_fail P gT;;
  e <- M.evar P;
  exact e g;;
  M.ret [(tt, Goal e)].

Definition change_hyp {P Q} (H : P) (newH: Q) : tactic := fun g =>
  gT <- M.goal_type g;
  n <- M.get_binder_name H;
  f <- M.remove H (
    M.nu n None (fun H' : Q =>
      e <- M.evar gT;
      a <- M.abs_fun H' e;
      b <- M.abs_fun H' (Goal e);
      M.ret (a, b)));
  let (f, g') := f in
  M.unify_or_fail (Goal (f newH)) g;;
  M.ret [(tt, AHyp None g')].

Inductive goal_pattern (B : Type) :=
  | gbase : forall {A}, A -> gtactic B -> goal_pattern B
  | gtele : forall {C}, (C -> goal_pattern B) -> goal_pattern B
  | gtele_evar : forall {C}, (C -> goal_pattern B) -> goal_pattern B.
Arguments gbase {B A} _ _.
Arguments gtele {B C} _.
Arguments gtele_evar {B C} _.

Fixpoint match_goal_pattern' {B}
    (u : Unification) (p : goal_pattern B) : list Hyp -> list Hyp -> gtactic B :=
  fix go l1 l2 g :=
  match p, l2 with
  | gbase P t, _ =>
    gT <- M.goal_type g;
    mif M.unify_cumul P gT u then t g
    else M.raise DoesNotMatchGoal
  | @gtele _ C f, (@ahyp A a d :: l2') =>
    oeqCA <- M.unify C A u;
    match oeqCA with
    | Some eqCA =>
      let a' := rcbv match eq_sym eqCA with eq_refl => a end in
      mtry match_goal_pattern' u (f a') [] (List.rev_append l1 l2')%list g
      with DoesNotMatchGoal =>
        go (ahyp a d :: l1) l2' g
      end
    | None => go (ahyp a d :: l1) l2' g end
  | @gtele_evar _ C f, _ =>
    e <- M.evar C;
    match_goal_pattern' u (f e) l1 l2 g
  | _, _ => M.raise DoesNotMatchGoal
  end.

Definition match_goal_pattern {B} (u : Unification)
    (p : goal_pattern B) : gtactic B := fun g=>
  r <- M.hyps; match_goal_pattern' u p [] (List.rev' r) g.

Fixpoint match_goal_base {B} (u : Unification)
    (ps : list (goal_pattern B)) : gtactic B := fun g =>
  match ps with
  | [] => M.raise NoPatternMatchesGoal
  | p :: ps' =>
    mtry match_goal_pattern u p g
    with DoesNotMatchGoal => match_goal_base u ps' g end
  end.

Definition ltac (t : string) (args : list dyn) : tactic := fun g =>
  d <- M.goal_to_dyn g;
  let (ty, el) := d in
  v <- @M.call_ltac ty t args;
  let (v, l) := v in
  M.unify_or_fail v el;;
  b <- M.is_evar v;
  if b then
    M.ret [(tt, Goal v)] (* it wasn't solved *)
  else
    let l' := dreduce (@List.map) (map (pair tt) l) in
    M.ret l'.

Definition destruct_all (T : Type) : tactic := fun g=>
  l <- M.hyps;
  l <- M.filter (fun h : Hyp=>
    let (Th, _, _) := h in
    r <- M.unify Th T UniCoq;
    M.ret (option_to_bool r)) l;
  (fix f (l : list Hyp) : tactic :=
    match l with
    | [] => idtac
    | ahyp x _ :: l => bind (destruct x) (fun _ => f l)
    end) l g.

Definition treduce (r : Reduction) : tactic := fun g=>
  T <- M.goal_type g;
  let T' := reduce r T in
  e <- M.evar T';
  b <- M.unify_cumul g (@Goal T e) UniMatch;
  match b with
  | true => M.ret [(tt, Goal e)]
  | _ => M.failwith "It should never fail here"
  end.

Definition typed_intro (T : Type) : tactic := fun g =>
  U <- M.goal_type g;
  mmatch U with
  | [? P:T->Type] forall x:T, P x =>
    xn <- M.get_binder_name U;
    intro_simpl xn g
  | _ => M.raise NotThatType
  end.

Definition typed_intros (T : Type) : tactic := fun g =>
  (mfix1 f (g : goal) : M _ :=
    mtry bind (typed_intro T) (fun _ => f) g with
    | NotThatType => idtac g
    end) g.

Definition cpose_base {A B} (name : string) (t : A)
    (cont : A -> gtactic B) : gtactic B := fun g =>
  M.nu name (Some t) (fun x=>
    gT <- M.goal_type g;
    r <- M.evar gT;
    value <- M.abs_let x t r;
    exact value g;;
    cont x (Goal r) >>= let_close_goals x).

Definition cpose {A} (t: A) (cont : A -> tactic) : tactic := fun g =>
  n <- M.get_binder_name cont;
  cpose_base n t cont g.

Definition cassert_base {A} (name : string)
    (cont : A -> tactic) : tactic := fun g =>
  a <- M.evar A; (* [a] will be the goal to solve [A] *)
  M.nu name None (fun x =>
    gT <- M.goal_type g;
    r <- M.evar gT; (* The new goal now referring to n *)
    value <- M.abs_fun x r;
    exact (value a) g;; (* instantiate the old goal with the new one *)
    v <- cont x (Goal r) >>= close_goals x;
    M.ret ((tt,Goal a) :: v)). (* append the goal for a to the top of the goals *)

Definition cassert {A} (cont : A -> tactic) : tactic := fun g=>
  n <- M.get_binder_name cont;
  cassert_base n cont g.

(** [cut U] creates two goals with types [U -> T] and [U], where
    [T] is the type of the current goal. *)
Definition cut (U : Type) : tactic := fun g =>
  T <- M.goal_type g;
  ut <- M.evar (U -> T);
  u <- M.evar U;
  exact (ut u) g;;
  M.ret [(tt,Goal ut); (tt,Goal u)].

(* performs simpl in each hypothesis and in the goal *)
Definition simpl_in_all : tactic := fun g =>
  l <- M.hyps;
  l <- M.fold_right (fun (hyp : Hyp) hyps =>
    let (A, x, ot) := hyp in
    let A := rsimpl A in
    M.ret (@ahyp A x ot :: hyps)
  ) [] l;
  T <- M.goal_type g;
  let T := rsimpl T in
  e <- M.Cevar T l; (* create the new goal in the new context *)
  (* we need normal unification since g might be a compound value *)
  oeq <- M.unify g (Goal e) UniCoq;
  match oeq with
  | Some (eq_refl _) => M.ret [(tt,Goal e)]
  | _ => M.raise exception (* should never happen *)
  end.

Definition reduce_in (r : Reduction) {P} (H: P) : tactic := fun g =>
  l <- M.hyps;
  l' <- M.map (fun hyp : Hyp =>
    let (T, v, def) := hyp in
    mif M.unify_cumul H v UniMatchNoRed then
      let T' := reduce r T in M.ret (@ahyp T' v def)
    else M.ret hyp) l;
  gT <- M.goal_type g;
  e <- M.Cevar gT l';
  oeq <- M.unify (Goal e) g UniCoq;
  match oeq with
  | Some (eq_refl _) => M.ret [(tt,Goal e)]
  | _ => M.raise exception (* should never happen *)
  end.

Definition simpl_in {P} (H: P) : tactic :=
  reduce_in RedSimpl H.

(** exists tactic *)
Definition mexists {A} (x: A) : tactic := fun g =>
  P <- M.evar _;
  e <- M.evar _;
  oeq <- M.unify g (Goal (@ex_intro _ P x e)) UniCoq;
  match oeq with
  | Some (eq_refl _) => M.ret [(tt,Goal e)]
  | _ => M.raise (NotUnifiable g (Goal (@ex_intro _ P x e)))
  end.

(** Printing of a goal *)
Definition print_hyp (a : Hyp) : M unit :=
  let (A, x, ot) := a in
  sA <- M.pretty_print A;
  sx <- M.pretty_print x;
  match ot with
  | Some t =>
    st <- M.pretty_print t;
    M.print (sx ++ " := " ++ st ++ " : " ++ sA)
  | None => M.print (sx ++ " : " ++ sA)
  end.

Definition print_hyps : M unit :=
  l <- M.hyps;
  let l := rev' l in
  M.iterate print_hyp l.

Definition print_goal : tactic := fun g =>
  let repeat c := (fix repeat s n :=
    match n with
    | 0 => s
    | S n => repeat (c++s)%string n
    end) ""%string in
  G <- M.goal_type g;
  sg <- M.pretty_print G;
  let sep := repeat "="%string 20 in
  print_hyps;;
  M.print sep;;
  M.print sg;;
  idtac g.

(** [n_etas n f] takes a function f with type [forall x1, ..., xn, T]
    and returns its eta-expansion: [fun x1, ..., xn=>f x1 .. xn].
    Raises [NotAProduct] if there aren't that many absractions. *)
Definition n_etas (n : nat) {A} (f : A) : M A :=
  (fix loop (n : nat) (d : dyn) : M (type d) :=
    match n with
    | 0 =>
      (* we remove the wrapper of the element in [d] *)
      M.unfold_projection (elem d)
    | S n' =>
       mmatch d with
       | [? B (T:B->Type) f] @Dyn (forall x:B, T x) f =>
         ty <- M.unfold_projection (type d);
         name <- M.get_binder_name ty;
         M.nu name None (fun x:B =>
           loop n' (Dyn (f x)) >>= M.abs_fun x
         )
       | _ => M.raise NotAProduct
       end
    end) n (Dyn f).

(** [fix_tac f n] is like Coq's [fix] tactic: it generates a fixpoint
    with a new goal as body, containing a variable named [f] with
    the current goal as type. The goal is expected to have at least
    [n] products. *)
Definition fix_tac (f : string) (n : N) : tactic := fun g =>
  gT <- M.goal_type g;
  r <- M.nu f None (fun f : gT=>
    (* We introduce the recursive definition f and create the new
       goal having it. *)
    new_goal <- M.evar gT;
    (* We need to enclose the body with n-abstractions as
     required by the fix operator. *)
    fixp <- n_etas (N.to_nat n) new_goal;
    fixp <- M.abs_fix f fixp n;
    (* fixp is now the fixpoint with the evar as body *)
    (* The new goal is enclosed with the definition of f *)
    new_goal <- M.abs_fun f (Goal new_goal);
    M.ret (fixp, AHyp None new_goal)
  );
  let (f, new_goal) := r in
  exact f g;;
  M.ret [(tt,new_goal)].

(** [repeat t] applies tactic [t] to the goal several times
    (it should only generate at most 1 subgoal), until no
    changes or no goal is left. *)
Definition repeat (t : tactic) : tactic := fun g =>
  (mfix1 f (g : goal) : M (list (unit * goal)) :=
    r <- try t g; (* if it fails, the execution will stop below *)
    match r with
    | [] => M.ret []
    | [(_,g')] =>
      mmatch g with
      | g' => M.ret [(tt,g)] (* the goal is the same, return *)
      | _ => f g'
      end
    | _ => M.print_term r;; M.failwith "The tactic generated more than a goal"
    end) g.

Definition map_term (f : forall d:dyn, M d.(type)) : forall d : dyn, M d.(type) :=
  mfix1 rec (d : dyn) : M d.(type) :=
    let (ty, el) := d in
    mmatch d as d return M d.(type) with
    | [? B A (b: B) (a: B -> A)] Dyn (a b) =n>
      d1 <- rec (Dyn a);
      d2 <- rec (Dyn b);
      M.ret (d1 d2)
    | [? B (A: B -> Type) (a: forall x, A x)] Dyn (fun x:B=>a x) =n>
      n <- M.get_binder_name el;
      M.nu n None (fun x : B =>
        d1 <- rec (Dyn (a x));
        M.abs_fun x d1)
    | [? B (A: B -> Type) a] Dyn (forall x:B, a x) =n>
      n <- M.get_binder_name el;
      M.nu n None (fun x : B =>
        d1 <- rec (Dyn (a x));
        M.abs_prod x d1)
    | [? d'] d' =n> f d'
    end.

Definition unfold_slow {A} (x : A) : tactic := fun g =>
  let def := rone_step x in
  gT <- M.goal_type g;
  gT' <- map_term (fun d =>
    let (ty, el) := d in
    mmatch d as d return M d.(type) with
    | Dyn x =n> M.ret def
    | [? A (d': A)] Dyn d' =n> M.ret d'
    end) (Dyn gT);
  e <- M.evar gT';
  exact e g;;
  M.ret [(tt,Goal e)].

Definition unfold {A} (x : A) : tactic := fun g =>
  gT <- M.goal_type g;
  let gT' := dreduce (x) gT in
  ng <- M.evar gT';
  exact ng g;;
  M.ret [(tt, Goal ng)].

Definition unfold_in {A B} (x : A) (h : B) : tactic :=
  reduce_in (RedStrong [RedBeta; RedMatch; RedFix; RedDeltaOnly [Dyn x]]) h.

Fixpoint intros_simpl (l : list string) : tactic :=
  match l with
  | [] => idtac
  | n :: l => bind (intro_simpl n) (fun _ => intros_simpl l)
  end.

Fixpoint name_pattern (l : list (list string)) : list tactic :=
  match l with
  | [] => []
  | ns :: l => intros_simpl ns :: name_pattern l
  end.

(** Type for goal manipulation primitives *)
Definition selector := list (unit * goal) -> M (list (unit * goal)).

Definition tactic_selector (t: tactic) (s: selector) : tactic := fun g =>
  l <- t g;
  filter_goals l >>= s.

Module S.
  Definition nth (n : nat) (t : tactic) : selector := fun l =>
    let (l1, l2) := dreduce (@nsplit) (nsplit n l) in
    match hd_error l2 with
    | None => M.raise NoGoalsLeft
    | Some (_, g) =>
      goals <- open_and_apply t g;
      let res := dreduce (@List.app, @List.tail) (l1 ++ goals ++ tail l2)%list in
      M.ret res
    end.

  Definition last (t : tactic) : selector := fun l =>
    let n := dreduce (pred, List.length) (pred (List.length l)) in
    nth n t l.

  Definition first (t : tactic) : selector := nth 0 t.

  Definition rev : selector := fun l =>
    let res := dreduce (rev', rev_append, app) (rev' l) in M.ret res.
End S.

Module notations.
  Open Scope tactic_scope.

  (* This notation makes sure that [t] is in [MC] scope ands casts the resulting
  lambda into a [tactic] to make sure that it can be ran. *)
  Notation "\tactic g => t" :=
    ((fun g => t%MC) : tactic) (at level 200, g at level 0, right associativity).

  Notation "r '<-' t1 ';' t2" := (bind t1 (fun r => t2%tactic))
    (at level 81, right associativity, format "'[' r  '<-'  '[' t1 ;  ']' ']' '/' t2 ") : tactic_scope.
  Notation "t1 ';;' t2" := (bind t1 (fun _=>t2%tactic))
    (at level 81, right associativity, format "'[' '[' t1 ;;  ']' ']' '/' t2 ") : tactic_scope.
  Notation "t >>= f" := (bind t f) (at level 70) : tactic_scope.

  Notation "'mif' b 'then' t 'else' u" :=
    (cond <- b; if cond then t else u) (at level 200) : tactic_scope.

  Notation "'mfix0' f : 'gtactic' T := b" :=
    (fix0 T%type (fun f => b%tactic))
    (at level 85, f at level 0, format
    "'[v  ' 'mfix0'  f  ':'  'gtactic'  T  ':=' '/  ' b ']'") : tactic_scope.

  Notation "'mfix1' f ( x : A ) : 'gtactic' T := b" :=
    (fix1 (fun x=>T%type) (fun f (x : A)=>b%tactic))
    (at level 85, f at level 0, x at next level, format
    "'[v  ' 'mfix1'  f  '(' x  ':'  A ')'  ':'  'gtactic'  T  ':=' '/  ' b ']'") : tactic_scope.

  Notation "'mfix2' f ( x : A ) ( y : B ) : 'gtactic' T := b" :=
    (fix2 (fun (x : A) (y : B)=>T%type) (fun f (x : A) (y : B)=>b%tactic))
    (at level 85, f at level 0, x at next level, y at next level, format
    "'[v  ' 'mfix2'  f  '(' x  ':'  A ')'  '(' y  ':'  B ')'  ':'  'gtactic'  T  ':=' '/  ' b ']'") : tactic_scope.

  Notation "'mfix3' f ( x : A ) ( y : B ) ( z : C ) : 'gtactic' T := b" :=
    (fix3 (fun (x : A) (y : B) (z : C)=>T%type) (fun f (x : A) (y : B) (z : C)=>b%tactic))
    (at level 85, f at level 0, x at next level, y at next level, z at next level, format
    "'[v  ' 'mfix3'  f  '(' x  ':'  A ')'  '(' y  ':'  B ')'  '(' z  ':'  C ')'  ':'  'gtactic'  T  ':=' '/  ' b ']'") : tactic_scope.

  Notation "'mfix4' f ( x1 : A1 ) ( x2 : A2 ) ( x3 : A3 ) ( x4 : A4 ) : 'gtactic' T := b" :=
    (fix4 (fun (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4)=>T%type) (fun f (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4) =>b%tactic))
    (at level 85, f at level 0, x1 at next level, x2 at next level, x3 at next level, x4 at next level, format
    "'[v  ' 'mfix4'  f  '(' x1  ':'  A1 ')'  '(' x2  ':'  A2 ')'  '(' x3  ':'  A3 ')'  '(' x4  ':'  A4 ')'  ':'  'gtactic'  T  ':=' '/  ' b ']'") : tactic_scope.

  Notation "'mmatch' x ls" :=
    (@mmatch' _ (fun _ => _) x ls%with_pattern)
    (at level 90, ls at level 91) : tactic_scope.
  Notation "'mmatch' x 'return' 'gtactic' p ls" :=
    (@mmatch' _ (fun x => p%type) x ls%with_pattern)
    (at level 90, ls at level 91) : tactic_scope.
  Notation "'mmatch' x 'as' y 'return' 'gtactic' p ls" :=
    (@mmatch' _ (fun y => p%type) x ls%with_pattern)
    (at level 90, ls at level 91) : tactic_scope.

  Notation "'mtry' a ls" :=
    (mtry' a (fun e =>
      (@mmatch' _ (fun _ => _) e
                   (app ls%with_pattern [([? x] x => raise x)%pattern]))))
      (at level 82, a at level 100, ls at level 91, only parsing) : tactic_scope.

  Notation "t 'or' u" := (or t u) (at level 50) : tactic_scope.

  (* We need a fresh evar to be able to use intro with ;; *)
  Notation "'intro' x" :=
    (T <- M.evar Type; @intro_cont T _ (fun x=>idtac))
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
    (bind_list t (name_pattern n)) (at level 40) : tactic_scope.

  Notation "[[ |- ps ] ] => t" :=
    (gbase ps t)
    (at level 202, ps at next level) : match_goal_pattern_scope.

  Notation "[[? a .. b | x .. y |- ps ] ] => t" :=
    (gtele_evar (fun a => .. (gtele_evar (fun b =>
       gtele (fun x => .. (gtele (fun y => gbase ps t)).. ))).. ))
    (at level 202, a binder, b binder,
     x binder, y binder, ps at next level) : match_goal_pattern_scope.

  Notation "[[? a .. b |- ps ] ] => t" :=
    (gtele_evar (fun a => .. (gtele_evar (fun b => gbase ps t)).. ))
    (at level 202, a binder, b binder, ps at next level) : match_goal_pattern_scope.

  Notation "[[ x .. y |- ps ] ] => t" :=
    (gtele (fun x => .. (gtele (fun y => gbase ps t)).. ))
    (at level 202, x binder, y binder, ps at next level) : match_goal_pattern_scope.

  Delimit Scope match_goal_pattern_scope with match_goal_pattern.

  Notation "'with' | p1 | .. | pn 'end'" :=
    ((@cons (goal_pattern _) p1%match_goal_pattern (.. (@cons (goal_pattern _) pn%match_goal_pattern nil) ..)))
      (at level 91, p1 at level 210, pn at level 210) : match_goal_with_scope.
  Notation "'with' p1 | .. | pn 'end'" :=
    ((@cons (goal_pattern _) p1%match_goal_pattern (.. (@cons (goal_pattern _) pn%match_goal_pattern nil) ..)))
      (at level 91, p1 at level 210, pn at level 210) : match_goal_with_scope.

  Delimit Scope match_goal_with_scope with match_goal_with.

  Notation "'match_goal' ls" := (match_goal_base UniCoq ls%match_goal_with)
    (at level 90, ls at level 91) : tactic_scope.
  Notation "'match_goal_nored' ls" := (match_goal_base UniMatchNoRed ls%match_goal_with)
    (at level 90, ls at level 91) : tactic_scope.

  Notation "t1 '&>' ts" :=
    (bind_list t1 ts) (at level 41, left associativity) : tactic_scope.
  Notation "t1 '|1>' t2" :=
    (tactic_selector t1 (S.nth 0 t2))
    (at level 41, left associativity, t2 at level 100) : tactic_scope.
  Notation "t1 '|2>' t2" :=
    (tactic_selector t1 (S.nth 1 t2))
    (at level 41, left associativity, t2 at level 100) : tactic_scope.
  Notation "t1 '|3>' t2" :=
    (tactic_selector t1 (S.nth 2 t2))
    (at level 41, left associativity, t2 at level 100) : tactic_scope.
  Notation "t1 '|4>' t2" :=
    (tactic_selector t1 (S.nth 3 t2))
    (at level 41, left associativity, t2 at level 100) : tactic_scope.
  Notation "t1 '|5>' t2" :=
    (tactic_selector t1 (S.nth 4 t2))
    (at level 41, left associativity, t2 at level 100) : tactic_scope.
  Notation "t1 '|6>' t2" :=
    (tactic_selector t1 (S.nth 5 t2))
    (at level 41, left associativity, t2 at level 100) : tactic_scope.

  Notation "t1 'l>' t2" :=
    (t1 &> S.last t2)
    (at level 41, left associativity, t2 at level 100) : tactic_scope.
End notations.

Import notations.

(* Some derived tactics *)
Definition apply_in {P Q} (c : P -> Q) (H : P) : tactic :=
  change_hyp H (c H).

Definition transitivity {B} (y : B) : tactic :=
  apply (fun x => @eq_trans B x y).

Definition symmetry : tactic :=
  apply eq_sym.

Definition exfalso : tactic :=
  apply False_ind.

Definition constructor (n : nat) : tactic :=
  A <- goal_type;
  match n with
  | 0 => M.raise ConstructorsStartsFrom1
  | S n =>
    l <- M.constrs A;
    match nth_error (snd l) n with
    | Some (@Dyn A x) => apply x
    | None => raise CantFindConstructor
    end
  end.

Definition split : tactic :=
  A <- goal_type;
  l <- M.constrs A;
  match snd l with
  | [_] => constructor 1
  | _ => raise Not1Constructor
  end.

Definition left : tactic :=
  A <- goal_type;
  l <- M.constrs A;
  match snd l with
  | [Dyn x; _] => apply x
  | _ => raise Not2Constructor
  end.

Definition right : tactic :=
  A <- goal_type;
  l <- M.constrs A;
  match snd l with
  | [_; Dyn x] => apply x
  | _ => raise Not2Constructor
  end.

Definition assumption : tactic :=
  A <- goal_type;
  match_goal with [[ x : A |- A ]] => exact x end.

(** Given a type [T] it searches for a hypothesis with that type and
    executes the [cont]inuation on it.  *)
Definition select (T : Type) (cont : T -> tactic) : tactic :=
  A <- goal_type;
  match_goal with [[ x : T |- A ]] => cont x end.

(** generalize with clear *)
Definition move_back {A} (x : A) (cont : tactic) : tactic :=
  generalize x ;; cclear x cont.
End T.
