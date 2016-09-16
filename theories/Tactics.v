Require Import Strings.String.
From MetaCoq Require Export Mtac.
Require Import MetaCoq.ListUtils.
Require Import Lists.List.
Import MtacNotations.
Import ListNotations.

Require Import Strings.String.

Local Set Universe Polymorphism.

Definition CantCoerce : Exception. exact exception. Qed.

Definition coerce {A B : Type} (x : A) : M B :=
  oH <- munify A B UniCoq;
  match oH with
  | Some H => match H with eq_refl => ret x end
  | _ => raise CantCoerce
  end.

Definition tactic := (goal -> M (list goal)).

Definition run_tac {P} (t : tactic) : M P :=
  e <- evar P;
  t (TheGoal e);;
  ret e.

Definition NotAGoal : Exception. exact exception. Qed.
Definition goal_type g : M Type :=
  match g with
    | @TheGoal A _ => ret A
    | _ => raise NotAGoal
  end.

Definition dyn_to_goal d :=
  match d with
  | Dyn x => TheGoal x
  end.

Definition goal_to_dyn : goal -> M dyn := fun g =>
  match g with
  | TheGoal d => ret (Dyn d)
  | _ => raise NotAGoal
  end.

Definition idtac : tactic := fun g => ret [g].

Definition fail (e : Exception) : tactic := fun g=>raise e.

Definition unify_or_fail {A} (x y : A) : M (x = y) :=
  oeq <- munify x y UniCoq;
  match oeq with
  | None => raise (NotUnifiable x y)
  | Some eq=> ret eq
  end.

Definition exact {A} (x:A) : tactic := fun g=>
  unify_or_fail (TheGoal x) g;; ret nil.

Definition try (t:tactic) : tactic := fun g=>
  mtry t g with _ => ret ( g :: nil) end.

Definition or (t u : tactic) : tactic := fun g=>
  mtry t g with _ => u g end.

Definition close_goals {A} (x:A) : list goal -> M (list goal) :=
  mmap (fun g'=>r <- abs x g'; ret (@AHyp A None r)).

Definition NotAnEvar {A} (x: A) : Exception. exact exception. Qed.
Definition CantInstantiate {A} (x t: A) : Exception. exact exception. Qed.

Definition decompose {A} (x: A) :=
  (mfix2 f (d : dyn) (args: list dyn) : M (dyn * list dyn)%type :=
    mmatch d with
    | [? A B (t1: forall x:A, B x) t2] Dyn (t1 t2) => f (Dyn t1) (Dyn t2 :: args)
    | _ => ret (d, args)
    end) (Dyn x) [].

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

Definition intro_cont {A} (t: A->tactic) : tactic := fun g=>
  mmatch g return M list goal with
  | [? B (P:B -> Type) e] @TheGoal (forall x:B, P x) e =>
    (* We can't put A as the type of the product domain, since it
    might be an evar, and it won't be instantiated (patterns do not
    instantiate foreign evars). Therefore, we unify it here. *)
    eq <- unify_or_fail B A;
    n <- get_binder_name t;
    tnu n None (fun x=>
      let Px := reduce (RedWhd [RedBeta]) (P x) in
      e' <- evar Px;
      g <- abs (P:=P) x e';
      instantiate e g;;
      let x := reduce (RedWhd [RedIota]) (match eq in _ = x with
                 | eq_refl => x
               end) in
      t x (TheGoal e') >> close_goals x)
  | _ => raise NotAProduct
  end.

(** Given a name of a variable, it introduces it in the context *)
Definition intro_simpl (var: string) : tactic := fun g=>
  mmatch g with
  | [? B t (P:B -> Type) e] @TheGoal (let x := t in P x) e =>
    tnu var (Some t) (fun x=>
      let Px := reduce (RedWhd [RedBeta]) (P x) in
      e' <- evar Px;
      g <- abs_let (P:=P) x t e';
      instantiate e g;;
      g' <- abs x (TheGoal e');
      ret [AHyp (Some t) g'])

  | [? B (P:B -> Type) e] @TheGoal (forall x:B, P x) e =>
    tnu var None (fun x=>
      let Px := reduce (RedWhd [RedBeta]) (P x) in
      e' <- evar Px;
      g <- abs (P:=P) x e';
      instantiate e g;;
      g' <- abs x (TheGoal e');
      ret [AHyp None g'])

  | _ => raise NotAProduct
  end.

Fixpoint is_open (g : goal) : M bool :=
  match g with
  | TheGoal e => is_evar e
  | @AHyp C _ f =>
    x <- get_binder_name f;
    tnu x None (fun x : C=>is_open (f x))
  end.

Definition filter_goals : list goal -> M (list goal) := mfilter is_open.

Definition let_close_goals {A} (x: A) (t: A) : list goal -> M (list goal) :=
  let t := rone_step x in (* to obtain x's definition *)
  mmap (fun g':goal=>
          r <- abs x g';
          ret (@AHyp A (Some t) r)
       ).

Definition open_and_apply (t : tactic) : tactic := fix open g :=
    match g return M _ with
    | TheGoal _ => t g
    | @AHyp C None f =>
      x <- get_binder_name f;
      tnu x None (fun x : C=>
        open (f x) >> close_goals x)
    | @AHyp C (Some t) f =>
      x <- get_binder_name f;
      tnu x (Some t) (fun x : C=>
        open (f x) >> let_close_goals x t)
    end.

Definition intros_all : tactic :=
  mfix1 f (g : goal) : M (list goal) :=
    open_and_apply (fun g =>
      mmatch g return M list goal with
      | [? T e] @TheGoal T e =>
        mtry
          xn <- get_binder_name T;
          r <- intro_simpl xn g;
          g <- hd_exception r;
          f g
        with WrongTerm =>
          ret [g]
        | NotAProduct =>
          ret [g]
        end
      end) g.

(** Introduces up to n binders. Throws [NotAProduct] if there
    aren't enough products in the goal.  *)
Definition introsn : nat -> tactic :=
  mfix2 f (n : nat) (g : goal) : M (list goal) :=
    open_and_apply (fun g =>
      match (n, g) with
      | (0, g) => ret [g]
      | (S n', @TheGoal T e) =>
        mtry
          xn <- get_binder_name T;
          r <- intro_simpl xn g;
          g <- hd_exception r;
          f n' g
        with WrongTerm => raise NotAProduct end
      | (_, _) => failwith "Should never get here"
      end) g.

Definition prim_reflexivity : tactic := fun g=>
  A <- evar Type;
  x <- evar A;
  unify_or_fail g (TheGoal (eq_refl x));; ret nil.

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

Definition bbind (t:tactic) (l:list tactic) : tactic := fun g=>
  l' <- t g;
  l' <- filter_goals l';
  ls <- gmap l l';
  ret (concat ls).

Definition bindb (t u:tactic) : tactic := fun g=>
  l <- t g;
  l <- filter_goals l;
  r <- mmap (open_and_apply u) l;
  let r := rhnf List.concat _ r in
  ret r.

(* Polymorphic CS are broken *)
Monomorphic Structure semicolon (left_type compose_type : Type) := SemiColon {
  right_type : Type;
  the_value : left_type -> right_type -> compose_type
}.
Arguments SemiColon {_ _ _} _.
Arguments the_value {_ _ _ _ _}.

Monomorphic Canonical Structure semicolon_tactic_tactics := SemiColon bbind.

(* Polymorphic CS are broken *)
Monomorphic Structure mtac_or_tactic := MtacOrTactic {
  left_type : Type;
  mtac_or_tactic_bind : left_type -> tactic -> tactic
}.
Monomorphic Canonical Structure semicolon_mtac_tactic A :=
  MtacOrTactic (M A) (fun a t g=>a;; t g).
Monomorphic Canonical Structure semicolon_tactic_tactic :=
  MtacOrTactic tactic bindb.

Monomorphic Canonical Structure semicolon_x_tactic (g : mtac_or_tactic) :=
  SemiColon (mtac_or_tactic_bind g).

Monomorphic Definition the_mtac_bind A B := (fun a b=>@bind A B a (fun _ => b)).
Monomorphic Canonical Structure semicolon_mtac_mtac A B := SemiColon (the_mtac_bind A B).

(** Overloaded binding *)
(* Polymorphic CS are broken *)
Monomorphic Structure binding  (left_type middle_type compose_type : Type) := Binding {
  bright_type : Type;
  the_bvalue : left_type -> (middle_type -> bright_type) -> compose_type }.
Arguments Binding {_ _ _ _} _.
Arguments the_bvalue {_ _ _ _ _ _}.

Monomorphic Canonical Structure binding_mtac A B := Binding (@bind A B).

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
        tnu n None (fun y=>
          r <- rec (Dyn (c y));
          abs_prod y r)
    | [? C D (c : C->D)] Dyn c =>
        n <- fresh_binder_name c;
        tnu n None (fun y=>
          r <- rec (Dyn (c y));
          abs_prod y r)
    | _ => print_term A;; raise (SomethingNotRight d)
    end.

Definition hyps_except {A} (x : A) :=
  l <- hypotheses;
  mfilter (fun y=>mmatch y with
    | [? b] ahyp x b => ret false
    | _ => ret true
    end) l.

Definition find_hyp_index {A} (x : A) :=
  l <- hypotheses;
  mindex_of (fun y=>mmatch y with
    | [? b] ahyp x b => ret true
    | _ => ret false
    end) l.

Definition type_of {A} (x:A) := A.

Fixpoint but_last {A} (l : list A) :=
  match l with
  | [] => []
  | [a] => []
  | (a :: ls) => a :: but_last ls
  end.

Definition generalize1 (cont: tactic) : tactic := fun g=>
  P <- goal_type g;
  l <- hypotheses;
  ft <- hd_exception l;
  let (A, x, _) := ft in
  aP <- abs_prod x P; (* aP = (forall x:A, P) *)
  e <- Cevar aP (tl l);
  mmatch aP with
  | [? Q : A -> Type] (forall z:A, Q z) => [H]
    let e' := match H in _ = Q return Q with
      | eq_refl _ => e
      end
    in
    oeq <- munify g (@TheGoal (Q x) (e' x)) UniCoq;
    match oeq with
    | Some _ => Mtac.remove x (cont (TheGoal e))
    | _ => raise exception
    end
  | _ => raise exception
  end.

(* if I have a goal (P; ?e) and a number n, I want to
   create a new goal (forall x_1, ..., x_n=>P; ?e')
   so ?e should be instantiated with ?e' x_1 ... x_n *)
(*
Definition abstract_up_to n : tactic := fun g=>
  l <- hypotheses;
  P <- goal_type g;
  pP <- productify_up_to (Dyn P) n l;
  let l' := rhnf (skipn n l) in
  e <- Cevar pP l';
*)

Definition cprint {A} (s: string) (c: A) :=
  x <- pretty_print c;
  let s := reduce RedNF (s++x)%string in
  print s.

Notation reduce_novars := (reduce (RedStrong [RedBeta;RedIota;RedDeltaC;RedZeta])).

Definition destruct {A : Type} (n : A) : tactic := fun g=>
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
              case_type := Pn;
              case_return := {| elem := P |};
              case_branches := l
           |} in
  d <- makecase c;
  d <- coerce (elem d);
  let d := rhnf d in
  unify_or_fail (@TheGoal Pn d) g;;
  let l := rhnf (List.map dyn_to_goal l) in
  ret l.

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
  (mfix1 app (d : dyn) : M (list goal) :=
    let (_, el) := d in
    oeq <- munify (TheGoal el) g UniCoq;
    match oeq with
    | Some _ => ret []
    | None =>
      mmatch d return M (list goal) with
      | [? T1 T2 f] @Dyn (forall x:T1, T2 x) f =>
          e <- evar T1;
          r <- app (Dyn (f e));
          ret (TheGoal e :: r)
      | _ =>
          gT <- goal_type g;
          raise (CantApply c gT)
      end
    end
  ) (Dyn c).

Definition transitivity {B : Type} (y : B) : tactic :=
  apply (fun x => @eq_trans B x y).

Definition symmetry : tactic :=
  apply eq_sym.

Definition CantFindConstructor : Exception. exact exception. Qed.
Definition ConstructorsStartsFrom1 : Exception. exact exception. Qed.

Definition constructor (n : nat) : tactic := fun g=>
  A <- goal_type g;
  match n with
  | 0 => raise ConstructorsStartsFrom1
  | S n =>
      l <- constrs A;
      match nth_error (snd l) n with
        | Some x => apply (elem x) g
        | None => fail CantFindConstructor g
      end
  end.

Definition Not1Constructor : Exception. exact exception. Qed.

Definition split : tactic := fun g=>
  A <- goal_type g;
  l <- constrs A;
  match snd l with
  | [_] =>  constructor 1 g
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

(* Monomorphic*) Fixpoint match_goal' (p : goal_pattern) (l : list Hyp) : tactic := fun g=>
  match p, l with
  | gbase P t, _ =>
    gty <- goal_type g;
    beq <- munify_cumul P gty UniCoq;
    if beq then t g
    else fail DoesNotMatchGoal g
  | @gtele C f, (@ahyp A a _ :: l) =>
    teq <- munify C A UniCoq;
    match teq with
    | Some eq =>
      e <- evar C;
      let e' := match eq with eq_refl => e end in
      munify e' a UniCoq;;
      mtry match_goal' (f e) l g
      with DoesNotMatchGoal =>
        match_goal' p l g
      end
    | None => match_goal' p l g end
  | _, _ => raise DoesNotMatchGoal
  end.

Definition match_goal p : tactic := fun g=>
  r <- hypotheses; let r := rsimpl (List.rev r) in match_goal' p r g.

Definition ltac (t : string) (args : list dyn) : tactic := fun g=>
  d <- goal_to_dyn g;
  let (ty, el) := d in
  v <- @call_ltac ty t args;
  let (v, l) := v in
  unify_or_fail v el;;
  b <- is_evar v;
  if b then
    ret [TheGoal v] (* it wasn't solved *)
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
    | (ahyp x _ :: l) => bindb (destruct x) (f l)
    end) l g.

Definition treduce (r : Reduction) : tactic := fun g=>
  T <- goal_type g;
  let T := reduce r T in
  e <- evar T;
  let e := TheGoal e in
  munify g e UniMatch;;
  ret [e].

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
      (bindb (typed_intro T) f) g
    with NotThatType =>
      idtac g
    end) g.

Definition cpose {A} (t: A) (cont: A -> tactic) : tactic := fun g=>
  n <- get_binder_name cont;
  tnu n (Some t) (fun x=>
    match g with
    | @TheGoal T e =>
      r <- evar T;
      value <- abs_let x t r;
      instantiate e value;;
      cont x (TheGoal r) >> let_close_goals x t
    | _ => raise NotAGoal
    end).

(* It isn't quite right, it's making a transparent binding instead of an opaque one *)
Definition cassert {A} (cont: A -> tactic) : tactic := fun g=>
  a <- evar A; (* [a] will be the goal to solve [A] *)
  n <- get_binder_name cont;
  tnu n None (fun x=>
    match g with
    | @TheGoal T e =>
      r <- evar T; (* The new goal now referring to n *)
      value <- abs x r;
      instantiate e (value a);; (* instantiate the old goal with the new one *)
      v <- cont x (TheGoal r) >> close_goals x;
      ret (TheGoal a :: v) (* append the goal for a to the top of the goals *)
    | _ => raise NotAGoal
    end).

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
  oeq <- munify g (TheGoal e) UniCoq;
  match oeq with
  | Some (eq_refl _) => ret [TheGoal e]
  | _ => raise exception (* should never happen *)
  end.

(** exists tactic *)
Definition mexists {A} (x: A) : tactic := fun g=>
  P <- evar _;
  e <- evar _;
  oeq <- munify g (TheGoal (@ex_intro _ P x e)) UniCoq;
  match oeq with
  | Some (eq_refl _) => ret [TheGoal e]
  | _ => raise (NotUnifiable g (TheGoal (@ex_intro _ P x e)))
  end.

(** Printing of a goal *)
Require Import Strings.String.

Definition print_hypothesis (a:Hyp) :=
  let (A, x, ot) := a in
  sA <- pretty_print A;
  sx <- pretty_print x;
  match ot with
  | Some t =>
    st <- pretty_print t;
    print (sx ++ " := " ++ st ++ " : " ++ sA)
  | None => print (sx ++ " : " ++ sA)
  end.

Definition print_hypotheses :=
  l <- hypotheses;
  let l := rev l in
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
         tnu name None (fun x:B =>
           loop n' (Dyn (f x)) >> abs x
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
Definition fix_tac f n : tactic := fun g=>
  G <- goal_to_dyn g;
  let (G, e) := G in
  r <- tnu f None (fun f:G=>
    (* We introduce the recursive definition f and create the new
       goal having it. *)
    new_goal <- evar G;
    (* We need to enclose the body with n-abstractions as
     required by the fix operator. *)
    fixp <- n_etas (S (N.to_nat n)) new_goal;
    fixp <- abs_fix f fixp n;
    (* fixp is now the fixpoint with the evar as body *)
    (* The new goal is enclosed with the definition of f *)
    new_goal <- abs f (TheGoal new_goal);
    ret (fixp, AHyp None new_goal)
  );
  let (f, new_goal) := r in
  instantiate e f;;
  ret [new_goal].

(** [repeat t] applies tactic [t] to the goal several times
    (it should only generate at most 1 subgoal), until no
    changes or no goal is left. *)
Definition repeat t : tactic := fun g=>
  (mfix1 f (g : goal) : M (list goal) :=
    r <- try t g; (* if it fails, the execution will stop below *)
    r <- filter_goals r;
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

(** WIP
Definition unfold_projection {A} (t : A) : M A :=
  d <- decompose t;
  let (hd, args) := d in
  let (ty, el) := hd in
  let unf_el := rone_step el in
  let red_el := RedWhd [RedIota; RedBeta] unf_el in
  repack red_el args.

Definition map_term (f : forall d:dyn, M d.(type)) :=
  mfix1 rec (d : dyn) : M d.(type) :=
    let (ty, el) := d in
    bvar <- is_var el;
    bevar <- is_evar el;
    btype <- is_prop_or_type d;
    if bvar || bevar || btype then
      f d
    else
      mmatch d as d return M d.(type) with
      | [? B A (b: B) (a: B -> A)] Dyn (a b) =>
        d1 <- rec (Dyn a);
        d2 <- rec (Dyn b);
        val <- coerce (d1 d2);
        ret val
      | [? B (A: B -> Type) (b: B) (a: forall x, A x)] Dyn (a b) =>
        d1 <- rec (Dyn a);
        d2 <- rec (Dyn b);
        val <- coerce (d1 d2);
        ret val
      | [? B (A: B -> Type) (a: forall x, A x)] Dyn (fun x:B=>a x) =>
        n <- get_binder_name el;
        tnu n None (fun x:B=>
          d1 <- rec (Dyn (a x));
          abs x d1)
      | [? d'] d' => f d'
      end.

Example map_term_id : Prop.
MProof.
  m <- map_term
  (fun d=>
   print_term d;;
   b <- is_evar d.(elem);
   if b then
     mmatch d as d return M d.(type) with
     | [? x] @Dyn nat x => ret 0
     | [? d'] d' => ret d'.(elem)
     end
   else
     ret d.(elem)
  ) (Dyn (_ + _ + _ = 0));
  _ <- print_term m; ret m.
ret 1. ret 1. ret 1.
Defined.
*)

Monomorphic Fixpoint intros_simpl (l: list string) : tactic :=
  match l with
  | [] => idtac
  | (n :: l) => bindb (intro_simpl n) (intros_simpl l)
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
          let v' := reduce (RedWhd [RedIota]) match eq' as x in _ = x with eq_refl=> v end in
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

Notation "t 'asp' n" := (bbind t (name_pattern n)) (at level 40).

Notation "[[ |- ps ] ] => t" :=
  (gbase ps t)
  (at level 202, ps at next level) : goal_match_scope.

Notation "[[ x .. y |- ps ] ] => t" :=
  (gtele (fun x=> .. (gtele (fun y=>gbase ps t)).. ))
  (at level 202, x binder, y binder, ps at next level) : goal_match_scope.
Delimit Scope goal_match_scope with goal_match.

Arguments match_goal _%goal_match _.

Notation "t 'where' m := u" := (elem (ltac:(mrun (v <- mwith t m u; ret v)))) (at level 0).
End TacticsNotations.

Module TacticOverload.
Notation "a ;; b" := (the_value a b).

Notation "r '<-' t1 ';' t2" := (the_bvalue t1 (fun r=>t2)).
End TacticOverload.

Import TacticsNotations.

Definition assumption : tactic := fun g=>
  P <- goal_type g;
  match_goal ([[ x:P |- P ]] => exact x) g.

(** Given a type [T] it searches for a hypothesis with that type and
    executes the [cont]inuation on it.  *)
Definition select T (cont: T -> tactic) : tactic := fun g=>
  G <- goal_type g;
  match_goal ([[(x : T) |- G ]] => cont x) g.
