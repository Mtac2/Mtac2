(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "theories" "MetaCoq" "-top" "Tactics") -*- *)
(* File reduced by coq-bug-finder from original input, then from 959 lines to 126 lines, then from 870 lines to 422 lines, then from 573 lines to 489 lines, then from 505 lines to 488 lines *)
(* coqc version 8.6 (February 2017) compiled on Feb 1 2017 11:48:45 with OCaml 4.02.3
   coqtop version 8.6 (February 2017) *)
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Require Coq.Strings.String.
Import Coq.Lists.List.

Polymorphic Definition dec_bool {P} (x : {P}+{~P}) : bool :=
  match x with
  | left _ => true
  | _ => false
  end.

Polymorphic Inductive poption (A : Type) : Type := PSome : A -> poption A | PNone : poption A.

Arguments PSome {_} _.
Arguments PNone {_}.

Polymorphic Inductive plist (A : Type) : Type := pnil : plist A | pcons : A -> plist A -> plist A.

Arguments pnil {_}.
Arguments pcons {_} _ _.

Infix "::" := pcons (at level 60, right associativity) : list_scope.
Notation " [ ] " := pnil (format "[ ]") : list_scope.
Notation " [ x ] " := (pcons x pnil) : list_scope.
Notation " [ x ; y ; .. ; z ] " :=  (pcons x (pcons y .. (pcons z pnil) ..)) : list_scope.

Polymorphic Definition papp :=
fun {A : Type} =>
  fix papp (l m : plist A) {struct l} : plist A :=
  match l with
  | pnil => m
  | pcons a l1 => pcons a (papp l1 m)
  end.

Section Map.

  Polymorphic Definition pmap := fun {A : Type} {B : Type} (f : A -> B) =>
    fix pmap (l : plist A) : plist B :=
      match l with
      | [] => []
      | a :: t => (f a) :: (pmap t)
      end.

End Map.

Polymorphic Definition pfold_left :=
fun {A B : Type}
  (f : A -> B -> A) =>
fix fold_left (l : plist B) (a0 : A) {struct l} : A :=
  match l with
  | pnil => a0
  | pcons b t => fold_left t (f a0 b)
  end.

Polymorphic Inductive peq (A : Type) (x : A) : A -> Prop := peq_refl : peq _ x x.

Arguments peq {_} _ _.
Notation "x 'p=' y" := (peq x y) (at level 70, no associativity).

Arguments peq_refl {A x} , [A] x.

Polymorphic Definition peq_sym :=
  fun {A : Type} {x y : A} (H : peq x y) =>
    match H in (peq _ y0) return (peq y0 x) with
    | peq_refl _ => peq_refl _
    end.

Polymorphic Inductive pprod (A B : Type) := ppair : A -> B -> pprod A B.
Arguments ppair {_ _} _ _.
Notation "x * y" := (pprod x y) : type_scope.
Notation "( x , y , .. , z )" := (ppair .. (ppair x y) .. z) : core_scope.
Polymorphic Definition psnd {A B} (p : A*B) := match p with ppair _ x => x end.
Import Coq.Strings.String.
Import Coq.NArith.BinNat.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Inductive Exception : Prop := exception : Exception.

Definition WrongTerm : Exception.
admit.
Defined.

Definition NotUnifiable {A} (x y : A) : Exception.
admit.
Defined.

Definition NameExistsInContext (s : string) : Exception.
admit.
Defined.

Definition NotAGoal : Exception.
admit.
Defined.

Definition DoesNotMatch : Exception.
admit.
Defined.
Definition NoPatternMatches : Exception.
admit.
Defined.

Definition EmptyList : Exception.
admit.
Defined.
Definition NotCumul {A B} (x: A) (y: B) : Exception.
admit.
Defined.

Record dyn : Type := Dyn { type : Type; elem : type }.
Arguments Dyn {_} _.

Inductive RedFlags :=
| RedBeta | RedDelta | RedMatch | RedFix | RedZeta
| RedDeltaC | RedDeltaX
| RedDeltaOnly : plist dyn -> RedFlags
| RedDeltaBut : plist dyn -> RedFlags.

Inductive Reduction :=
| RedNone
| RedSimpl
| RedOneStep
| RedWhd : plist RedFlags -> Reduction
| RedStrong : plist RedFlags -> Reduction
| RedVmCompute.

Inductive Unification : Type :=
| UniCoq : Unification
| UniMatch : Unification
| UniMatchNoRed : Unification
| UniEvarconv : Unification.

Inductive Hyp : Prop :=
| ahyp : forall {A}, A -> poption A -> Hyp.

Record Case : Type :=
    mkCase {
        case_ind : Type;
        case_val : case_ind;
        case_return : dyn;
        case_branches : plist dyn
        }.

Definition reduce (r : Reduction) {A} (x : A) := x.

Notation RedAll := ([RedBeta;RedDelta;RedZeta;RedMatch;RedFix]).
Notation RedNF := (RedStrong RedAll).
Notation rcbv := (reduce RedNF).
Notation rone_step := (reduce RedOneStep).
Notation "'dreduce' ( l1 , .. , ln )" :=
  (reduce (RedStrong [RedBeta; RedFix; RedMatch;
           RedDeltaOnly (Dyn (@l1) :: .. (Dyn (@ln) :: pnil) ..)]))
  (at level 0).

Inductive goal : Prop :=
  | Goal : forall {A}, A -> goal
  | AHyp : forall {A}, poption A -> (A -> goal) -> goal
  | HypRem : forall {A}, A -> goal -> goal.

Inductive pattern (M : Type -> Type) (A : Type) (B : A -> Type) (y : A) : Prop :=
  | pbase : forall x : A, (y p= x -> M (B x)) -> Unification -> pattern M A B y
  | ptele : forall {C}, (forall x : C, pattern M A B y) -> pattern M A B y.

Arguments pbase {M A B y} _ _ _.
Arguments ptele {M A B y C} _.

Notation "[? x .. y ] ps" := (ptele (fun x => .. (ptele (fun y => ps)).. ))
  (at level 202, x binder, y binder, ps at next level) : pattern_scope.
Notation "p => b" := (pbase p%core (fun _ => b%core) UniMatch)
  (no associativity, at level 201) : pattern_scope.
Notation "'_' => b " := (ptele (fun x=> pbase x (fun _ => b%core) UniMatch))
  (at level 201, b at next level) : pattern_scope.

Notation "p '=n>' b" := (pbase p%core (fun _ => b%core) UniMatchNoRed)
  (no associativity, at level 201) : pattern_scope.

Notation "p '=u>' b" := (pbase p%core (fun _ => b%core) UniCoq)
  (no associativity, at level 201) : pattern_scope.

Delimit Scope pattern_scope with pattern.

Notation "'with' | p1 | .. | pn 'end'" :=
  ((@pcons (pattern _ _ _ _) p1%pattern (.. (@pcons (pattern _ _ _ _) pn%pattern pnil) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.
Notation "'with' p1 | .. | pn 'end'" :=
  ((@pcons (pattern _ _ _ _) p1%pattern (.. (@pcons (pattern _ _ _ _) pn%pattern pnil) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.

Delimit Scope with_pattern_scope with with_pattern.

Module M.
Inductive t : Type -> Prop :=
| ret : forall {A : Type}, A -> t A
| bind : forall {A : Type} {B : Type},
   t A -> (A -> t B) -> t B
| mtry' : forall {A : Type}, t A -> (Exception -> t A) -> t A
| raise : forall {A : Type}, Exception -> t A
| fix1' : forall {A : Type} {B : A -> Type} (S : Type -> Prop),
  (forall a : Type, S a -> t a) ->
  ((forall x : A, S (B x)) -> (forall x : A, S (B x))) ->
  forall x : A, t (B x)
| fix2' : forall {A1 : Type} {A2 : A1 -> Type} {B : forall (a1 : A1), A2 a1 -> Type} (S : Type -> Prop),
  (forall a : Type, S a -> t a) ->
  ((forall (x1 : A1) (x2 : A2 x1), S (B x1 x2)) ->
    (forall (x1 : A1) (x2 : A2 x1), S (B x1 x2))) ->
  forall (x1 : A1) (x2 : A2 x1), t (B x1 x2)
| fix3' : forall {A1 : Type} {A2 : A1 -> Type}  {A3 : forall (a1 : A1), A2 a1 -> Type} {B : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type} (S : Type -> Prop),
  (forall a : Type, S a -> t a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), S (B x1 x2 x3)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), S (B x1 x2 x3))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), t (B x1 x2 x3)
| fix4' : forall {A1 : Type} {A2 : A1 -> Type} {A3 : forall (a1 : A1), A2 a1 -> Type} {A4 : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type} {B : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2), A4 a1 a2 a3 -> Type} (S : Type -> Prop),
  (forall a : Type, S a -> t a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), S (B x1 x2 x3 x4)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), S (B x1 x2 x3 x4))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), t (B x1 x2 x3 x4)
| fix5' : forall {A1 : Type} {A2 : A1 -> Type} {A3 : forall (a1 : A1), A2 a1 -> Type} {A4 : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type} {A5 : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2), A4 a1 a2 a3 -> Type} {B : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2) (a4 : A4 a1 a2 a3), A5 a1 a2 a3 a4 -> Type} (S : Type -> Prop),
  (forall a : Type, S a -> t a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), S (B x1 x2 x3 x4 x5)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), S (B x1 x2 x3 x4 x5))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), t (B x1 x2 x3 x4 x5)

| is_var : forall {A : Type}, A -> t bool

| nu : forall {A : Type} {B : Type}, string -> poption A -> (A -> t B) -> t B

| abs_fun : forall {A : Type} {P : A -> Type} (x : A), P x -> t (forall x, P x)

| abs_let : forall {A : Type} {P : A -> Type} (x: A) (y: A), P x -> t (let x := y in P x)

| abs_prod : forall {A : Type} (x : A), Type -> t Type

| abs_fix : forall {A : Type}, A -> A -> N -> t A

| get_binder_name : forall {A : Type}, A -> t string

| remove : forall {A : Type} {B : Type}, A -> t B -> t B

| gen_evar : forall (A : Type), poption (plist Hyp) -> t A

| is_evar : forall {A : Type}, A -> t bool

| hash : forall {A : Type}, A -> N -> t N

| solve_typeclasses : t unit

| print : string -> t unit

| pretty_print : forall {A : Type}, A -> t string

| hyps : t (plist Hyp)

| destcase : forall {A : Type} (a : A), t (Case)

| constrs : forall {A : Type} (a : A), t (pprod dyn (plist dyn))
| makecase : forall (C : Case), t dyn

| unify {A} (x y : A) : Unification -> t (poption (x p= y))

| unify_univ (A B : Type) : Unification -> t (poption (A -> B))

| get_reference : string -> t dyn

| get_var : string -> t dyn

| call_ltac : forall {A : Type}, string -> plist dyn -> t (pprod A (plist goal))
| list_ltac : t unit
.
Definition evar (A : Type) : t A := gen_evar A PNone.

Definition fix1 {A} B := @fix1' A B t (fun _ x => x).

Module Export monad_notations.
  Delimit Scope M_scope with MC.
  Open Scope M_scope.

  Notation "r '<-' t1 ';' t2" := (@bind _ _ t1 (fun r=> t2%MC))
    (at level 81, right associativity, format "'[' r  '<-'  '[' t1 ;  ']' ']' '/' t2 ") : M_scope.
  Notation "t1 ';;' t2" := (bind t1 (fun _ => t2%MC))
    (at level 81, right associativity, format "'[' '[' t1 ;;  ']' ']' '/' t2 ") : M_scope.
  Notation "t >>= f" := (bind t f) (at level 70) : M_scope.

  Notation "'mif' b 'then' t 'else' u" :=
    (cond <- b; if cond then t else u) (at level 200) : M_scope.
End monad_notations.

Fixpoint open_pattern {A P y} (p : pattern t A P y) : t (P y) :=
  match p with
  | pbase x f u =>
    oeq <- unify x y u;
    match oeq return t (P y) with
    | PSome eq =>

      let h := reduce (RedStrong [RedBeta;RedDelta;RedMatch]) (peq_sym eq) in
      let 'peq_refl := eq in

      let b := reduce (RedStrong [RedBeta]) (f h) in b
    | PNone => raise DoesNotMatch
    end
  | @ptele _ _ _ _ C f => e <- evar C; open_pattern (f e)
  end.

Fixpoint mmatch' {A P} (y : A) (ps : plist (pattern t A P y)) : t (P y) :=
  match ps with
  | [] => raise NoPatternMatches
  | p :: ps' =>
    mtry' (open_pattern p) (fun e =>
      mif unify e DoesNotMatch UniMatchNoRed then mmatch' y ps' else raise e)
  end.

Module Export notations.
  Export monad_notations.

  Notation "'mfix1' f ( x : A ) : 'M' T := b" :=
    (fix1 (fun x=>T%type) (fun f (x : A)=>b%MC))
    (at level 85, f at level 0, x at next level, format
    "'[v  ' 'mfix1'  f  '(' x  ':'  A ')'  ':'  'M'  T  ':=' '/  ' b ']'") : M_scope.

  Notation "'mmatch' x ls" :=
    (@mmatch' _ (fun _ => _) x ls%with_pattern)
    (at level 90, ls at level 91) : M_scope.

  Notation "'mtry' a ls" :=
    (mtry' a (fun e =>
      (@mmatch' _ (fun _ => _) e
                   (papp ls%with_pattern [([? x] x => raise x)%pattern]))))
      (at level 82, a at level 100, ls at level 91, only parsing) : M_scope.
End notations.

Definition map {A B} (f : A -> t B) :=
  mfix1 rec (l : plist A) : M (plist B) :=
    match l with
    | [] => ret []
    | x :: xs => x <- f x; xs <- rec xs; ret (x :: xs)
    end.

Definition hd {A} (l : plist A) : t A :=
  match l with
  | a :: _ => ret a
  | _ => raise EmptyList
  end.

Definition unify_cumul {A B} (x: A) (y: B) (u : Unification) : t bool :=
  of <- unify_univ A B u;
  match of with
  | PSome f =>
    let fx := reduce RedOneStep (f x) in
    oeq <- unify fx y u;
    match oeq with PSome _ => ret true | PNone => ret false end
  | PNone => ret false
  end.

Definition unify_or_fail {A} (x y : A) : t (x p= y) :=
  oeq <- unify x y UniCoq;
  match oeq with
  | PNone => raise (NotUnifiable x y)
  | PSome eq => ret eq
  end.

Definition cumul_or_fail {A B} (x: A) (y: B) : t unit :=
  b <- unify_cumul x y UniCoq;
  if b then ret tt else raise (NotCumul x y).

Definition names_of_hyp : t (list string) :=
  env <- hyps;
  pfold_left (fun (ns : t (list string)) (h:Hyp)=>
    let (_, var, _) := h in
    n <- get_binder_name var;
    r <- ns; ret (cons n r)) env (ret nil).

Definition anonymize (s : string) : t string :=
  let s' := rcbv ("__" ++ s)%string in
  ret s'.

Definition fresh_name (name: string) : t string :=
  names <- names_of_hyp;
  let find name : t bool :=
    let res := reduce RedNF (List.find (fun n => dec_bool (string_dec name n)) names) in
    match res with None => ret false | _ => ret true end
  in
  (mfix1 f (name: string) : M string :=
     mif find name then
       let name := reduce RedNF (name ++ "_")%string in
       f name
     else ret name) name.

Definition fresh_binder_name {A} (x : A) : t string :=
  name <- mtry get_binder_name x with WrongTerm => M.ret "x"%string end;
  fresh_name name.

End M.

Notation M := M.t.

Import M.notations.
Set Printing Universes.

Definition NotAProduct : Exception.
admit.
Defined.

Definition gtactic (A : Type) := goal -> M (plist (A * goal)).
Notation tactic := (gtactic unit).

Definition ret {A} (x : A) : gtactic A := fun g => M.ret [(x,g)].
Definition idtac : tactic := ret tt.

Definition close_goals {A B} (y : B) : plist (A * goal) -> M (plist (A * goal)) :=
  M.map (fun '(x,g') => r <- M.abs_fun y g'; M.ret (x, @AHyp B PNone r)).

Definition let_close_goals {A B} (y : B) : plist (A * goal) -> M (plist (A * goal)) :=
  let t := rone_step y in
  M.map (fun '(x,g') => r <- M.abs_fun y g'; M.ret (x, @AHyp B (PSome t) r)).

Definition rem_hyp {A B} (x : B) (l: plist (A * goal)) : M (plist (A * goal)) :=
  let v := dreduce (@pmap) (pmap (fun '(y,g) => (y, HypRem x g)) l) in M.ret v.

Definition open_and_apply {A} (t : gtactic A) : gtactic A :=
  fix open g :=
    match g return M _ with
    | Goal _ => t g
    | @AHyp C PNone f =>
      x <- M.fresh_binder_name f;
      M.nu x PNone (fun x : C =>
        open (f x) >>= close_goals x)
    | @AHyp C (PSome t) f =>
      x <- M.fresh_binder_name f;
      M.nu x (PSome t) (fun x : C =>
        open (f x) >>= let_close_goals x)
    | HypRem x f =>
      M.remove x (open f) >>= rem_hyp x
    end.

Definition exact {A} (x:A) : tactic := fun g =>
  match g with
  | Goal g => M.cumul_or_fail x g;; M.ret []
  | _ => M.raise NotAGoal
  end.

Definition intro_base {A B} (var : string) (t : A -> gtactic B) : gtactic B := fun g =>
  mmatch g with
  | [? B (def: B) P e] @Goal (let x := def in P x) e =n>

    eqBA <- M.unify_or_fail B A;
    M.nu var (PSome def) (fun x=>
      let Px := reduce (RedWhd [RedBeta]) (P x) in
      e' <- M.evar Px;
      nG <- M.abs_let (P:=P) x def e';
      exact nG g;;
      let x := reduce (RedWhd [RedMatch]) (match eqBA with peq_refl => x end) in
      t x (Goal e') >>= let_close_goals x)
  | [? P e] @Goal (forall x:A, P x) e =u>
    M.nu var PNone (fun x=>
      let Px := reduce (RedWhd [RedBeta]) (P x) in
      e' <- M.evar Px;
      nG <- M.abs_fun (P:=P) x e';
      exact nG g;;
      t x (Goal e') >>= close_goals x)
  | _ => M.raise NotAProduct
  end.

Definition intro_simpl (var : string) : tactic := fun g =>
  A <- M.evar Type;
  intro_base var (fun _ : A => idtac) g.

Definition intro_anonymous {A} (T : A) (f : string -> M string) (g : goal) : M goal :=
  name <- M.get_binder_name T;
  axn <- M.anonymize name;
  axn <- f axn;
  res <- intro_simpl axn g >>= M.hd;
  M.ret (psnd res).

Set Printing All.
Definition intros_all : tactic :=
  mfix1 f (g : goal) : M (plist (unit * goal)) :=
    open_and_apply (fun g =>
      match g return M (plist (unit * goal)) with
      | @Goal T e =>
        mtry intro_anonymous T M.ret g >>= f with
        | WrongTerm => M.ret [(tt,g)]
        | NotAProduct => M.ret [(tt,g)]
        | [? s] NameExistsInContext s => intro_anonymous T M.fresh_name g >>= f
        end
      | _ => M.raise NotAGoal
      end) g.
