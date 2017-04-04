(* Need to load Unicoq to get the module dependency right *)
Declare ML Module "unicoq".
(** Load library "MetaCoqPlugin.cma". *)
Declare ML Module "MetaCoqPlugin".

Require Import MetaCoq.Utils.
Require Import Strings.String.
Require Import NArith.BinNat.
Require Import NArith.BinNatDef.
Require Import Lists.List.
Import ListNotations.

Inductive Exception : Type := exception : Exception.

Definition StuckTerm : Exception. exact exception. Qed.

Definition NotAList : Exception. exact exception. Qed.

Definition TermNotGround : Exception. exact exception. Qed.

Definition WrongTerm : Exception. exact exception. Qed.

Definition HypMissesDependency : Exception. exact exception. Qed.
Definition TypeMissesDependency : Exception. exact exception. Qed.
Definition DuplicatedVariable : Exception. exact exception. Qed.
Definition NotAVar : Exception. exact exception. Qed.

Definition LtacError (s:string) : Exception. exact exception. Qed.

Definition NotUnifiable {A} (x y : A) : Exception. exact exception. Qed.

Definition Failure (s : string) : Exception. exact exception. Qed.

Definition NameExistsInContext (s : string) : Exception. exact exception. Qed.

Definition ExceptionNotGround : Exception. exact exception. Qed.

Definition CannotRemoveVar (x : string) : Exception. exact exception. Qed.

Definition RefNotFound (x : string) : Exception. exact exception. Qed.

Definition AbsDependencyError : Exception. exact exception. Qed.

Definition VarAppearsInValue : Exception. exact exception. Qed.

Definition NotAGoal : Exception. exact exception. Qed.

Definition DoesNotMatch : Exception. exact exception. Qed.
Definition NoPatternMatches : Exception. exact exception. Qed.
Definition Anomaly : Exception. exact exception. Qed.
Definition Continue : Exception. exact exception. Qed.

Definition NameNotFound (n: string) : Exception. exact exception. Qed.
Definition WrongType (T: Type) : Exception. exact exception. Qed.

Definition EmptyList : Exception. exact exception. Qed.
Definition NotThatManyElements : Exception. exact exception. Qed.

Definition CantCoerce : Exception. exact exception. Qed.
Definition NotCumul {A B} (x: A) (y: B) : Exception. exact exception. Qed.

Definition NotAnEvar {A} (x: A) : Exception. exact exception. Qed.
Definition CantInstantiate {A} (x t: A) : Exception. exact exception. Qed.

Record dyn := Dyn { type : Type; elem :> type }.
Arguments Dyn {_} _.

Inductive RedFlags :=
| RedBeta | RedDelta | RedMatch | RedFix | RedZeta
| RedDeltaC | RedDeltaX
| RedDeltaOnly : list dyn -> RedFlags
| RedDeltaBut : list dyn -> RedFlags.

Inductive Reduction :=
| RedNone
| RedSimpl
| RedOneStep
| RedWhd : list RedFlags -> Reduction
| RedStrong : list RedFlags -> Reduction
| RedVmCompute.

Inductive Unification : Type :=
| UniCoq : Unification
| UniMatch : Unification
| UniMatchNoRed : Unification
| UniEvarconv : Unification.

Inductive Hyp : Type :=
| ahyp : forall {A}, A -> option A -> Hyp.

Record Case :=
    mkCase {
        case_ind : Type;
        case_val : case_ind;
        case_return : dyn;
        case_branches : list dyn
        }.

(* Reduction primitive. It throws [NotAList] if the list of flags is not a list.  *)
Definition reduce (r : Reduction) {A} (x : A) := x.

Notation RedAll := ([RedBeta;RedDelta;RedZeta;RedMatch;RedFix]).
Notation RedNF := (RedStrong RedAll).
Notation RedHNF := (RedWhd RedAll).

Notation rsimpl := (reduce RedSimpl).
Notation rhnf := (reduce RedHNF).
Notation rcbv := (reduce RedNF).
Notation rone_step := (reduce RedOneStep).
Notation "'dreduce' ( l1 , .. , ln )" :=
  (reduce (RedStrong [RedBeta; RedFix; RedMatch;
           RedDeltaOnly (Dyn (@l1) :: .. (Dyn (@ln) :: nil) ..)]))
  (at level 0).

(** goal type *)
Inductive goal :=
  | Goal : forall {A}, A -> goal
  | AHyp : forall {A}, option A -> (A -> goal) -> goal
  | HypRem : forall {A}, A -> goal -> goal.

(** Pattern matching without pain *)
(* The M will be instantiated with the M monad or the gtactic monad. In principle,
we could make it part of the B, but then higher order unification will fail. *)
Inductive pattern (M : Type -> Type) (A : Type) (B : A -> Type) (y : A) : Prop :=
  | pbase : forall x : A, (y = x -> M (B x)) -> Unification -> pattern M A B y
  | ptele : forall {C}, (forall x : C, pattern M A B y) -> pattern M A B y.

Arguments pbase {M A B y} _ _ _.
Arguments ptele {M A B y C} _.

Notation "[? x .. y ] ps" := (ptele (fun x => .. (ptele (fun y => ps)).. ))
  (at level 202, x binder, y binder, ps at next level) : pattern_scope.
Notation "p => b" := (pbase p%core (fun _ => b%core) UniMatch)
  (no associativity, at level 201) : pattern_scope.
Notation "p => [ H ] b" := (pbase p%core (fun H => b%core) UniMatch)
  (no associativity, at level 201, H at next level) : pattern_scope.
Notation "'_' => b " := (ptele (fun x=> pbase x (fun _ => b%core) UniMatch))
  (at level 201, b at next level) : pattern_scope.

Notation "p '=n>' b" := (pbase p%core (fun _ => b%core) UniMatchNoRed)
  (no associativity, at level 201) : pattern_scope.
Notation "p '=n>' [ H ] b" := (pbase p%core (fun H => b%core) UniMatchNoRed)
  (no associativity, at level 201, H at next level) : pattern_scope.

Notation "p '=u>' b" := (pbase p%core (fun _ => b%core) UniCoq)
  (no associativity, at level 201) : pattern_scope.
Notation "p '=u>' [ H ] b" := (pbase p%core (fun H => b%core) UniCoq)
  (no associativity, at level 201, H at next level) : pattern_scope.

Delimit Scope pattern_scope with pattern.

Notation "'with' | p1 | .. | pn 'end'" :=
  ((@cons (pattern _ _ _ _) p1%pattern (.. (@cons (pattern _ _ _ _) pn%pattern nil) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.
Notation "'with' p1 | .. | pn 'end'" :=
  ((@cons (pattern _ _ _ _) p1%pattern (.. (@cons (pattern _ _ _ _) pn%pattern nil) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.

Delimit Scope with_pattern_scope with with_pattern.

(** THE definition of MetaCoq *)
Set Printing Universes.
Unset Printing Notations.

Module M.
Inductive t : Type -> Type :=
| ret : forall {A : Type}, A -> t A
| bind : forall {A : Type} {B : Type},
   t A -> (A -> t B) -> t B
| mtry' : forall {A : Type}, t A -> (Exception -> t A) -> t A
| raise : forall {A : Type}, Exception -> t A
| fix1' : forall {A : Type} {B : A -> Type} (S : Type -> Type),
  (forall a : Type, S a -> t a) ->
  ((forall x : A, S (B x)) -> (forall x : A, S (B x))) ->
  forall x : A, t (B x)
| fix2' : forall {A1 : Type} {A2 : A1 -> Type} {B : forall (a1 : A1), A2 a1 -> Type} (S : Type -> Type),
  (forall a : Type, S a -> t a) ->
  ((forall (x1 : A1) (x2 : A2 x1), S (B x1 x2)) ->
    (forall (x1 : A1) (x2 : A2 x1), S (B x1 x2))) ->
  forall (x1 : A1) (x2 : A2 x1), t (B x1 x2)
| fix3' : forall {A1 : Type} {A2 : A1 -> Type}  {A3 : forall (a1 : A1), A2 a1 -> Type} {B : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type} (S : Type -> Type),
  (forall a : Type, S a -> t a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), S (B x1 x2 x3)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), S (B x1 x2 x3))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), t (B x1 x2 x3)
| fix4' : forall {A1 : Type} {A2 : A1 -> Type} {A3 : forall (a1 : A1), A2 a1 -> Type} {A4 : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type} {B : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2), A4 a1 a2 a3 -> Type} (S : Type -> Type),
  (forall a : Type, S a -> t a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), S (B x1 x2 x3 x4)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), S (B x1 x2 x3 x4))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), t (B x1 x2 x3 x4)
| fix5' : forall {A1 : Type} {A2 : A1 -> Type} {A3 : forall (a1 : A1), A2 a1 -> Type} {A4 : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type} {A5 : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2), A4 a1 a2 a3 -> Type} {B : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2) (a4 : A4 a1 a2 a3), A5 a1 a2 a3 a4 -> Type} (S : Type -> Type),
  (forall a : Type, S a -> t a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), S (B x1 x2 x3 x4 x5)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), S (B x1 x2 x3 x4 x5))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), t (B x1 x2 x3 x4 x5)

(** [is_var e] returns if [e] is a variable. *)
| is_var : forall {A : Type}, A -> t bool

(* [nu x od f] executes [f x] where variable [x] is added to the local context,
   optionally with definition [d] with [od = Some d].  It raises
   [NameExistsInContext] if the name "x" is in the context, or
   [VarAppearsInValue] if executing [f x] results in a term containing variable
   [x]. *)
| nu : forall {A : Type} {B : Type}, string -> option A -> (A -> t B) -> t B

(** [abs_fun x e] abstracts variable [x] from [e]. It raises [NotAVar[] if [x]
    is not a variable, or [AbsDependencyError] if [e] or its type [P] depends on
    a variable also depending on [x]. *)
| abs_fun : forall {A : Type} {P : A -> Type} (x : A), P x -> t (forall x, P x)

(** [abs_let x d e] returns [let x := d in e]. It raises [NotAVar] if [x] is not
    a variable, or [AbsDependencyError] if [e] or its type [P] depends on a
    variable also depending on [x]. *)
| abs_let : forall {A : Type} {P : A -> Type} (x: A) (y: A), P x -> t (let x := y in P x)

(** [abs_prod x e] returns [forall x, e]. It raises [NotAVar] if [x] is not a
    variable, or [AbsDependencyError] if [e] or its type [P] depends on a
    variable also depending on [x]. *)
| abs_prod : forall {A : Type} (x : A), Type -> t Type

(** [abs_fix f t n] returns [fix f {struct n} := t].
    [f]'s type must have n products, that is, be [forall x1, ..., xn, T] *)
| abs_fix : forall {A : Type}, A -> A -> N -> t A

(** [get_binder_name t] returns the name of variable [x] if:
    - [t = x],
    - [t = forall x, P x],
    - [t = fun x=>b],
    - [t = let x := d in b].
    It raises [WrongTerm] in any other case.
*)
| get_binder_name : forall {A : Type}, A -> t string

(** [remove x t] executes [t] in a context without variable [x].
    Raises [NotAVar] if [x] is not a variable, and
    [CannotRemoveVar "x"] if [t] or the environment depends on [x]. *)
| remove : forall {A : Type} {B : Type}, A -> t B -> t B

(** [evar A ohyps] creates a meta-variable with type [A] and,
    optionally, in the context resulting from [ohyp].

    It might raise [HypMissesDependency] if some variable in [ohyp]
    is referring to a variable not in the rest of the list
    (the order matters, and is from new-to-old). For instance,
    if [H : x > 0], then the context containing [H] and [x] should be
    given as:
    [ [ahyp H None; ahyp x None] ]

    If the type [A] is referring to variables not in the list of
    hypotheses, it raise [TypeMissesDependency]. If the list contains
    something that is not a variable, it raises [NotAVar]. If it contains duplicated
    occurrences of a variable, it raises a [DuplicatedVariable].
*)
| gen_evar : forall (A : Type), option (list Hyp) -> t A

(** [is_evar e] returns if [e] is a meta-variable. *)
| is_evar : forall {A : Type}, A -> t bool

(** [hash e n] returns a number smaller than [n] representing
    a hash of term [e] *)
| hash : forall {A : Type}, A -> N -> t N

(** [solve_typeclasses] calls type classes resolution. *)
| solve_typeclasses : t unit

(** [print s] prints string [s] to stdout. *)
| print : string -> t unit

(** [pretty_print e] converts term [e] to string. *)
| pretty_print : forall {A : Type}, A -> t string

(** [hyps] returns the list of hypotheses. *)
| hyps : t (list Hyp)

| destcase : forall {A : Type} (a : A), t (Case)

(** Given an inductive type A, applied to all its parameters (but not *)
(*     necessarily indices), it returns the type applied to exactly the *)
(*     parameters, and a list of constructors (applied to the parameters). *)
| constrs : forall {A : Type} (a : A), t (prod dyn (list dyn))
| makecase : forall (C : Case), t dyn

(** [munify x y r] uses reduction strategy [r] to equate [x] and [y].
    It uses convertibility of universes, meaning that it fails if [x]
    is [Prop] and [y] is [Type]. If they are both types, it will
    try to equate its leveles. *)
| unify {A} (x y : A) : Unification -> t (option (x = y))

(** [munify_univ A B r] uses reduction strategy [r] to equate universes
    [A] and [B].  It uses cumulativity of universes, e.g., it succeeds if
    [x] is [Prop] and [y] is [Type]. *)
| unify_univ (A B : Type) : Unification -> t (option (A -> B))

(** [get_reference s] returns the constant that is reference by s. *)
| get_reference : string -> t dyn

(** [get_var s] returns the var named after s. *)
| get_var : string -> t dyn

| call_ltac : forall {A : Type}, string -> list dyn -> t (prod A (list goal))
| list_ltac : t unit
.

Arguments t _%type.

Definition Cevar (A : Type) (ctx : list Hyp) : t A := gen_evar A (Some ctx).
Definition evar (A : Type) : t A := gen_evar A None.

Definition failwith {A} (s : string) : t A := raise (Failure s).

Definition fix1 {A} B := @fix1' A B t (fun _ x => x).
Definition fix2 {A1 A2} B := @fix2' A1 A2 B t (fun _ x => x).
Definition fix3 {A1 A2 A3} B := @fix3' A1 A2 A3 B t (fun _ x => x).
Definition fix4 {A1 A2 A3 A4} B := @fix4' A1 A2 A3 A4 B t (fun _ x => x).
Definition fix5 {A1 A2 A3 A4 A5} B := @fix5' A1 A2 A3 A4 A5 B t (fun _ x => x).

(** Defines [eval f] to execute after elaboration the Mtactic [f].
    It allows e.g. [rewrite (eval f)]. *)
Class runner A  (f : t A) := { eval : A }.
Arguments runner {A} _.
Arguments Build_runner {A} _ _.
Arguments eval {A} _ {_}.

Hint Extern 20 (runner ?f) =>
  (exact (Build_runner f ltac:(mrun f)))  : typeclass_instances.

Definition print_term {A} (x : A) : t unit :=
  bind (pretty_print x) (fun s=> print s).

Module monad_notations.
  Bind Scope M_scope with t.
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

Import monad_notations.

Fixpoint open_pattern {A P y} (p : pattern t A P y) : t (P y) :=
  match p with
  | pbase x f u =>
    oeq <- unify x y u;
    match oeq return t (P y) with
    | Some eq =>
      (* eq has type x = t, but for the pattern we need t = x.
         we still want to provide eq_refl though, so we reduce it *)
      let h := reduce (RedStrong [RedBeta;RedDelta;RedMatch]) (eq_sym eq) in
      let 'eq_refl := eq in
      (* For some reason, we need to return the beta-reduction of the pattern, or some tactic fails *)
      let b := reduce (RedStrong [RedBeta]) (f h) in b
    | None => raise DoesNotMatch
    end
  | @ptele _ _ _ _ C f => e <- evar C; open_pattern (f e)
  end.

Fixpoint mmatch' {A P} (y : A) (ps : list (pattern t A P y)) : t (P y) :=
  match ps with
  | [] => raise NoPatternMatches
  | p :: ps' =>
    mtry' (open_pattern p) (fun e =>
      mif unify e DoesNotMatch UniMatchNoRed then mmatch' y ps' else raise e)
  end.

Module notations.
  Export monad_notations.

  (* We cannot make this notation recursive, so we loose
     notation in favor of naming. *)
  Notation "'\nu' x , a" := (
    let f := fun x => a in
    n <- get_binder_name f;
    nu n None f) (at level 81, x at next level, right associativity) : M_scope.

  Notation "'\nu' x : A , a" := (
    let f := fun x:A=>a in
    n <- get_binder_name f;
    nu n None f) (at level 81, x at next level, right associativity) : M_scope.

  Notation "'\nu' x := t , a" := (
    let f := fun x => a in
    n <- get_binder_name f;
    nu n (Some t) f) (at level 81, x at next level, right associativity) : M_scope.

  Notation "'mfix1' f ( x : A ) : 'M' T := b" :=
    (fix1 (fun x=>T%type) (fun f (x : A)=>b%MC))
    (at level 85, f at level 0, x at next level, format
    "'[v  ' 'mfix1'  f  '(' x  ':'  A ')'  ':'  'M'  T  ':=' '/  ' b ']'") : M_scope.

  Notation "'mfix2' f ( x : A ) ( y : B ) : 'M' T := b" :=
    (fix2 (fun (x : A) (y : B)=>T%type) (fun f (x : A) (y : B)=>b%MC))
    (at level 85, f at level 0, x at next level, y at next level, format
    "'[v  ' 'mfix2'  f  '(' x  ':'  A ')'  '(' y  ':'  B ')'  ':'  'M'  T  ':=' '/  ' b ']'") : M_scope.

  Notation "'mfix3' f ( x : A ) ( y : B ) ( z : C ) : 'M' T := b" :=
    (fix3 (fun (x : A) (y : B) (z : C)=>T%type) (fun f (x : A) (y : B) (z : C)=>b%MC))
    (at level 85, f at level 0, x at next level, y at next level, z at next level, format
    "'[v  ' 'mfix3'  f  '(' x  ':'  A ')'  '(' y  ':'  B ')'  '(' z  ':'  C ')'  ':'  'M'  T  ':=' '/  ' b ']'") : M_scope.

  Notation "'mfix4' f ( x1 : A1 ) ( x2 : A2 ) ( x3 : A3 ) ( x4 : A4 ) : 'M' T := b" :=
    (fix4 (fun (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4)=>T%type) (fun f (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4) =>b%MC))
    (at level 85, f at level 0, x1 at next level, x2 at next level, x3 at next level, x4 at next level, format
    "'[v  ' 'mfix4'  f  '(' x1  ':'  A1 ')'  '(' x2  ':'  A2 ')'  '(' x3  ':'  A3 ')'  '(' x4  ':'  A4 ')'  ':'  'M'  T  ':=' '/  ' b ']'") : M_scope.

  Notation "'mfix5' f ( x1 : A1 ) ( x2 : A2 ) ( x3 : A3 ) ( x4 : A4 ) ( x5 : A5 ) : 'M' T := b" :=
    (fix5 (fun (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4) (x5 : A5)=>T%type) (fun f (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4) (x5 : A5) =>b%MC))
    (at level 85, f at level 0, x1 at next level, x2 at next level, x3 at next level, x4 at next level, x5 at next level, format
    "'[v  ' 'mfix5'  f  '(' x1  ':'  A1 ')'  '(' x2  ':'  A2 ')'  '(' x3  ':'  A3 ')'  '(' x4  ':'  A4 ')'  '(' x5  ':'  A5 ')'  ':'  'M'  T  ':=' '/  ' b ']'") : M_scope.

  Notation "'mmatch' x ls" :=
    (@mmatch' _ (fun _ => _) x ls%with_pattern)
    (at level 90, ls at level 91) : M_scope.
  Notation "'mmatch' x 'return' 'M' p ls" :=
    (@mmatch' _ (fun x => p%type) x ls%with_pattern)
    (at level 90, ls at level 91) : M_scope.
  Notation "'mmatch' x 'as' y 'return' 'M' p ls" :=
    (@mmatch' _ (fun y => p%type) x ls%with_pattern)
    (at level 90, ls at level 91) : M_scope.

  Notation "'mtry' a ls" :=
    (mtry' a (fun e =>
      (@mmatch' _ (fun _ => _) e
                   (app ls%with_pattern [([? x] x => raise x)%pattern]))))
      (at level 82, a at level 100, ls at level 91, only parsing) : M_scope.
End notations.

Import notations.

(* Utilities for lists *)
Definition map {A B} (f : A -> t B) :=
  mfix1 rec (l : list A) : M (list B) :=
    match l with
    | [] => ret []
    | x :: xs => x <- f x; xs <- rec xs; ret (x :: xs)
    end.

Fixpoint mapi' (n : nat) {A B} (f : nat -> A -> t B) (l: list A) : t (list B) :=
  match l with
  | [] => ret []
  | x :: xs =>
    el <- f n x;
    xs' <- mapi' (S n) f xs;
    ret (el :: xs')
  end.

Definition mapi := @mapi' 0.
Arguments mapi {_ _} _ _.

Definition filter {A} (b : A -> t bool) : list A -> t (list A) :=
  fix f l :=
    match l with
    | [] => ret []
    | x :: xs => bx <- b x; r <- f xs;
                 if bx then ret (x :: r) else ret r
    end.

Definition hd {A} (l : list A) : t A :=
  match l with
  | a :: _ => ret a
  | _ => raise EmptyList
  end.

Fixpoint last {A} (l : list A) : t A :=
  match l with
  | [a] => ret a
  | _ :: s => last s
  | _ => raise EmptyList
  end.

Definition fold_right {A B} (f : B -> A -> t A) (x : A) : list B -> t A :=
  fix loop l :=
    match l with
    | [] => ret x
    | x :: xs => r <- loop xs; f x r
    end.

Definition fold_left {A B} (f : A -> B -> t A) : list B -> A -> t A :=
  fix loop l (a : A) :=
    match l with
    | [] => ret a
    | b :: bs => r <- f a b; loop bs r
    end.

Definition index_of {A} (f : A -> t bool) (l : list A) : t (option nat) :=
  ir <- fold_left (fun (ir : (nat * option nat)) x =>
    let (i, r) := ir in
    match r with
    | Some _ => ret ir
    | _ => mif f x then ret (i, Some i) else ret (S i, None)
    end
  ) l (0, None);
  let (_, r) := ir in
  ret r.

Fixpoint nth {A} (n : nat) (l : list A) : t A :=
  match n, l with
  | 0, a :: _ => ret a
  | S n, _ :: s => nth n s
  | _, _ => raise NotThatManyElements
  end.

Definition iterate {A} (f : A -> t unit) : list A -> t unit :=
  fix loop l :=
    match l with
    | [] => ret tt
    | b :: bs => f b;; loop bs
    end.

(** More utilitie *)
Definition mwith {A B} (c : A) (n : string) (v : B) : t dyn :=
  (mfix1 app (d : dyn) : M _ :=
    let (ty, el) := d in
    mmatch d with
    | [? T1 T2 f] @Dyn (forall x:T1, T2 x) f =>
      binder <- get_binder_name ty;
      oeq <- unify binder n UniMatchNoRed;
      if oeq then
        oeq' <- unify B T1 UniCoq;
        match oeq' with
        | Some eq' =>
          let v' := reduce (RedWhd [RedMatch]) match eq' as x in _ = x with eq_refl=> v end in
          ret (Dyn (f v'))
        | _ => raise (WrongType T1)
        end
      else
        e <- evar T1;
        app (Dyn (f e))
    | _ => raise (NameNotFound n)
    end
  ) (Dyn c).

Definition type_of {A} (x : A) : Type := A.
Definition type_inside {A} (x : t A) : Type := A.

Definition unify_cumul {A B} (x: A) (y: B) (u : Unification) : t bool :=
  of <- unify_univ A B u;
  match of with
  | Some f =>
    let fx := reduce RedOneStep (f x) in
    oeq <- unify fx y u;
    match oeq with Some _ => ret true | None => ret false end
  | None => ret false
  end.

(** Unifies [x] with [y] and raises [NotUnifiable] if it they
    are not unifiable. *)
Definition unify_or_fail {A} (x y : A) : t (x = y) :=
  oeq <- unify x y UniCoq;
  match oeq with
  | None => raise (NotUnifiable x y)
  | Some eq => ret eq
  end.

(** Unifies [x] with [y] using cumulativity and raises [NotCumul] if it they
    are not unifiable. *)
Definition cumul_or_fail {A B} (x: A) (y: B) : t unit :=
  b <- unify_cumul x y UniCoq;
  if b then ret tt else raise (NotCumul x y).

Definition names_of_hyp : t (list string) :=
  env <- hyps;
  List.fold_left (fun (ns : t (list string)) (h:Hyp)=>
    let (_, var, _) := h in
    n <- get_binder_name var;
    r <- ns; ret (n :: r)) env (ret []).

Definition hyps_except {A} (x : A) : t (list Hyp) :=
  l <- M.hyps;
  filter (fun y =>
    mmatch y with
    | [? b] ahyp x b => M.ret false
    | _ => ret true
    end) l.

Definition find_hyp_index {A} (x : A) : t(option nat) :=
  l <- M.hyps;
  index_of (fun y =>
    mmatch y with
    | [? b] ahyp x b => M.ret true
    | _ => ret false
    end) l.

(** given a string s it appends a marker to avoid collition with user
    provided names *)
Definition anonymize (s : string) : t string :=
  let s' := rcbv ("__" ++ s)%string in
  ret s'.

Definition fresh_name (name: string) : t string :=
  names <- names_of_hyp;
  let find name : t bool :=
    let res := reduce RedNF (find (fun n => dec_bool (string_dec name n)) names) in
    match res with None => ret false | _ => ret true end
  in
  (mfix1 f (name: string) : M string :=
     mif find name then
       let name := reduce RedNF (name ++ "_")%string in
       f name
     else ret name) name.

Definition fresh_binder_name {A} (x : A) : t string :=
  name <- mtry get_binder_name x with WrongTerm => ret "x"%string end;
  fresh_name name.

Definition unfold_projection {A} (y : A) : t A :=
  let x := rone_step y in
  let x := reduce (RedWhd (RedBeta::RedMatch::nil)) x in ret x.

(** [coerce x] coreces element [x] of type [A] into
    an element of type [B], assuming [A] and [B] are
    unifiable. It raises [CantCoerce] if it fails. *)
Definition coerce {A B : Type} (x : A) : t B :=
  oH <- unify A B UniCoq;
  match oH with
  | Some H => match H with eq_refl => ret x end
  | _ => raise CantCoerce
  end.

Definition is_prop_or_type (d : dyn) : t bool :=
  mmatch d with
  | Dyn Prop => ret true
  | Dyn Type => ret true
  | _ => ret false
  end.

(** [goal_type g] extracts the type of the goal or raises [NotAGoal]
    if [g] is not [Goal]. *)
Definition goal_type (g : goal) : t Type :=
  match g with
  | @Goal A _ => ret A
  | _ => raise NotAGoal
  end.

(** Convertion functions from [dyn] to [goal]. *)
Definition dyn_to_goal (d : dyn) : goal :=
  match d with
  | Dyn x => Goal x
  end.

Definition goal_to_dyn (g : goal) : t dyn :=
  match g with
  | Goal d => ret (Dyn d)
  | _ => raise NotAGoal
  end.

Definition cprint {A} (s : string) (c : A) : t unit :=
  x <- pretty_print c;
  let s := reduce RedNF (s ++ x)%string in
  print s.

(** Printing of a goal *)
Definition print_hyp (a : Hyp) : t unit :=
  let (A, x, ot) := a in
  sA <- pretty_print A;
  sx <- pretty_print x;
  match ot with
  | Some t =>
    st <- pretty_print t;
    M.print (sx ++ " := " ++ st ++ " : " ++ sA)
  | None => print (sx ++ " : " ++ sA)
  end.

Definition print_hyps : t unit :=
  l <- hyps;
  let l := rev' l in
  iterate print_hyp l.

Definition print_goal (g : goal) : t unit :=
  let repeat c := (fix repeat s n :=
    match n with
    | 0 => s
    | S n => repeat (c++s)%string n
    end) ""%string in
  G <- goal_type g;
  sg <- pretty_print G;
  let sep := repeat "="%string 20 in
  print_hyps;;
  print sep;;
  print sg;;
  ret tt.

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
Definition instantiate {A} (x y : A) : t unit :=
  k <- decompose x;
  let (h, _) := k in
  let h := rcbv h.(elem) in
  b <- is_evar h;
  let t := reduce (RedWhd [RedBeta]) t in
  if b then
    r <- unify x y UniEvarconv;
    match r with
    | Some _ => M.ret tt
    | _ => raise (CantInstantiate x y)
    end
  else raise (NotAnEvar h).
End M.

Notation M := M.t.

Import M.notations.

Notation "t 'mwhere' m := u" :=
  (elem (ltac:(mrun (v <- M.mwith t m u; M.ret v)%MC))) (at level 0).
