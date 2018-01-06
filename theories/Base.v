(* Need to load Unicoq to get the module dependency right *)
Declare ML Module "unicoq".
(** Load library "MetaCoqPlugin.cma". *)
Declare ML Module "MetaCoqPlugin".

From Mtac2 Require Import Logic Datatypes Logic List Utils.
Require Import Strings.String.
Require Import NArith.BinNat.
Require Import NArith.BinNatDef.
Import Mtac2.List.ListNotations.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

Inductive Exception : Prop := exception : Exception.

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

Definition NotAReference {A} (x : A) : Exception. exact exception. Qed.
Definition AlreadyDeclared (name : string) : Exception. exact exception. Qed.
Definition UnboundVar : Exception. exact exception. Qed.

Definition NotAMatchExp : Exception. exact exception. Qed.

Definition NoClassInstance (A : Type) : Exception. exact exception. Qed.

(** Lifted from coq 8.6.1 Decl_kinds
    TODO: auto generate this file to avoid inconsistencies.
 *)
Inductive definition_object_kind :=
| dok_Definition
| dok_Coercion
| dok_SubClass
| dok_CanonicalStructure
| dok_Example
| dok_Fixpoint
| dok_CoFixpoint
| dok_Scheme
| dok_StructureComponent
| dok_IdentityCoercion
| dok_Instance
| dok_Method.

Inductive implicit_arguments :=
| ia_Explicit
| ia_Implicit
| ia_MaximallyImplicit.

Polymorphic Record dyn := Dyn { type : Type; elem :> type }.
Arguments Dyn {_} _.

Inductive redlist A := rlnil | rlcons : A -> redlist A -> redlist A.

Arguments rlnil {_}.
Arguments rlcons {_} _ _.

Notation "[]rl" := rlnil.
Notation "[rl: x ; .. ; y ]" := (rlcons x (.. (rlcons y rlnil) ..)).

Inductive RedFlags@{I J} : Prop :=
| RedBeta | RedDelta | RedMatch | RedFix | RedZeta
| RedDeltaC | RedDeltaX
| RedDeltaOnly : redlist@{I} dyn@{J} -> RedFlags
| RedDeltaBut : redlist@{I} dyn@{J} -> RedFlags.

Inductive Reduction@{I J} : Prop :=
| RedNone
| RedSimpl
| RedOneStep
| RedWhd : redlist@{I} RedFlags@{I J} -> Reduction
| RedStrong : redlist@{I} RedFlags@{I J} -> Reduction
| RedVmCompute.

Inductive Unification : Type :=
| UniCoq : Unification
| UniMatch : Unification
| UniMatchNoRed : Unification
| UniEvarconv : Unification.

Inductive Hyp : Type :=
| ahyp : forall {A}, A -> moption A -> Hyp.

Record Case :=
    mkCase {
        case_ind : Type;
        case_val : case_ind;
        case_return : dyn;
        case_branches : mlist dyn
        }.

(* Reduction primitive. It throws [NotAList] if the list of flags is not a list.  *)
Definition reduce@{I J K} (r : Reduction@{I J}) {A:Type@{K}} (x : A) := x.

Notation RedAll := ([rl:RedBeta;RedDelta;RedZeta;RedMatch;RedFix]).
Notation RedNF := (RedStrong RedAll).
Notation RedHNF := (RedWhd RedAll).

Notation rsimpl := (reduce RedSimpl).
Notation rhnf := (reduce RedHNF).
Notation rcbv := (reduce RedNF).
Notation rone_step := (reduce RedOneStep).
Notation "'dreduce' ( l1 , .. , ln )" :=
  (reduce (RedStrong [rl:RedBeta; RedFix; RedMatch;
           RedDeltaOnly (rlcons (Dyn (@l1)) ( .. (rlcons (Dyn (@ln)) rlnil) ..))]))
  (at level 0).

(** goal type *)
Inductive goal@{K L} :=
  | Goal : forall {A:Type@{K}}, A -> goal
  | AHyp : forall {A:Type@{L}}, moption@{L} A -> (A -> goal) -> goal
  | HypRem : forall {A:Type@{L}}, A -> goal -> goal.

(** Pattern matching without pain *)
(* The M will be instantiated with the M monad or the gtactic monad. In principle,
we could make it part of the B, but then higher order unification will fail. *)
Inductive pattern (M : Type -> Type) (A : Type) (B : A -> Type) (y : A) : Prop :=
  | pbase : forall x : A, (y =m= x -> M (B x)) -> Unification -> pattern M A B y
  | ptele : forall {C}, (forall x : C, pattern M A B y) -> pattern M A B y.

Arguments pbase {M A B y} _ _ _.
Arguments ptele {M A B y C} _.

Notation "[? x .. y ] ps" := (ptele (fun x => .. (ptele (fun y => ps)).. ))
  (at level 202, x binder, y binder, ps at next level) : pattern_scope.
Notation "p => b" := (pbase p%core (fun _ => b%core) UniMatch)
  (no associativity, at level 201) : pattern_scope.
Notation "p => [ H ] b" := (pbase p%core (fun H => b%core) UniMatch)
  (no associativity, at level 201, H at next level) : pattern_scope.
Notation "p => [ H .. G ] b" := (pbase p%core (fun H => .. (fun G => b%core) .. ) UniMatch)
  (no associativity, at level 201, H binder, G binder) : pattern_scope.
Notation "'_' => b " := (ptele (fun x=> pbase x (fun _ => b%core) UniMatch))
  (at level 201, b at next level) : pattern_scope.

Notation "p '=n>' b" := (pbase p%core (fun _ => b%core) UniMatchNoRed)
  (no associativity, at level 201) : pattern_scope.
Notation "p '=n>' [ H ] b" := (pbase p%core (fun H => b%core) UniMatchNoRed)
  (no associativity, at level 201, H at next level) : pattern_scope.
Notation "p =n> [ H .. G ] b" := (pbase p%core (fun H => .. (fun G => b%core) .. ) UniMatchNoRed)
  (no associativity, at level 201, H binder, G binder) : pattern_scope.

Notation "p '=u>' b" := (pbase p%core (fun _ => b%core) UniCoq)
  (no associativity, at level 201) : pattern_scope.
Notation "p '=u>' [ H ] b" := (pbase p%core (fun H => b%core) UniCoq)
  (no associativity, at level 201, H at next level) : pattern_scope.
Notation "p =u> [ H .. G ] b" := (pbase p%core (fun H => .. (fun G => b%core) .. ) UniCoq)
  (no associativity, at level 201, H binder, G binder) : pattern_scope.

Notation "p '=c>' b" := (pbase p%core (fun _ => b%core) UniEvarconv)
  (no associativity, at level 201) : pattern_scope.
Notation "p '=c>' [ H ] b" := (pbase p%core (fun H => b%core) UniEvarconv)
  (no associativity, at level 201, H at next level) : pattern_scope.
Notation "p =c> [ H .. G ] b" := (pbase p%core (fun H => .. (fun G => b%core) .. ) UniEvarconv)
  (no associativity, at level 201, H binder, G binder) : pattern_scope.

Delimit Scope pattern_scope with pattern.

Notation "'with' | p1 | .. | pn 'end'" :=
  ((@mcons (pattern _ _ _ _) p1%pattern (.. (@mcons (pattern _ _ _ _) pn%pattern [m:]) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.
Notation "'with' p1 | .. | pn 'end'" :=
  ((@mcons (pattern _ _ _ _) p1%pattern (.. (@mcons (pattern _ _ _ _) pn%pattern [m:]) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.

Delimit Scope with_pattern_scope with with_pattern.

(** THE definition of the monad *)
Set Printing Universes.
Unset Printing Notations.

Module M.
Import ProdNotations.
Inductive t@{H I J} : Type@{I} -> Prop :=
| ret : forall {A : Type@{I}}, A -> t A
| bind : forall {A : Type@{I}} {B : Type@{I}},
   t A -> (A -> t B) -> t B
| mtry' : forall {A : Type@{I}}, t A -> (Exception -> t A) -> t A
| raise : forall {A : Type@{I}}, Exception -> t A
| fix1' : forall {A : Type@{I}} {B : A -> Type@{I}} (S : Type@{I} -> Prop),
  (forall a : Type@{I}, S a -> t a) ->
  ((forall x : A, S (B x)) -> (forall x : A, S (B x))) ->
  forall x : A, t (B x)
| fix2' : forall {A1 : Type@{I}} {A2 : A1 -> Type@{I}} {B : forall (a1 : A1), A2 a1 -> Type@{I}} (S : Type@{I} -> Prop),
  (forall a : Type@{I}, S a -> t a) ->
  ((forall (x1 : A1) (x2 : A2 x1), S (B x1 x2)) ->
    (forall (x1 : A1) (x2 : A2 x1), S (B x1 x2))) ->
  forall (x1 : A1) (x2 : A2 x1), t (B x1 x2)
| fix3' : forall {A1 : Type@{I}} {A2 : A1 -> Type@{I}}  {A3 : forall (a1 : A1), A2 a1 -> Type@{I}} {B : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type@{I}} (S : Type@{I} -> Prop),
  (forall a : Type@{I}, S a -> t a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), S (B x1 x2 x3)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), S (B x1 x2 x3))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), t (B x1 x2 x3)
| fix4' : forall {A1 : Type@{I}} {A2 : A1 -> Type@{I}} {A3 : forall (a1 : A1), A2 a1 -> Type@{I}} {A4 : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type@{I}} {B : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2), A4 a1 a2 a3 -> Type@{I}} (S : Type@{I} -> Prop),
  (forall a : Type@{I}, S a -> t a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), S (B x1 x2 x3 x4)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), S (B x1 x2 x3 x4))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), t (B x1 x2 x3 x4)
| fix5' : forall {A1 : Type@{I}} {A2 : A1 -> Type@{I}} {A3 : forall (a1 : A1), A2 a1 -> Type@{I}} {A4 : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type@{I}} {A5 : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2), A4 a1 a2 a3 -> Type@{I}} {B : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2) (a4 : A4 a1 a2 a3), A5 a1 a2 a3 a4 -> Type@{I}} (S : Type@{I} -> Prop),
  (forall a : Type@{I}, S a -> t a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), S (B x1 x2 x3 x4 x5)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), S (B x1 x2 x3 x4 x5))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), t (B x1 x2 x3 x4 x5)

(** [is_var e] returns if [e] is a variable. *)
| is_var : forall {A : Type@{I}}, A -> t bool

(* [nu x od f] executes [f x] where variable [x] is added to the local context,
   optionally with definition [d] with [od = Some d].  It raises
   [NameExistsInContext] if the name "x" is in the context, or
   [VarAppearsInValue] if executing [f x] results in a term containing variable
   [x]. *)
| nu : forall {A : Type@{I}} {B : Type@{I}}, string -> moption A -> (A -> t B) -> t B

(** [abs_fun x e] abstracts variable [x] from [e]. It raises [NotAVar] if [x]
    is not a variable, or [AbsDependencyError] if [e] or its type [P] depends on
    a variable also depending on [x]. *)
| abs_fun : forall {A : Type@{I}} {P : A -> Type@{I}} (x : A), P x -> t (forall x, P x)

(** [abs_let x d e] returns [let x := d in e]. It raises [NotAVar] if [x] is not
    a variable, or [AbsDependencyError] if [e] or its type [P] depends on a
    variable also depending on [x]. *)
| abs_let : forall {A : Type@{I}} {P : A -> Type@{I}} (x: A) (y: A), P x -> t (let x := y in P x)

(** [abs_prod x e] returns [forall x, e]. It raises [NotAVar] if [x] is not a
    variable, or [AbsDependencyError] if [e] or its type [P] depends on a
    variable also depending on [x]. *)
| abs_prod : forall {A : Type@{I}} (x : A), Type@{I} -> t Type@{J}

(** [abs_fix f t n] returns [fix f {struct n} := t].
    [f]'s type must have n products, that is, be [forall x1, ..., xn, T] *)
| abs_fix : forall {A : Type@{I}}, A -> A -> N -> t A

(** [get_binder_name t] returns the name of variable [x] if:
    - [t = x],
    - [t = forall x, P x],
    - [t = fun x=>b],
    - [t = let x := d in b].
    It raises [WrongTerm] in any other case.
*)
| get_binder_name : forall {A : Type@{I}}, A -> t string

(** [remove x t] executes [t] in a context without variable [x].
    Raises [NotAVar] if [x] is not a variable, and
    [CannotRemoveVar "x"] if [t] or the environment depends on [x]. *)
| remove : forall {A : Type@{I}} {B : Type@{I}}, A -> t B -> t B

(** [gen_evar A ohyps] creates a meta-variable with type [A] and,
    optionally, in the context resulting from [ohyp].

    It might raise [HypMissesDependency] if some variable in [ohyp]
    is referring to a variable not in the rest of the list
    (the order matters, and is from new-to-old). For instance,
    if [H : x > 0], then the context containing [H] and [x] should be
    given as:
    [ [ahyp H None; ahyp x None] ]

    If the type [A] is referring to variables not in the list of
    hypotheses, it raise [Type@{I}MissesDependency]. If the list contains
    something that is not a variable, it raises [NotAVar]. If it contains duplicated
    occurrences of a variable, it raises a [DuplicatedVariable].
*)
| gen_evar : forall (A : Type@{I}), moption (mlist@{I} Hyp@{J}) -> t A

(** [is_evar e] returns if [e] is a meta-variable. *)
| is_evar : forall {A : Type@{I}}, A -> t bool

(** [hash e n] returns a number smaller than [n] representing
    a hash of term [e] *)
| hash : forall {A : Type@{I}}, A -> N -> t N

(** [solve_typeclasses] calls type classes resolution. *)
| solve_typeclasses : t unit

(** [print s] prints string [s] to stdout. *)
| print : string -> t unit

(** [pretty_print e] converts term [e] to string. *)
| pretty_print : forall {A : Type@{I}}, A -> t string

(** [hyps] returns the list of hypotheses. *)
| hyps : t (mlist@{I} Hyp@{J})

| destcase : forall {A : Type@{I}} (a : A), t (Case@{H H I J})

(** Given an inductive type A, applied to all its parameters (but not *)
(*     necessarily indices), it returns the type applied to exactly the *)
(*     parameters, and a list of constructors (applied to the parameters). *)
| constrs : forall {A : Type@{I}} (a : A), t (mprod@{I I} dyn@{H} (mlist@{I} dyn@{J}))
| makecase : forall (C : Case@{H H I J}), t dyn@{J}

(** [munify x y r] uses reduction strategy [r] to equate [x] and [y].
    It uses convertibility of universes, meaning that it fails if [x]
    is [Prop] and [y] is [Type@{I}]. If they are both types, it will
    try to equate its leveles. *)
| unify {A : Type@{I}} (x y : A) : Unification -> t (moption@{I} (x =m= y))

(** [munify_univ A B r] uses reduction strategy [r] to equate universes
    [A] and [B].  It uses cumulativity of universes, e.g., it succeeds if
    [x] is [Prop] and [y] is [Type@{I}]. *)
| unify_univ (A B : Type@{I}) : Unification -> t (moption (A -> B))

(** [get_reference s] returns the constant that is reference by s. *)
| get_reference : string -> t dyn@{J}

(** [get_var s] returns the var named after s. *)
| get_var : string -> t dyn@{J}

| call_ltac : forall {A : Type@{I}}, string -> mlist@{I} dyn@{J} -> t (mprod@{I I} A (mlist@{I} goal@{H J}))
| list_ltac : t unit

(** [read_line] returns the string from stdin. *)
| read_line : t string

(** [break f t] calls [f] at each step of the computation of [t]. [f]
    is expcted to return the term that receives as argument, or any
    transformation of it. *)
| break' : forall (S : Type@{I} -> Prop),
  (forall a : Type@{I}, S a -> t a) ->
  (forall A : Type@{I}, S A -> t (S A)) -> forall {A : Type@{I}}, S A -> t A

(** [decompose x] decomposes value [x] into a head and a spine of
    arguments. For instance, [decompose (3 + 3)] returns
    [(Dyn add, [Dyn 3; Dyn 3])] *)
| decompose : forall {A : Type@{I}}, A -> t (mprod@{I I} dyn@{J} (mlist@{I} dyn@{J}))

(** [solve_typeclass A] calls type classes resolution for [A] and returns the result or fail. *)
| solve_typeclass : forall (A:Type@{I}), t (moption A)

(** [declare dok name opaque t] defines [name] as definition kind
    [dok] with content [t] and opacity [opaque] *)
| declare : forall (dok : definition_object_kind)
                   (name : string)
                   (opaque : bool),
    forall {A : Type@{I}}, A -> t A

(** [declare_implicits r l] declares implicit arguments for global
    reference [r] according to [l] *)
| declare_implicits : forall {A : Type@{I}} (a : A),
    mlist@{I} implicit_arguments -> t unit

(** [os_cmd cmd] executes the command and returns its error number. *)
| os_cmd : string -> t Z
.

Arguments t _%type.

Definition fmap {A:Type} {B:Type} (f : A -> B) (x : t A) : t B :=
  bind x (fun a => ret (f a)).
Definition fapp {A B} (f : t (A -> B)) (x : t A) : t B :=
  bind f (fun g => fmap g x).

Definition Cevar (A : Type) (ctx : mlist Hyp) : t A := gen_evar A (mSome ctx).
Definition evar (A : Type) : t A := gen_evar A mNone.

Definition failwith {A} (s : string) : t A := raise (Failure s).

Definition fix1 {A} B := @fix1' A B t (fun _ x => x).
Definition fix2 {A1 A2} B := @fix2' A1 A2 B t (fun _ x => x).
Definition fix3 {A1 A2 A3} B := @fix3' A1 A2 A3 B t (fun _ x => x).
Definition fix4 {A1 A2 A3 A4} B := @fix4' A1 A2 A3 A4 B t (fun _ x => x).
Definition fix5 {A1 A2 A3 A4 A5} B := @fix5' A1 A2 A3 A4 A5 B t (fun _ x => x).

Definition break {A} f := @break' t (fun _ x => x) f A.

(** Defines [eval f] to execute after elaboration the Mtactic [f].
    It allows e.g. [rewrite (eval f)]. *)
Class runner A  (f : t A) := { eval : A }.
Arguments runner {A} _.
Arguments Build_runner {A} _ _.
Arguments eval {A} _ {_}.

Hint Extern 20 (runner ?f) =>
  (mrun (bind f (fun eres=> ret (Build_runner f eres))))  : typeclass_instances.

Definition print_term {A} (x : A) : t unit :=
  bind (pretty_print x) (fun s=> print s).

Definition dbg_term {A} (s: string) (x : A) : t unit :=
  bind (pretty_print x) (fun t=> print (s++t)).

Module monad_notations.
  Bind Scope M_scope with t.
  Delimit Scope M_scope with MC.
  Open Scope M_scope.

  Notation "r '<-' t1 ';' t2" := (bind t1 (fun r=> t2))
    (at level 20, t1 at level 100, t2 at level 200,
     right associativity, format "'[' r  '<-'  '[' t1 ;  ']' ']' '/' t2 ") : M_scope.
  Notation "' r1 .. rn '<-' t1 ';' t2" := (bind t1 (fun r1 => .. (fun rn => t2) ..))
    (at level 20, r1 binder, rn binder, t1 at level 100, t2 at level 200,
     right associativity, format "'[' ''' r1 .. rn  '<-'  '[' t1 ;  ']' ']' '/' t2 ") : M_scope.
  Notation "t1 ';;' t2" := (bind t1 (fun _ => t2))
    (at level 100, t2 at level 200,
     format "'[' '[' t1 ;;  ']' ']' '/' t2 ") : M_scope.

  Notation "f =<< t" := (bind t f) (at level 70, only parsing) : M_scope.
  Notation "t >>= f" := (bind t f) (at level 70) : M_scope.

  Infix "<$>" := fmap (at level 61, left associativity) : M_scope.
  Infix "<*>" := fapp (at level 61, left associativity) : M_scope.

  Notation "'mif' b 'then' t 'else' u" :=
    (cond <- b; if cond then t else u) (at level 200) : M_scope.
End monad_notations.

Import monad_notations.

Fixpoint open_pattern {A P y} (p : pattern t A P y) : t (P y) :=
  match p with
  | pbase x f u =>
    oeq <- unify x y u;
    match oeq return t (P y) with
    | mSome eq =>
      (* eq has type x =m= t, but for the pattern we need t = x.
         we still want to provide eq_refl though, so we reduce it *)
      let h := reduce (RedWhd [rl:RedBeta;RedDelta;RedMatch]) (meq_sym eq) in
      let 'meq_refl := eq in
      (* For some reason, we need to return the beta-reduction of the pattern, or some tactic fails *)
      let b := reduce (RedWhd [rl:RedBeta]) (f h) in b
    | mNone => raise DoesNotMatch
    end
  | @ptele _ _ _ _ C f => e <- evar C; open_pattern (f e)
  end.

Fixpoint mmatch' {A P} (y : A) (ps : mlist (pattern t A P y)) : t (P y) :=
  match ps with
  | [m:] => raise NoPatternMatches
  | p :m: ps' =>
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
    nu n mNone f) (at level 200, x ident, a at level 200, right associativity) : M_scope.

  Notation "'\nu' x : A , a" := (
    let f := fun x:A=>a in
    n <- get_binder_name f;
    nu n mNone f) (at level 200, x ident, a at level 200, right associativity) : M_scope.

  Notation "'\nu' x := t , a" := (
    let f := fun x => a in
    n <- get_binder_name f;
    nu n (mSome t) f) (at level 200, x ident, a at level 200, right associativity) : M_scope.

  Notation "'mfix1' f x .. y : 'M' T := b" :=
    (fix1 (fun x => .. (fun y => T%type) ..) (fun f x => .. (fun y => b) ..))
    (at level 200, f ident, x binder, y binder, format
    "'[v  ' 'mfix1'  f  x  ..  y  ':'  'M'  T  ':=' '/  ' b ']'") : M_scope.

  Notation "'mfix2' f x .. y : 'M' T := b" :=
    (fix2 (fun x => .. (fun y => T%type) ..) (fun f x => .. (fun y => b) ..))
    (at level 200, f ident, x binder, y binder, format
    "'[v  ' 'mfix2'  f  x  ..  y  ':'  'M'  T  ':=' '/  ' b ']'") : M_scope.

  Notation "'mfix3' f x .. y : 'M' T := b" :=
    (fix3 (fun x => .. (fun y => T%type) ..) (fun f x => .. (fun y => b) ..))
    (at level 200, f ident, x binder, y binder, format
    "'[v  ' 'mfix3'  f  x  ..  y  ':'  'M'  T  ':=' '/  ' b ']'") : M_scope.

  Notation "'mfix4' f x .. y : 'M' T := b" :=
    (fix4 (fun x => .. (fun y => T%type) ..) (fun f x => .. (fun y => b) ..))
    (at level 200, f ident, x binder, y binder, format
    "'[v  ' 'mfix4'  f  x  ..  y  ':'  'M'  T  ':=' '/  ' b ']'") : M_scope.

  Notation "'mfix5' f x .. y : 'M' T := b" :=
    (fix5 (fun x => .. (fun y => T%type) ..) (fun f x => .. (fun y => b) ..))
    (at level 200, f ident, x binder, y binder, format
    "'[v  ' 'mfix5'  f  x  ..  y  ':'  'M'  T  ':=' '/  ' b ']'") : M_scope.

  Notation "'mmatch' x ls" :=
    (@mmatch' _ (fun _ => _) x ls%with_pattern)
    (at level 200, ls at level 91) : M_scope.
  Notation "'mmatch' x 'return' 'M' p ls" :=
    (@mmatch' _ (fun _ => p%type) x ls%with_pattern)
    (at level 200, ls at level 91) : M_scope.
  Notation "'mmatch' x 'as' y 'return' 'M' p ls" :=
    (@mmatch' _ (fun y => p%type) x ls%with_pattern)
    (at level 200, ls at level 91) : M_scope.

  Notation "'mtry' a ls" :=
    (mtry' a (fun e =>
      (@mmatch' _ (fun _ => _) e
                   (mapp ls%with_pattern [m:([? x] x => raise x)%pattern]))))
      (at level 200, a at level 100, ls at level 91, only parsing) : M_scope.
End notations.

Import notations.

(* Utilities for lists *)
Definition map {A B} (f : A -> t B) :=
  mfix1 rec (l : mlist A) : M (mlist B) :=
    match l with
    | [m:] => ret [m:]
    | x :m: xs => mcons <$> f x <*> rec xs
    end.

Fixpoint mapi' (n : nat) {A B} (f : nat -> A -> t B) (l: mlist A) : t (mlist B) :=
  match l with
  | [m:] => ret [m:]
  | x :m: xs => mcons <$> f n x <*> mapi' (S n) f xs
  end.

Definition mapi := @mapi' 0.
Arguments mapi {_ _} _ _.

Definition find {A} (b : A -> t bool) : mlist A -> t (moption A) :=
  fix f l :=
    match l with
    | [m:] => ret mNone
    | x :m: xs => mif b x then ret (mSome x) else f xs
    end.

Definition filter {A} (b : A -> t bool) : mlist A -> t (mlist A) :=
  fix f l :=
    match l with
    | [m:] => ret [m:]
    | x :m: xs => mif b x then mcons x <$> f xs else f xs
    end.

Definition hd {A} (l : mlist A) : t A :=
  match l with
  | a :m: _ => ret a
  | _ => raise EmptyList
  end.

Fixpoint last {A} (l : mlist A) : t A :=
  match l with
  | [m:a] => ret a
  | _ :m: s => last s
  | _ => raise EmptyList
  end.

Definition fold_right {A B} (f : B -> A -> t A) (x : A) : mlist B -> t A :=
  fix loop l :=
    match l with
    | [m:] => ret x
    | x :m: xs => f x =<< loop xs
    end.

Definition fold_left {A B} (f : A -> B -> t A) : mlist B -> A -> t A :=
  fix loop l (a : A) :=
    match l with
    | [m:] => ret a
    | b :m: bs => loop bs =<< f a b
    end.

Definition index_of {A} (f : A -> t bool) (l : mlist A) : t (moption nat) :=
  ''(_, r) <- fold_left (fun '(i, r) x =>
    match r with
    | mSome _ => ret (i,r)
    | _ => mif f x then ret (i, mSome i) else ret (S i, mNone)
    end
  ) l (0, mNone);
  ret r.

Fixpoint nth {A} (n : nat) (l : mlist A) : t A :=
  match n, l with
  | 0, a :m: _ => ret a
  | S n, _ :m: s => nth n s
  | _, _ => raise NotThatManyElements
  end.

Definition iterate {A} (f : A -> t unit) : mlist A -> t unit :=
  fix loop l :=
    match l with
    | [m:] => ret tt
    | b :m: bs => f b;; loop bs
    end.

(** More utilitie *)
Definition mwith {A B} (c : A) (n : string) (v : B) : t dyn :=
  (mfix1 app (d : dyn) : M _ :=
    let (ty, el) := d in
    mmatch d with
    | [? T1 T2 f] @Dyn (forall x:T1, T2 x) f =>
      let ty := reduce (RedWhd [rl:RedBeta]) ty in
      binder <- get_binder_name ty;
      mif unify binder n UniMatchNoRed then
        oeq' <- unify B T1 UniCoq;
        match oeq' with
        | mSome eq' =>
          let v' := reduce (RedWhd [rl:RedMatch]) match eq' as x in _ =m= x with meq_refl=> v end in
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

Definition cumul {A B} (u : Unification) (x: A) (y: B) : t bool :=
  of <- unify_univ A B u;
  match of with
  | mSome f =>
    let fx := reduce RedOneStep (f x) in
    oeq <- unify fx y u;
    match oeq with mSome _ => ret true | mNone => ret false end
  | mNone => ret false
  end.

(** Unifies [x] with [y] and raises [NotUnifiable] if it they
    are not unifiable. *)
Definition unify_or_fail {A} (u : Unification) (x y : A) : t (x =m= y) :=
  oeq <- unify x y u;
  match oeq with
  | mNone => raise (NotUnifiable x y)
  | mSome eq => ret eq
  end.

(** Unifies [x] with [y] using cumulativity and raises [NotCumul] if it they
    are not unifiable. *)
Definition cumul_or_fail {A B} (u : Unification) (x: A) (y: B) : t unit :=
  mif cumul u x y then ret tt else raise (NotCumul x y).

Definition names_of_hyp : t (mlist string) :=
  env <- hyps;
  mfold_left (fun (ns : t (mlist string)) '(ahyp var _) =>
    mcons <$> get_binder_name var <*> ns) env (ret [m:]).

Definition hyps_except {A} (x : A) : t (mlist Hyp) :=
  filter (fun y =>
    mmatch y with
    | [? b] ahyp x b => M.ret false
    | _ => ret true
    end) =<< M.hyps.

Definition find_hyp_index {A} (x : A) : t (moption nat) :=
  index_of (fun y =>
    mmatch y with
    | [? b] ahyp x b => M.ret true
    | _ => ret false
    end) =<< M.hyps.

(** given a string s it appends a marker to avoid collition with user
    provided names *)
Definition anonymize (s : string) : t string :=
  let s' := rcbv ("__" ++ s)%string in
  ret s'.

Definition fresh_name (name: string) : t string :=
  names <- names_of_hyp;
  let find name : t bool :=
    let res := reduce RedNF (mfind (fun n => dec_bool (string_dec name n)) names) in
    match res with mNone => ret false | _ => ret true end
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
  let x := reduce (RedWhd [rl:RedBeta;RedMatch]) x in ret x.

(** [coerce x] coreces element [x] of type [A] into
    an element of type [B], assuming [A] and [B] are
    unifiable. It raises [CantCoerce] if it fails. *)
Definition coerce {A B : Type} (x : A) : t B :=
  oH <- unify A B UniCoq;
  match oH with
  | mSome H => match H with meq_refl => ret x end
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
  | mSome t =>
    st <- pretty_print t;
    M.print (sx ++ " := " ++ st ++ " : " ++ sA)
  | mNone => print (sx ++ " : " ++ sA)
  end.

Definition print_hyps : t unit :=
  l <- hyps;
  let l := mrev' l in
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

(** [instantiate x t] tries to instantiate meta-variable [x] with [t].
    It fails with [NotAnEvar] if [x] is not a meta-variable (applied to a spine), or
    [CantInstantiate] if it fails to find a suitable instantiation. [t] is beta-reduced
    to avoid false dependencies. *)
Definition instantiate {A} (x y : A) : t unit :=
  ''(m: h, _) <- decompose x;
  let h := rcbv h.(elem) in
  mif is_evar h then
    let t := reduce (RedWhd [rl:RedBeta]) t in
    r <- unify x y UniEvarconv;
    match r with
    | mSome _ => M.ret tt
    | _ => raise (CantInstantiate x y)
    end
  else raise (NotAnEvar h).

Definition solve_typeclass_or_fail (A : Type) : t A :=
  x <- solve_typeclass A;
  match x with mSome a => M.ret a | mNone => raise (NoClassInstance A) end.

(** Collects obviously visible evars *)
Definition collect_evars {A} (x: A) :=
  res <- (mfix1 f (d: dyn) : M (mlist dyn) :=
    let (_, e) := d in
    mif M.is_evar e then M.ret [m: d]
    else
      let e := reduce (RedWhd [rl: RedBeta; RedMatch; RedZeta]) e in
      ''(m: h, l) <- M.decompose e;
      if is_empty l then M.ret [m:]
      else
        f h >>= fun d => M.map f l >>= fun ds => M.ret (mapp d (mconcat ds))
    ) (Dyn x);
  let red := dreduce (@mapp, @mconcat) res in
  ret red.

End M.

Notation M := M.t.

Import M.notations.

Notation "t 'mwith' ( k := u )" :=
  (elem (ltac:(mrun (M.mwith t k u)))) (at level 0).


(** Execution of tactics at unification *)
Polymorphic Definition lift {A} (f: M A) (v : A) := A.



(** creation of exceptions *)
Definition new_exception name := M.declare dok_Definition name true exception;; M.ret tt.
Notation "'new' 'exception' n" := (M.eval (h <- M.get_binder_name (fun n=>n);
                                           new_exception h)) (at level 0, n at next level).
