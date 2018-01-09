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
Set Printing Universes.

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

Inductive dyn@{a} : Prop := Dyn : forall {type : Type@{a}} (elem : type), dyn.
Record dynr := Dynr { typer: Type; elemr:> typer }.
Arguments Dynr {_} _.

Inductive redlist A := rlnil | rlcons : A -> redlist A -> redlist A.

Arguments rlnil {_}.
Arguments rlcons {_} _ _.

Notation "[]rl" := rlnil.
Notation "[rl: x ; .. ; y ]" := (rlcons x (.. (rlcons y rlnil) ..)).

Inductive RedFlags@{a} : Prop :=
| RedBeta | RedDelta | RedMatch | RedFix | RedZeta
| RedDeltaC | RedDeltaX
| RedDeltaOnly : redlist@{a} dyn@{a} -> RedFlags
| RedDeltaBut : redlist@{a} dyn@{a} -> RedFlags.

Inductive Reduction@{a} : Prop :=
| RedNone
| RedSimpl
| RedOneStep
| RedWhd : redlist@{a} RedFlags@{a} -> Reduction
| RedStrong : redlist@{a} RedFlags@{a} -> Reduction
| RedVmCompute.

Inductive Unification : Type :=
| UniCoq : Unification
| UniMatch : Unification
| UniMatchNoRed : Unification
| UniEvarconv : Unification.

Inductive Hyp : Type :=
| ahyp : forall {A}, A -> moption A -> Hyp.

Record Case@{a c} :=
    mkCase {
        case_ind : Type@{a};
        case_val : case_ind;
        case_return : dyn@{c};
        case_branches : mlist@{c} dyn@{c}
        }.

(* Reduction primitive. It throws [NotAList] if the list of flags is not a list.  *)
Definition reduce@{r a} (r : Reduction@{r}) {A:Type@{a}} (x : A) := x.

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
Inductive pattern@{a b e} (M : Type@{b} -> Type@{b}) (A : Type@{a}) (B : A -> Type@{b}) (y : A) : Prop :=
  | pbase : forall x : A, (y =m= x ->M (B x)) -> Unification -> pattern M A B y
  | ptele : forall {C:Type@{e}}, (forall x : C, pattern M A B y) -> pattern M A B y.

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
Unset Printing Notations.

Module M.
Import ProdNotations.
Inductive t@{t} : Type@{t} -> Prop := mkt : forall{a}, t a.

Definition ret@{a} : forall {A : Type@{a}}, A -> t@{a} A.
  refine (fun a _=>mkt). Qed.

Definition bind@{a b} : forall {A : Type@{a}} {B : Type@{b}}, t A -> (A -> t B) -> t@{b} B.
  refine (fun a b _ _=>mkt). Qed.

Definition mtry'@{a} : forall {A : Type@{a}}, t@{a} A -> (Exception -> t@{a} A) -> t@{a} A.
  refine (fun A _ _ => mkt). Qed.

Definition raise@{a} : forall {A : Type@{a}}, Exception -> t@{a} A.
  refine (fun A _ => mkt). Qed.

Definition fix1'@{a b} : forall{A: Type@{a}} {B: A->Type@{b}} (S: Type@{b}->Prop),
  (forall a: Type@{b}, S a->t a) ->
  ((forall x: A, S (B x))->(forall x: A, S (B x))) ->
  forall x: A, t@{b} (B x).
  refine (fun A B _ _ _ x=>mkt). Qed.

Definition fix2'@{a1 a2 b} : forall {A1: Type@{a1}} {A2: A1->Type@{a2}} {B: forall (a1 : A1), A2 a1->Type@{b}} (S: Type@{b}->Prop),
  (forall a: Type@{b}, S a -> t a) ->
  ((forall (x1: A1) (x2: A2 x1), S (B x1 x2)) ->
    (forall (x1: A1) (x2: A2 x1), S (B x1 x2))) ->
  forall (x1: A1) (x2: A2 x1), t (B x1 x2).
  refine (fun A1 A2 B _ _ _ x1 x2=>mkt). Qed.

Definition fix3'@{a1 a2 a3 b} : forall {A1: Type@{a1}} {A2: A1->Type@{a2}} {A3 : forall (a1: A1), A2 a1->Type@{a3}} {B: forall (a1: A1) (a2: A2 a1), A3 a1 a2->Type@{b}} (S : Type@{b}->Prop),
  (forall a: Type@{b}, S a -> t a) ->
  ((forall (x1: A1) (x2: A2 x1) (x3: A3 x1 x2), S (B x1 x2 x3)) ->
    (forall (x1: A1) (x2: A2 x1) (x3: A3 x1 x2), S (B x1 x2 x3))) ->
  forall (x1: A1) (x2: A2 x1) (x3: A3 x1 x2), t (B x1 x2 x3).
  refine (fun A1 A2 A3 B _ _ _ x1 x2 x3=>mkt). Qed.

Definition fix4'@{a1 a2 a3 a4 b} : forall {A1: Type@{a1}} {A2: A1->Type@{a2}} {A3: forall (a1: A1), A2 a1->Type@{a3}} {A4: forall (a1: A1) (a2: A2 a1), A3 a1 a2->Type@{a4}} {B: forall (a1: A1) (a2: A2 a1) (a3: A3 a1 a2), A4 a1 a2 a3->Type@{b}} (S : Type@{b} -> Prop),
  (forall a: Type@{b}, S a->t a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), S (B x1 x2 x3 x4)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), S (B x1 x2 x3 x4))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), t (B x1 x2 x3 x4).
  refine (fun A1 A2 A3 A4 B _ _ _ x1 x2 x3 x4=>mkt). Qed.

Definition fix5'@{a1 a2 a3 a4 a5 b}: forall{A1: Type@{a1}} {A2: A1->Type@{a2}} {A3: forall(a1: A1), A2 a1->Type@{a3}} {A4: forall(a1: A1)(a2: A2 a1), A3 a1 a2->Type@{a4}} {A5: forall(a1: A1)(a2: A2 a1)(a3: A3 a1 a2), A4 a1 a2 a3->Type@{a5}} {B: forall(a1: A1)(a2: A2 a1)(a3: A3 a1 a2)(a4: A4 a1 a2 a3), A5 a1 a2 a3 a4->Type@{b}} (S : Type@{b}->Prop),
  (forall a : Type@{b}, S a -> t a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), S (B x1 x2 x3 x4 x5)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), S (B x1 x2 x3 x4 x5))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), t (B x1 x2 x3 x4 x5).
  refine (fun A1 A2 A3 A4 A5 B _ _ _ x1 x2 x3 x4 x5=>mkt). Qed.

(** [is_var e] returns if [e] is a variable. *)
Definition is_var@{a}: forall{A : Type@{a}}, A->t@{Set} bool.
  refine (fun _ _=>mkt). Qed.

(* [nu x od f] executes [f x] where variable [x] is added to the local context,
   optionally with definition [d] with [od = Some d].  It raises
   [NameExistsInContext] if the name "x" is in the context, or
   [VarAppearsInValue] if executing [f x] results in a term containing variable
   [x]. *)
Definition nu@{a b}: forall{A: Type@{a}}{B: Type@{b}}, string -> moption@{a} A -> (A -> t@{b} B) -> t@{b} B.
  refine (fun _ _ _ _ _ =>mkt). Qed.

(** [abs_fun x e] abstracts variable [x] from [e]. It raises [NotAVar] if [x]
    is not a variable, or [AbsDependencyError] if [e] or its type [P] depends on
    a variable also depending on [x]. *)
Definition abs_fun@{a b c}: forall{A: Type@{a}} {P: A->Type@{b}} (x: A), P x -> t@{c} (forall x, P x).
  refine (fun _ _ _ _ => mkt). Qed.

(** [abs_let x d e] returns [let x := d in e]. It raises [NotAVar] if [x] is not
    a variable, or [AbsDependencyError] if [e] or its type [P] depends on a
    variable also depending on [x]. *)
Definition abs_let@{a b c}: forall{A: Type@{a}} {P: A->Type@{b}} (x: A) (y: A), P x -> t@{c} (let x := y in P x).
  refine (fun _ _ _ _ _=> mkt). Qed.

(** [abs_prod x e] returns [forall x, e]. It raises [NotAVar] if [x] is not a
    variable, or [AbsDependencyError] if [e] or its type [P] depends on a
    variable also depending on [x]. *)
Definition abs_prod@{a b c}: forall{A: Type@{a}} (x : A), Type@{a} -> t@{c} Type@{b}.
  refine (fun _ _ _=> mkt). Qed.

(** [abs_fix f t n] returns [fix f {struct n} := t].
    [f]'s type must have n products, that is, be [forall x1, ..., xn, T] *)
Definition abs_fix@{a}: forall{A: Type@{a}}, A -> A -> N -> t@{a} A.
  refine (fun _ _ _ _=> mkt). Qed.

(** [get_binder_name t] returns the name of variable [x] if:
    - [t = x],
    - [t = forall x, P x],
    - [t = fun x=>b],
    - [t = let x := d in b].
    It raises [WrongTerm] in any other case.
*)
Definition get_binder_name@{a}: forall{A: Type@{a}}, A -> t@{Set} string.
  refine (fun _ _=> mkt). Qed.

(** [remove x t] executes [t] in a context without variable [x].
    Raises [NotAVar] if [x] is not a variable, and
    [CannotRemoveVar "x"] if [t] or the environment depends on [x]. *)
Definition remove@{a b} : forall{A: Type@{a}} {B: Type@{b}}, A -> t@{b} B -> t@{b} B.
  refine (fun _ _ _ _=> mkt). Qed.

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
Definition gen_evar@{a b c}: forall(A: Type@{a}), moption@{c} (mlist@{c} Hyp@{b}) -> t@{a} A.
  refine (fun _ _=>mkt). Qed.

(** [is_evar e] returns if [e] is a meta-variable. *)
Definition is_evar@{a}: forall{A: Type@{a}}, A -> t@{Set} bool.
  refine (fun _ _=>mkt). Qed.

(** [hash e n] returns a number smaller than [n] representing
    a hash of term [e] *)
Definition hash@{a}: forall{A: Type@{a}}, A -> N -> t@{Set} N.
  refine (fun _ _ _=>mkt). Qed.

(** [solve_typeclasses] calls type classes resolution. *)
Definition solve_typeclasses : t@{Set} unit.
  refine mkt. Qed.

(** [print s] prints string [s] to stdout. *)
Definition print : string -> t@{Set} unit.
  refine (fun _=>mkt). Qed.

(** [pretty_print e] converts term [e] to string. *)
Definition pretty_print@{a} : forall{A: Type@{a}}, A -> t@{Set} string.
  refine (fun _ _ =>mkt). Qed.

(** [hyps] returns the list of hypotheses. *)
Definition hyps@{b c}: t@{c} (mlist@{c} Hyp@{b}).
  refine mkt. Qed.

Definition destcase@{a c1 c2 d}: forall{A: Type@{a}} (a: A), t@{d} (Case@{c1 c2}).
  refine (fun _ _ =>mkt). Qed.

(** Given an inductive type A, applied to all its parameters (but not
    necessarily indices), it returns the type applied to exactly the
    parameters, and a list of constructors (applied to the parameters). *)
Definition constrs@{a c}: forall{A: Type@{a}} (a: A), t@{c} (mprod@{c c} dyn@{c} (mlist@{c} dyn@{c})).
  refine (fun _ _ =>mkt). Qed.

Definition makecase@{c1 c2}: forall(C: Case@{c1 c2}), t@{c2} dyn@{c2}.
  refine (fun _ =>mkt). Qed.

(** [munify x y r] uses reduction strategy [r] to equate [x] and [y].
    It uses convertibility of universes, meaning that it fails if [x]
    is [Prop] and [y] is [Type@{I}]. If they are both types, it will
    try to equate its leveles. *)
Definition unify@{a} {A: Type@{a}} (x y: A) : Unification -> t@{a} (moption@{a} (meq@{a} x y)).
  refine (fun _=>mkt). Qed.

(** [munify_univ A B r] uses reduction strategy [r] to equate universes
    [A] and [B].  It uses cumulativity of universes, e.g., it succeeds if
    [x] is [Prop] and [y] is [Type@{I}]. *)
Definition unify_univ@{a b c} (A: Type@{a}) (B: Type@{b}) : Unification -> t@{c} (moption@{c} (A->B)).
  refine (fun _=>mkt). Qed.

(** [get_reference s] returns the constant that is reference by s. *)
Definition get_reference@{a}: string -> t@{a} dyn@{a}.
  refine (fun _=>mkt). Qed.

(** [get_var s] returns the var named after s. *)
Definition get_var@{a}: string -> t@{a} dyn@{a}.
  refine (fun _=>mkt). Qed.

Definition call_ltac : forall{A: Type}, string->mlist dyn -> t (mprod A (mlist goal)).
  refine (fun _ _ _ =>mkt). Qed.

Definition list_ltac: t@{Set} unit.
  refine mkt. Qed.

(** [read_line] returns the string from stdin. *)
Definition read_line: t@{Set} string.
  refine mkt. Qed.

(** [break f t] calls [f] at each step of the computation of [t]. [f]
    is expcted to return the term that receives as argument, or any
    transformation of it. *)
Definition break' : forall (S : Type -> Prop),
  (forall a : Type, S a -> t a) ->
  (forall A : Type, S A -> t (S A)) -> forall {A : Type}, S A -> t A.
  refine (fun _ _ _ _ _ =>mkt). Qed.


(** [decompose x] decomposes value [x] into a head and a spine of
    arguments. For instance, [decompose (3 + 3)] returns
    [(Dyn add, [Dyn 3; Dyn 3])] *)
Definition decompose@{a} : forall {A: Type@{a}}, A -> t@{a} (mprod@{a a} dyn@{a} (mlist@{a} dyn@{a})).
  refine (fun _ _  =>mkt). Qed.

(** [solve_typeclass A] calls type classes resolution for [A] and returns the result or fail. *)
Definition solve_typeclass@{a} : forall (A:Type@{a}), t@{a} (moption@{a} A).
  refine (fun _  =>mkt). Qed.

(** [declare dok name opaque t] defines [name] as definition kind
    [dok] with content [t] and opacity [opaque] *)
Definition declare@{a}: forall (dok: definition_object_kind)
                   (name: string)
                   (opaque: bool),
    forall{A : Type@{a}}, A -> t@{a} A.
  refine (fun _ _ _ _ _ =>mkt). Qed.

(** [declare_implicits r l] declares implicit arguments for global
    reference [r] according to [l] *)
Definition declare_implicits@{a}: forall {A: Type@{a}} (a : A),
    mlist@{Set} implicit_arguments -> t@{Set} unit.
  refine (fun _ _ _ => mkt). Qed.

(** [os_cmd cmd] executes the command and returns its error number. *)
Definition os_cmd: string -> t@{Set} Z.
  refine (fun _ => mkt). Qed.

Arguments t _%type.

Definition fmap@{a b} {A:Type@{a}} {B:Type@{b}} (f : A -> B) (x : t@{a} A) : t@{b} B :=
  bind x (fun a => ret (f a)).
Definition fapp@{a b} {A:Type@{a}} {B:Type@{b}} (f : t@{b} (A -> B)) (x : t@{b} A) : t@{b} B :=
  bind f (fun g => fmap g x).

Definition Cevar (A : Type) (ctx : mlist Hyp) : t A := gen_evar A (mSome ctx).
Definition evar@{a b} (A : Type@{a}) : t@{a} A := gen_evar@{a Set b} A mNone.

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

Fixpoint open_pattern@{a1 a2 a3 I K a b} {A P y} (p : pattern@{a1 a2 a3} t A P y) : t@{a2} (P y) :=
  match p with
  | pbase x f u =>
    oeq <- unify x y u;
    match oeq return t (P y) with
    | mSome eq =>
      (* eq has type x =m= t, but for the pattern we need t = x.
         we still want to provide eq_refl though, so we reduce it *)
      let h := (* reduce@{b1 b2 b3} (RedWhd [rl:RedBeta;RedDelta;RedMatch]) *) (meq_sym@{a1 K} eq) in
      let 'meq_refl := eq in
      (* For some reason, we need to return the beta-reduction of the pattern, or some tactic fails *)
      let b := (* reduce@{b1 b2 b3} (RedWhd [rl:RedBeta]) *) (f h) in b
    | mNone => raise DoesNotMatch
    end
  | @ptele _ _ _ _ C f => e <- evar@{a b} C; open_pattern (f e)
  end.

Fixpoint mmatch'@{a1 a2 a3 a b I K J} {A:Type@{a1}} {P:A->Type@{a2}} (y : A) (ps : mlist@{J} (pattern@{a1 a2 a3} t A P y)) : t@{a2} (P y) :=
  match ps with
  | [m:] => raise NoPatternMatches
  | p :m: ps' =>
    mtry'@{a1} (open_pattern@{a1 a2 a3 a b I K} p) (fun e =>
      bind@{Set a1} (unify e DoesNotMatch UniMatchNoRed) (fun b=>
      if b then mmatch' y ps' else raise e))
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
Definition mwith {A B} (c : A) (n : string) (v : B) : t dynr :=
  (mfix1 app (d : dynr) : M _ :=
    let (ty, el) := d in
    mmatch d with
    | [? T1 T2 f] @Dynr (forall x:T1, T2 x) f =>
      let ty := reduce (RedWhd [rl:RedBeta]) ty in
      binder <- get_binder_name ty;
      mif unify binder n UniMatchNoRed then
        oeq' <- unify B T1 UniCoq;
        match oeq' with
        | mSome eq' =>
          let v' := reduce (RedWhd [rl:RedMatch]) match eq' as x in _ =m= x with meq_refl=> v end in
          ret (Dynr (f v'))
        | _ => raise (WrongType T1)
        end
      else
        e <- evar T1;
        app (Dynr (f e))
    | _ => raise (NameNotFound n)
    end
  ) (Dynr c).

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

Definition names_of_hyp@{I J} : t@{I} (mlist@{Set} string) :=
  env <- hyps@{I J};
  mfold_left@{Set J} (fun (ns : t@{Set} (mlist@{Set} string)) '(ahyp var _) =>
    fmap mcons@{Set} (get_binder_name@{J} var) <*> ns) env (ret@{Set} [m:]).

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

Definition fresh_name(*@{H I J R1 R2}*) (name: string) : t(*@{H I J}*) string :=
  names <- names_of_hyp(*@{H I J}*);
  let find name : t(*@{H I J}*) bool :=
    let res := reduce(*@{R1 R2 Set}*) RedNF (mfind (fun n => dec_bool (string_dec name n)) names) in
    match res with mNone => ret false | _ => ret true end
  in
  (mfix1 f (name: string) : M string :=
     mif find name then
       let name := reduce(*@{R1 R2 Set}*) RedNF (name ++ "_")%string in
       f name
     else ret name) name.

Definition fresh_binder_name(*@{H I J R1 R2}*) {A:Type(*(*@{I}*)*)} (x : A) : t(*@{H I J}*) string :=
  bind(*@{H I J}*) (mtry'(*@{H I J}*) (get_binder_name(*@{H I J}*) x) (fun _ => ret "x"%string)) (fun name=>
  fresh_name(*@{H I J R1 R2}*) name).

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
Definition dyn_to_goal (d : dyn) : t goal :=
  mmatch d with
  | [? A x] @Dyn A x => ret (Goal x)
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
  ''(m: (Dyn h), _) <- decompose x;
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
  (elemr (ltac:(mrun (M.mwith t k u)))) (at level 0).


(** Execution of tactics at unification *)
Polymorphic Definition lift {A} (f: M A) (v : A) := A.



(** creation of exceptions *)
Definition new_exception name := M.declare dok_Definition name true exception;; M.ret tt.
Notation "'new' 'exception' n" := (M.eval (h <- M.get_binder_name (fun n=>n);
                                           new_exception h)) (at level 0, n at next level).
