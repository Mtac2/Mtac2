Require Import Strings.String.
Require Import NArith.BinNat.
From Mtac2 Require Import Logic Datatypes Logic List Utils Sorts MTele Pattern.
Import Sorts.
Import ListNotations.
Import ProdNotations.
From Mtac2.intf Require Export Exceptions Dyn Reduction Unification DeclarationDefs Goals Case Tm_kind Name.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

(** THE definition of the monad *)
Unset Printing Notations.

Module M.

Inductive t : Type -> Prop := mkt : forall{a}, t a.

Local Ltac make := refine (mkt) || (intro; make).

Definition ret : forall {A : Type}, A -> t A.
  make. Qed.

Definition bind : forall {A : Type} {B : Type}, t A -> (A -> t B) -> t B.
  make. Qed.

Definition mtry' : forall {A : Type}, t A -> (Exception -> t A) -> t A.
  make. Qed.

Definition raise' : forall {A : Type}, Exception -> t A.
  make. Qed.

Definition fix1 : forall{A: Type} (B: A->Type),
  ((forall x: A, t (B x))->(forall x: A, t (B x))) ->
  forall x: A, t (B x).
  make. Qed.

Definition fix2 : forall {A1: Type} {A2: A1->Type} (B: forall (a1 : A1), A2 a1->Type),
  ((forall (x1: A1) (x2: A2 x1), t (B x1 x2)) ->
    (forall (x1: A1) (x2: A2 x1), t (B x1 x2))) ->
  forall (x1: A1) (x2: A2 x1), t (B x1 x2).
  make. Qed.

Definition fix3 : forall {A1: Type} {A2: A1->Type} {A3 : forall (a1: A1), A2 a1->Type} (B: forall (a1: A1) (a2: A2 a1), A3 a1 a2->Type),
  ((forall (x1: A1) (x2: A2 x1) (x3: A3 x1 x2), t (B x1 x2 x3)) ->
    (forall (x1: A1) (x2: A2 x1) (x3: A3 x1 x2), t (B x1 x2 x3))) ->
  forall (x1: A1) (x2: A2 x1) (x3: A3 x1 x2), t (B x1 x2 x3).
  make. Qed.

Definition fix4 : forall {A1: Type} {A2: A1->Type} {A3: forall (a1: A1), A2 a1->Type} {A4: forall (a1: A1) (a2: A2 a1), A3 a1 a2->Type} (B: forall (a1: A1) (a2: A2 a1) (a3: A3 a1 a2), A4 a1 a2 a3->Type),
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), t (B x1 x2 x3 x4)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), t (B x1 x2 x3 x4))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), t (B x1 x2 x3 x4).
  make. Qed.

Definition fix5: forall{A1: Type} {A2: A1->Type} {A3: forall(a1: A1), A2 a1->Type} {A4: forall(a1: A1)(a2: A2 a1), A3 a1 a2->Type} {A5: forall(a1: A1)(a2: A2 a1)(a3: A3 a1 a2), A4 a1 a2 a3->Type} (B: forall(a1: A1)(a2: A2 a1)(a3: A3 a1 a2)(a4: A4 a1 a2 a3), A5 a1 a2 a3 a4->Type),
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), t (B x1 x2 x3 x4 x5)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), t (B x1 x2 x3 x4 x5))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), t (B x1 x2 x3 x4 x5).
  make. Qed.

(** [is_var e] returns if [e] is a variable. *)
Definition is_var: forall{A : Type}, A->t bool.
  make. Qed.

(* [nu x od f] executes [f x] where variable [x] is added to the local context,
   optionally with definition [d] with [od = Some d].  It raises
   [NameExistsInContext] if the name "x" is in the context, or
   [VarAppearsInValue] if executing [f x] results in a term containing variable
   [x]. *)
Definition nu: forall{A: Type}{B: Type}, name -> moption A -> (A -> t B) -> t B.
  make. Qed.

(** [abs_fun x e] abstracts variable [x] from [e]. It raises [NotAVar] if [x]
    is not a variable, or [AbsDependencyError] if [e] or its type [P] depends on
    a variable also depending on [x]. *)
Definition abs_fun: forall{A: Type} {P: A->Type} (x: A), P x -> t (forall x, P x).
  make. Qed.

(** [abs_let x d e] returns [let x := d in e]. It raises [NotAVar] if [x] is not
    a variable, or [AbsDependencyError] if [e] or its type [P] depends on a
    variable also depending on [x]. *)
Definition abs_let: forall{A: Type} {P: A->Type} (x: A) (y: A), P x -> t (let x := y in P x).
  make. Qed.

(** [abs_prod x e] returns [forall x, e]. It raises [NotAVar] if [x] is not a
    variable, or [AbsDependencyError] if [e] or its type [P] depends on a
    variable also depending on [x]. *)
Definition abs_prod_type: forall{A: Type} (x : A), Type -> t Type.
  make. Qed.

(** [abs_prod x e] returns [forall x, e]. It raises [NotAVar] if [x] is not a
    variable, or [AbsDependencyError] if [e] or its type [P] depends on a
    variable also depending on [x]. *)
Definition abs_prod_prop: forall{A: Type} (x : A), Prop -> t Prop.
  make. Qed.

(** [abs_fix f t n] returns [fix f {struct n} := t].
    [f]'s type must have n products, that is, be [forall x1, ..., xn, T] *)
Definition abs_fix: forall{A: Type}, A -> A -> N -> t A.
  make. Qed.

(** [get_binder_name t] returns the name of variable [x] if:
    - [t = x],
    - [t = forall x, P x],
    - [t = fun x=>b],
    - [t = let x := d in b].
    It raises [WrongTerm] in any other case.
*)
Definition get_binder_name: forall{A: Type}, A -> t string.
  make. Qed.

(** [remove x t] executes [t] in a context without variable [x].
    Raises [NotAVar] if [x] is not a variable, and
    [CannotRemoveVar "x"] if [t] or the environment depends on [x]. *)
Definition remove : forall{A: Type} {B: Type}, A -> t B -> t B.
  make. Qed.

(** [gen_evar A ohyps] creates a meta-variable with type [A] and,
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
Definition gen_evar: forall(A: Type), moption (mlist Hyp) -> t A.
  make. Qed.

(** [is_evar e] returns if [e] is a meta-variable. *)
Definition is_evar: forall{A: Type}, A -> t bool.
  make. Qed.

(** [hash e n] returns a number smaller than [n] representing
    a hash of term [e] *)
Definition hash: forall{A: Type}, A -> N -> t N.
  make. Qed.

(** [solve_typeclasses] calls type classes resolution. *)
Definition solve_typeclasses : t unit.
  make. Qed.

(** [print s] prints string [s] to stdout. *)
Definition print : string -> t unit.
  make. Qed.

(** [pretty_print e] converts term [e] to string. *)
Definition pretty_print : forall{A: Type}, A -> t string.
  make. Qed.

(** [hyps] returns the list of hypotheses. *)
Definition hyps: t (mlist Hyp).
  make. Qed.

Definition destcase: forall{A: Type} (a: A), t (Case).
  make. Qed.

(** Given an inductive type A, applied to all its parameters (but not
    necessarily indices), it returns the type applied to exactly the
    parameters, and a list of constructors (applied to the parameters). *)
Definition constrs: forall{A: Type} (a: A), t (mprod dyn (mlist dyn)).
  make. Qed.

Definition makecase: forall(C: Case), t dyn.
  make. Qed.

(** [munify x y r] uses reduction strategy [r] to equate [x] and [y].
    It uses convertibility of universes, meaning that it fails if [x]
    is [Prop] and [y] is [Type]. If they are both types, it will
    try to equate its leveles. *)
Definition unify {A: Type} (x y: A) : Unification -> t (moption (meq x y)).
  make. Qed.

(** [munify_univ A B r] uses reduction strategy [r] to equate universes
    [A] and [B].  It uses cumulativity of universes, e.g., it succeeds if
    [x] is [Prop] and [y] is [Type]. *)
Definition unify_univ (A: Type) (B: Type) : Unification -> t (moption (A->B)).
  make. Qed.

(** [get_reference s] returns the constant that is reference by s. *)
Definition get_reference: string -> t dyn.
  make. Qed.

(** [get_var s] returns the var named after s. *)
Definition get_var: string -> t dyn.
  make. Qed.

Definition call_ltac : forall(sort: Sort) {A: sort}, string->mlist dyn -> t (mprod A (mlist goal)).
  make. Qed.

Definition list_ltac: t unit.
  make. Qed.

(** [read_line] returns the string from stdin. *)
Definition read_line: t string.
  make. Qed.

(** [decompose x] decomposes value [x] into a head and a spine of
    arguments. For instance, [decompose (3 + 3)] returns
    [(Dyn add, [Dyn 3; Dyn 3])] *)
Definition decompose : forall {A: Type}, A -> t (mprod dyn (mlist dyn)).
  make. Qed.

(** [solve_typeclass A] calls type classes resolution for [A] and returns the result or fail. *)
Definition solve_typeclass : forall (A:Type), t (moption A).
  make. Qed.

(** [declare dok name opaque t] defines [name] as definition kind
    [dok] with content [t] and opacity [opaque] *)
Definition declare: forall (dok: definition_object_kind)
                   (name: string)
                   (opaque: bool),
    forall{A : Type}, A -> t A.
  make. Qed.

(** [declare_implicits r l] declares implicit arguments for global
    reference [r] according to [l] *)
Definition declare_implicits: forall {A: Type} (a : A),
    mlist implicit_arguments -> t unit.
  make. Qed.

(** [os_cmd cmd] executes the command and returns its error number. *)
Definition os_cmd: string -> t Z.
  make. Qed.

Definition get_debug_exceptions: t bool.
  make. Qed.
Definition set_debug_exceptions: bool -> t unit.
  make. Qed.

Definition get_trace: t bool.
  make. Qed.
Definition set_trace: bool -> t unit.
  make. Qed.

(** [decompose_app' uni a (h u .. w) (fun x .. z => t)] executes
    [t[i..k/x..z]] iff [a] is [H u' .. w' i .. k]
    where [u' .. w'] unify with [u .. w] according to the
    unification stragety [uni].
 *)
Definition decompose_app' :
  forall {A : Type} {B : A -> Type} {m} (uni : Unification) (a : A) (C : MTele_ConstT A m),
    MTele_sort (MTele_ConstMap (si := SType) SProp (T:=A) (fun a => t (B a)) C) ->
    t (B a).
  make. Qed.

(** [decompose_forallT T (fun A B => t)] executes [t[A'/A, B'/B]] iff T is
    [forall a : A, B']. *)
Definition decompose_forallT :
  forall {A : Type} {B : Type -> Type} (T : Type),
    (forall (A : Type) (b : A -> Type), t (B (forall a : A, b a))) ->
    t (B T).
  make. Qed.

(** [decompose_forallP T (fun A B => t)] executes [t[A'/A, B'/B]] iff T is
    [forall a : A, B'] and [B'].

    This is a specialized version of [decompose_forallT] that makes sure to not
    insert any casts from [Prop] to [Type]. *)
Definition decompose_forallP :
  forall {A : Type} {B : Prop -> Type} (P : Prop),
    (forall (A : Type) (b : A -> Prop), t (B (forall a : A, b a))) ->
    t (B P).
  make. Qed.

(** [decompose_app'' m (fun A B f x => t)] executes [A' .. x'/A .. x] iff m is
    [f x] with [f : forall a : A, B a] and [x : A]. *)
Definition decompose_app'' :
  forall {S : forall T, T -> Type} {T : Type} (m : T),
    (forall A (B : A -> Type) (f : forall a, B a) (a : A), t (S _ (f a))) ->
    t (S T m).
  make. Qed.

Definition new_timer : forall {A} (a : A), t unit.
  make. Qed.

Definition start_timer : forall {A} (a : A) (reset : bool), t unit.
  make. Qed.

Definition stop_timer : forall {A} (a : A), t unit.
  make. Qed.

Definition reset_timer : forall {A} (a : A), t unit.
  make. Qed.

Definition print_timer : forall {A} (a : A), t unit.
  make. Qed.

(** [kind_of_term t] returns the term kind of t *)
Definition kind_of_term: forall{A: Type}, A -> t tm_kind.
  make. Qed.

Arguments t _%type.

Definition fmap {A:Type} {B:Type} (f : A -> B) (x : t A) : t B :=
  bind x (fun a => ret (f a)).
Definition fapp {A:Type} {B:Type} (f : t (A -> B)) (x : t A) : t B :=
  bind f (fun g => fmap g x).

Definition Cevar (A : Type) (ctx : mlist Hyp) : t A := gen_evar A (mSome ctx).
Definition evar (A : Type) : t A := gen_evar A mNone.


Definition raise {A:Type} (e: Exception): t A :=
  bind get_debug_exceptions (fun b=>
  if b then
    bind (pretty_print e) (fun s=>
    bind (print ("raise " ++ s)) (fun _ =>
    raise' e))
  else
    raise' e).

Definition failwith {A} (s : string) : t A := raise (Failure s).


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
  Notation "` r1 .. rn '<-' t1 ';' t2" := (bind t1 (fun r1 => .. (bind t1 (fun rn => t2)) ..))
    (at level 20, r1 binder, rn binder, t1 at level 100, t2 at level 200,
     right associativity, format "'[' '`' r1  ..  rn  '<-'  '[' t1 ;  ']' ']' '/' t2 ") : M_scope.
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

Fixpoint open_pattern {A P y} (E : Exception) (p : pattern t A P y) : t (P y) :=
  match p with
  | pany b => b
  | pbase x f u =>
    oeq <- unify x y u;
    match oeq return t (P y) with
    | mSome eq =>
      (* eq has type x =m= t, but for the pattern we need t = x.
         we still want to provide eq_refl though, so we reduce it *)
      let h := reduce (RedWhd [rl:RedBeta;RedDelta;RedMatch]) (meq_sym eq) in
      let 'meq_refl := eq in
      (* For some reason, we need to return the beta-reduction of the pattern, or some tactic fails *)
      let b := (* reduce (RedWhd [rl:RedBeta]) *) (f h) in b
    | mNone => raise E
    end
  | @ptele _ _ _ _ C f => e <- evar C; open_pattern E (f e)
  | psort f =>
    mtry'
      (open_pattern E (f SProp))
      (fun e =>
         oeq <- M.unify e E UniMatchNoRed;
         match oeq with
         | mSome _ => open_pattern E (f SType)
         | mNone => raise e
         end
      )
  end.

Fixpoint mmatch' {A:Type} {P:A->Type} (E : Exception) (y : A) (ps : mlist (pattern t A P y)) : t (P y) :=
  match ps with
  | [m:] => raise NoPatternMatches
  | p :m: ps' =>
    mtry' (open_pattern E p) (fun e =>
      bind (unify e E UniMatchNoRed) (fun b=>
      if b then mmatch' E y ps' else raise e))
  end.

Definition NotCaught : Exception. constructor. Qed.

Module notations_pre.
  Export monad_notations.

  (* We cannot make this notation recursive, so we loose
     notation in favor of naming. *)
  Notation "'\nu' x , a" := (
    let f := fun x => a in
    nu (FreshFrom f) mNone f) (at level 200, x ident, a at level 200, right associativity) : M_scope.

  Notation "'\nu' x : A , a" := (
    let f := fun x:A=>a in
    nu (FreshFrom f) mNone f) (at level 200, x ident, a at level 200, right associativity) : M_scope.

  Notation "'\nu' x := t , a" := (
    let f := fun x => a in
    nu (FreshFrom f) (mSome t) f) (at level 200, x ident, a at level 200, right associativity) : M_scope.

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
    (@mmatch' _ (fun _ => _) DoesNotMatch x ls%with_pattern)
    (at level 200, ls at level 91) : M_scope.
  Notation "'mmatch' x 'return' 'M' p ls" :=
    (@mmatch' _ (fun _ => p%type) DoesNotMatch x ls%with_pattern)
    (at level 200, ls at level 91) : M_scope.
  Notation "'mmatch' x 'as' y 'return' 'M' p ls" :=
    (@mmatch' _ (fun y => p%type) DoesNotMatch x ls%with_pattern)
    (at level 200, ls at level 91) : M_scope.

  Notation "'mtry' a ls" :=
    (mtry' a (fun e =>
      (@mmatch' _ (fun _ => _) NotCaught e
                   (mapp ls%with_pattern [m:(e => raise e)%pattern]))))
      (at level 200, a at level 100, ls at level 91, only parsing) : M_scope.

  Import TeleNotation.
  Notation "'dcase' v 'as' A ',' x 'in' t" :=
    (@M.decompose_app' _ (fun _ => _) [tele A (_:A)] UniMatchNoRed v (@Dyn) (fun A x => t)) (at level 91, t at level 200) : M_scope.
  Notation "'dcase' v 'as' x 'in' t" :=
    (dcase v as _ , x in t) (at level 91, t at level 200) : M_scope.
End notations_pre.

Import notations_pre.

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
    let fx := reduce (RedOneStep [rl:RedBeta]) (f x) in
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
    fmap mcons (get_binder_name var) <*> ns) env (ret [m:]).

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

Definition def_binder_name {A:Type} (x : A) : t string :=
  mtry' (get_binder_name x) (fun _ => ret "x"%string).

Fixpoint string_rev_app (s1 s2 : string) :=
  match s1 with
  | EmptyString => s2
  | String c s1 => string_rev_app s1 (String c s2)
  end.

Definition string_rev s := string_rev_app s EmptyString.

(* string_rev_flatten: takes a list of reversed strings and computes
the string that consists of the unreversed strings. *)
Fixpoint string_rev_flatten (ss : mlist string) :=
  match ss with
  | [m:] => EmptyString
  | s :m: ss => string_rev_app s (string_rev_flatten ss)
  end.

Definition fail_strs (l : mlist dyn) : M.t string :=
  fix2 (fun _ _ => string) (fun go l (acc : mlist string) =>
  match l with
  | [m: ] =>
    let r := reduce (RedVmCompute) (string_rev (string_rev_flatten acc)) in
    M.ret r
  | D :m: l =>
    mmatch D with
    | [? s] @Dyn string s =>
      (* let r := reduce (RedVmCompute) (string_rev s) in *)
      go l (s :m: acc)
    | _ =>
      dcase D as t in
      s <- M.pretty_print t;
      (* let r := reduce (RedVmCompute) (string_rev s) in *)
      go l (s :m: acc)
    end
  end) l [m:].


Module notations.
  Export notations_pre.

  Local Definition bind_nu {A B C} (F : A) (a : B -> t C) :=
    M.nu (FreshFrom F) mNone a.

  (* Fresh names. This notation is declared recursive to allow optional type
     annotations but it only works for a single binder *)
  Notation "'\nu_f' 'for' F 'as' x .. z , a " := (
    bind_nu F (fun x => .. (bind_nu F (fun z => a)) .. )
  ) (at level 200, a at level 200, x binder, z binder).

  Local Definition bind_nu_rec {A} {B : A -> Type} {C}
        (a : forall x : A, B x -> t C)
        (F : forall x : A, B x) :=
    M.nu (FreshFrom F) mNone (fun x : A => let F := reduce (RedOneStep [rl: RedBeta]) (F x) in a x F).

  (* Fresh names _m_irroring the shape of the [F]'s type.

     The names will only be related to [F]'s binder names if [F] is
     syntactically equal to [fun x .. z => ..]. Otherwise, the reduction
     strategy will not reduce the term far enough for the next call to
     [fresh_binder_name] to find the correct name.

     This notation is let-expanded because Coq's notation mechanism is unable to
     recognize it as [(<recursive part>) F]. *)
  Notation "'\nu_m' 'for' F 'as' x .. z , a " := (
    let t := (bind_nu_rec (fun x => .. (bind_nu_rec (fun z => fun _ => a)) .. )) in t F
  ) (at level 200, a at level 200, x binder, z binder).

  Notation "'\nu_M' 'for' F 'as' x .. z ; f , a " := (
    let t := (bind_nu_rec (fun x => .. (bind_nu_rec (fun z => fun f => a)) .. )) in t F
  ) (at level 200, a at level 200, x binder, z binder).


  (* This `fail` notation mirrors Ltac's `fail` notation, with one exception: no
  automagic spaces are inserted between the arguments. *)
  Notation "'mfail' s1 .. sn" :=
    ((fail_strs (mcons (Dyn s1) .. (mcons (Dyn sn) mnil) ..)) >>= M.failwith)
      (at level 0, s1 at next level, sn at next level) : M_scope.
End notations.

Definition unfold_projection {A} (y : A) : t A :=
  let x := reduce (RedOneStep [rl:RedDelta]) y in
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
  | @Goal s A x =>
    match s as s return stype_of s -> t Type with
      | SProp => fun A => ret (A:Type)
      | SType => fun A => ret A end A
  | _ => raise NotAGoal
  end.

(** [goal_prop g] extracts the prop of the goal or raises [NotAGoal]
    if [g] is not [Goal], or [CantCoerce] its type can't be cast to a Prop. *)
Definition goal_prop (g : goal) : t Prop :=
  match g with
  | @Goal s A _ =>
    match s as s return forall A:stype_of s, t Prop with
      | SProp => fun A:Prop => ret A
      | SType => fun A:Type =>
        gP <- evar Prop;
        mtry
         cumul_or_fail UniMatch gP A;;
         ret gP
        with _ => raise CantCoerce end (* its better to raise CantCoerce than NotCumul *)
    end A
  | _ => raise NotAGoal
  end.

(** Convertion functions from [dyn] to [goal]. *)
Definition dyn_to_goal (d : dyn) : t goal :=
  mmatch d with
  | [? (A:Prop) x] @Dyn A x => ret (@Goal SProp A x)
  | [? (A:Type) x] @Dyn A x => ret (@Goal SType A x)
  end.

Definition goal_to_dyn (g : goal) : t dyn :=
  match g with
  | Goal _ d => ret (Dyn d)
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
  dcase h as e in
    mif is_evar e then
      let t := reduce (RedWhd [rl:RedBeta]) t in
      r <- unify x y UniEvarconv;
      match r with
      | mSome _ => M.ret tt
      | _ => raise (CantInstantiate x y)
      end
    else raise (NotAnEvar h)
  .

Definition solve_typeclass_or_fail (A : Type) : t A :=
  x <- solve_typeclass A;
  match x with mSome a => M.ret a | mNone => raise (NoClassInstance A) end.

(** Collects obviously visible evars *)
Definition collect_evars {A} (x: A) :=
  res <- (mfix1 f (d: dyn) : M (mlist dyn) :=
    dcase d as e in
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

(** Query functions *)
Definition isVar {A} (x: A) :=
  kind_of_term x >>= fun k=>
  match k with
  | tmVar => ret true
  | _ => ret false
  end.

Definition isEvar {A} (x: A) :=
  kind_of_term x >>= fun k=>
  match k with
  | tmEvar => ret true
  | _ => ret false
  end.

Definition isConst {A} (x: A) :=
  kind_of_term x >>= fun k=>
  match k with
  | tmConst => ret true
  | _ => ret false
  end.

Definition isConstruct {A} (x: A) :=
  kind_of_term x >>= fun k=>
  match k with
  | tmConstruct => ret true
  | _ => ret false
  end.

Definition isApp {A} (x: A) :=
  kind_of_term x >>= fun k=>
  match k with
  | tmApp => ret true
  | _ => ret false
  end.

Definition isLambda {A} (x: A) :=
  kind_of_term x >>= fun k=>
  match k with
  | tmLambda => ret true
  | _ => ret false
  end.

Definition isProd {A} (x: A) :=
  kind_of_term x >>= fun k=>
  match k with
  | tmProd => ret true
  | _ => ret false
  end.

Definition isCast {A} (x: A) :=
  kind_of_term x >>= fun k=>
  match k with
  | tmCast => ret true
  | _ => ret false
  end.

Definition isSort {A} (x: A) :=
  kind_of_term x >>= fun k=>
  match k with
  | tmSort => ret true
  | _ => ret false
  end.

Definition isCase {A} (x: A) :=
  kind_of_term x >>= fun k=>
  match k with
  | tmCase => ret true
  | _ => ret false
  end.

End M.

Notation M := M.t.