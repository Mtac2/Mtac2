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

(* From MetaCoq Require Export Types. *)

(* Set Universe Polymorphism. *)
Unset Universe Minimization ToSet.

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


Polymorphic Record dyn := Dyn { type : Type; elem :> type }.
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

Polymorphic Record Case :=
    mkCase {
        case_ind : Type;
        case_val : case_ind;
        case_return : dyn;
        case_branches : list dyn
        }.

(* Reduction primitive. It throws [NotAList] if the list of flags is not a list.  *)
Definition reduce (r : Reduction) {A} (x : A) := x.

(** goal type *)
Polymorphic Inductive goal :=
| Goal : forall {A}, A -> goal
| AHyp : forall {A}, option A -> (A -> goal) -> goal.

(** THE definition of MetaCoq *)
Set Printing Universes.
Unset Printing Notations.

Inductive Mtac : Type -> Prop :=
| ret : forall {A : Type}, A -> Mtac A
| bind : forall {A : Type} {B : Type},
    Mtac A -> (A -> Mtac B) -> Mtac B
| ttry : forall {A : Type}, Mtac A -> (Exception -> Mtac A) -> Mtac A
| raise : forall {A : Type}, Exception -> Mtac A
| tfix1' : forall {A : Type} {B : A -> Type} (S : Type -> Prop),
  (forall a : Type, S a -> Mtac a) ->
  ((forall x : A, S (B x)) -> (forall x : A, S (B x))) ->
  forall x : A, Mtac (B x)
| tfix2' : forall {A1 : Type} {A2 : A1 -> Type} {B : forall (a1 : A1), A2 a1 -> Type} (S : Type -> Prop),
  (forall a : Type, S a -> Mtac a) ->
  ((forall (x1 : A1) (x2 : A2 x1), S (B x1 x2)) ->
    (forall (x1 : A1) (x2 : A2 x1), S (B x1 x2))) ->
  forall (x1 : A1) (x2 : A2 x1), Mtac (B x1 x2)
| tfix3' : forall {A1 : Type} {A2 : A1 -> Type}  {A3 : forall (a1 : A1), A2 a1 -> Type} {B : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type} (S : Type -> Prop),
  (forall a : Type, S a -> Mtac a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), S (B x1 x2 x3)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), S (B x1 x2 x3))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), Mtac (B x1 x2 x3)
| tfix4' : forall {A1 : Type} {A2 : A1 -> Type} {A3 : forall (a1 : A1), A2 a1 -> Type} {A4 : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type} {B : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2), A4 a1 a2 a3 -> Type} (S : Type -> Prop),
  (forall a : Type, S a -> Mtac a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), S (B x1 x2 x3 x4)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), S (B x1 x2 x3 x4))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), Mtac (B x1 x2 x3 x4)
| tfix5' : forall {A1 : Type} {A2 : A1 -> Type} {A3 : forall (a1 : A1), A2 a1 -> Type} {A4 : forall (a1 : A1) (a2 : A2 a1), A3 a1 a2 -> Type} {A5 : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2), A4 a1 a2 a3 -> Type} {B : forall (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2) (a4 : A4 a1 a2 a3), A5 a1 a2 a3 a4 -> Type} (S : Type -> Prop),
  (forall a : Type, S a -> Mtac a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), S (B x1 x2 x3 x4 x5)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), S (B x1 x2 x3 x4 x5))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), Mtac (B x1 x2 x3 x4 x5)

(** [is_var e] returns if [e] is a variable. *)
| is_var : forall {A : Type}, A -> Mtac bool

(* [nu x od f] executes [f x] where variable [x] is added to the local context,
   optionally with definition [d] with [od = Some d].  It raises
   [NameExistsInContext] if the name "x" is in the context, or
   [VarAppearsInValue] if executing [f x] results in a term containing variable
   [x]. *)
| nu : forall {A : Type} {B : Type}, string -> option A -> (A -> Mtac B) -> Mtac B

(** [abs_fun x e] abstracts variable [x] from [e]. It raises [NotAVar[] if [x]
    is not a variable, or [AbsDependencyError] if [e] or its type [P] depends on
    a variable also depending on [x]. *)
| abs_fun : forall {A : Type} {P : A -> Type} (x : A), P x -> Mtac (forall x, P x)

(** [abs_let x d e] returns [let x := d in e]. It raises [NotAVar] if [x] is not
    a variable, or [AbsDependencyError] if [e] or its type [P] depends on a
    variable also depending on [x]. *)
| abs_let : forall {A : Type} {P : A -> Type} (x: A) (t: A), P x -> Mtac (let x := t in P x)

(** [abs_prod x e] returns [forall x, e]. It raises [NotAVar] if [x] is not a
    variable, or [AbsDependencyError] if [e] or its type [P] depends on a
    variable also depending on [x]. *)
| abs_prod : forall {A : Type} (x : A), Type -> Mtac Type

(** [abs_fix f t n] returns [fix f {struct n} := t].
    [f]'s type must have n products, that is, be [forall x1, ..., xn, T] *)
| abs_fix : forall {A : Type}, A -> A -> N -> Mtac A

(** [get_binder_name t] returns the name of variable [x] if:
    - [t = x],
    - [t = forall x, P x],
    - [t = fun x=>b],
    - [t = let x := d in b].
    It raises [WrongTerm] in any other case.
*)
| get_binder_name : forall {A : Type}, A -> Mtac string

(** [remove x t] executes [t] in a context without variable [x].
    Raises [NotAVar] if [x] is not a variable, and
    [CannotRemoveVar "x"] if [t] or the environment depends on [x]. *)
| remove : forall {A : Type} {B : Type}, A -> Mtac B -> Mtac B

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
| evar : forall (A : Type), option (list Hyp) -> Mtac A

(** [is_evar e] returns if [e] is a meta-variable. *)
| is_evar : forall {A : Type}, A -> Mtac bool

(** [hash e n] returns a number smaller than [n] representing
    a hash of term [e] *)
| hash : forall {A : Type}, A -> N -> Mtac N

(** [solve_typeclasses] calls type classes resolution. *)
| solve_typeclasses : Mtac unit

(** [print s] prints string [s] to stdout. *)
| print : string -> Mtac unit

(** [pretty_print e] converts term [e] to string. *)
| pretty_print : forall {A : Type}, A -> Mtac string

(** [hypotheses] returns the list of hypotheses. *)
| hypotheses : Mtac (list Hyp)

| destcase : forall {A : Type} (a : A), Mtac (Case)

(** Given an inductive type A, applied to all its parameters (but not *)
(*     necessarily indices), it returns the type applied to exactly the *)
(*     parameters, and a list of constructors (applied to the parameters). *)
| constrs : forall {A : Type} (a : A), Mtac (prod dyn (list dyn))
| makecase : forall (C : Case), Mtac dyn

(** [munify x y r] uses reduction strategy [r] to equate [x] and [y].
    It uses convertibility of universes, meaning that it fails if [x]
    is [Prop] and [y] is [Type]. If they are both types, it will
    try to equate its leveles. *)
| munify {A} (x y : A) : Unification -> Mtac (option (x = y))

(** [munify_univ A B r] uses reduction strategy [r] to equate universes
    [A] and [B].  It uses cumulativity of universes, e.g., it succeeds if
    [x] is [Prop] and [y] is [Type]. *)
| munify_univ (A B : Type) : Unification -> Mtac (option (A -> B))

(** [get_reference s] returns the constant that is reference by s. *)
| get_reference : string -> Mtac dyn

(** [get_var s] returns the var named after s. *)
| get_var : string -> Mtac dyn

| call_ltac : forall {A : Type}, string -> list dyn -> Mtac (prod A (list goal))
| list_ltac : Mtac unit
.

Arguments Mtac (_%type).

Definition failwith {A} s : Mtac A := raise (Failure s).

Definition tfix1 {A} B := @tfix1' A B Mtac (fun _ x => x).
Definition tfix2 {A1 A2} B := @tfix2' A1 A2 B Mtac (fun _ x => x).
Definition tfix3 {A1 A2 A3} B := @tfix3' A1 A2 A3 B Mtac (fun _ x => x).
Definition tfix4 {A1 A2 A3 A4} B := @tfix4' A1 A2 A3 A4 B Mtac (fun _ x => x).
Definition tfix5 {A1 A2 A3 A4 A5} B := @tfix5' A1 A2 A3 A4 A5 B Mtac (fun _ x => x).

(** Defines [eval f] to execute after elaboration the Mtactic [f].
    It allows e.g. [rewrite (eval f)]. *)
Class runner A  (f : Mtac A) := { eval : A }.
Arguments runner {A} _.
Arguments Build_runner {A} _ _.
Arguments eval {A} _ {_}.

Hint Extern 20 (runner ?f) =>
  (exact (Build_runner f ltac:(mrun f)))  : typeclass_instances.

Definition print_term {A} (x: A) : Mtac unit :=
  bind (pretty_print x) (fun s=> print s).


Module MtacNotations.

Bind Scope Mtac_scope with Mtac.
Delimit Scope Mtac_scope with MC.
Open Scope Mtac_scope.

Notation M := Mtac.

Notation RedAll := ([RedBeta;RedDelta;RedZeta;RedMatch;RedFix]).
Notation RedNF := (RedStrong RedAll).
Notation RedHNF := (RedWhd RedAll).

Notation rsimpl := (reduce RedSimpl).
Notation rhnf := (reduce RedHNF).
Notation rcbv := (reduce RedNF).
Notation rone_step := (reduce RedOneStep).

Notation "r '<-' t1 ';' t2" := (@bind _ _ t1 (fun r=> t2%MC))
  (at level 81, right associativity, format "'[' r  '<-'  '[' t1 ;  ']' ']' '/' t2 ") : Mtac_scope.
Notation "t1 ';;' t2" := (@bind _ _ t1 (fun _=>t2%MC))
  (at level 81, right associativity, format "'[' '[' t1 ;;  ']' ']' '/' t2 ") : Mtac_scope.
Notation "t >>= f" := (bind t f) (at level 70) : Mtac_scope.
Open Scope string.

(* We cannot make this notation recursive, so we loose
   notation in favor of naming. *)
Notation "'\nu' x , a" := (
  let f := fun x=>a in
  n <- get_binder_name f;
  nu n None f) (at level 81, x at next level, right associativity) : Mtac_scope.

Notation "'\nu' x : A , a" := (
  let f := fun x:A=>a in
  n <- get_binder_name f;
  nu n None f) (at level 81, x at next level, right associativity) : Mtac_scope.

Notation "'\nu' x := t , a" := (
  let f := fun x=>a in
  n <- get_binder_name f;
  nu n (Some t) f) (at level 81, x at next level, right associativity) : Mtac_scope.

Notation "'mfix1' f ( x : A ) : 'M' T := b" := (tfix1 (fun x=>T%type) (fun f (x : A)=>b%MC))
  (at level 85, f at level 0, x at next level, format
  "'[v  ' 'mfix1'  f  '(' x  ':'  A ')'  ':'  'M'  T  ':=' '/  ' b ']'").

Notation "'mfix2' f ( x : A ) ( y : B ) : 'M' T := b" :=
  (tfix2 (fun (x : A) (y : B)=>T%type) (fun f (x : A) (y : B)=>b%MC))
  (at level 85, f at level 0, x at next level, y at next level, format
  "'[v  ' 'mfix2'  f  '(' x  ':'  A ')'  '(' y  ':'  B ')'  ':'  'M'  T  ':=' '/  ' b ']'").

Notation "'mfix3' f ( x : A ) ( y : B ) ( z : C ) : 'M' T := b" :=
  (tfix3 (fun (x : A) (y : B) (z : C)=>T%type) (fun f (x : A) (y : B) (z : C)=>b%MC))
  (at level 85, f at level 0, x at next level, y at next level, z at next level, format
  "'[v  ' 'mfix3'  f  '(' x  ':'  A ')'  '(' y  ':'  B ')'  '(' z  ':'  C ')'  ':'  'M'  T  ':=' '/  ' b ']'").

Notation "'mfix4' f ( x1 : A1 ) ( x2 : A2 ) ( x3 : A3 ) ( x4 : A4 ) : 'M' T := b" :=
  (tfix4 (fun (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4)=>T%type) (fun f (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4) =>b%MC))
  (at level 85, f at level 0, x1 at next level, x2 at next level, x3 at next level, x4 at next level, format
  "'[v  ' 'mfix4'  f  '(' x1  ':'  A1 ')'  '(' x2  ':'  A2 ')'  '(' x3  ':'  A3 ')'  '(' x4  ':'  A4 ')'  ':'  'M'  T  ':=' '/  ' b ']'").

Notation "'mfix5' f ( x1 : A1 ) ( x2 : A2 ) ( x3 : A3 ) ( x4 : A4 ) ( x5 : A5 ) : 'M' T := b" :=
  (tfix5 (fun (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4) (x5 : A5)=>T%type) (fun f (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4) (x5 : A5) =>b%MC))
  (at level 85, f at level 0, x1 at next level, x2 at next level, x3 at next level, x4 at next level, x5 at next level, format
  "'[v  ' 'mfix5'  f  '(' x1  ':'  A1 ')'  '(' x2  ':'  A2 ')'  '(' x3  ':'  A3 ')'  '(' x4  ':'  A4 ')'  '(' x5  ':'  A5 ')'  ':'  'M'  T  ':=' '/  ' b ']'").


Definition type_inside {A} (x : M A) := A.


Definition DoesNotMatch : Exception. exact exception. Qed.
Definition NoPatternMatches : Exception. exact exception. Qed.
Definition Anomaly : Exception. exact exception. Qed.
Definition Continue : Exception. exact exception. Qed.

(** Pattern matching without pain *)
Polymorphic Inductive pattern A (B : A -> Type) (t : A) : Prop :=
| pbase : forall (x:A), (t = x -> Mtac (B x)) -> Unification -> pattern A B t
| ptele : forall {C}, (forall (x : C), pattern A B t) -> pattern A B t.

Polymorphic Fixpoint open_pattern {A P t} (p : pattern A P t) : M (P t) :=
  match p with
  | pbase _ _ _ x f u =>
    oeq <- munify x t u;
    match oeq return M (P t) with
    | Some eq =>
        (* eq has type x = t, but for the pattern we need t = x.
           we still want to provide eq_refl though, so we reduce it *)
        let h := reduce (RedStrong [RedBeta;RedDelta;RedMatch]) (eq_sym eq) in
        match eq in _ = x return M (P x) with
        | eq_refl =>
          (* For some reason, we need to return the beta-reduction of the pattern, or some tactic fails *)
          let b := reduce (RedStrong [RedBeta]) (f h) in b
        end
    | None => raise DoesNotMatch
    end
  | @ptele _ _ _ C f =>
    e <- evar C None;
    open_pattern (f e)
  end.

Polymorphic Fixpoint tmatch {A P} t (ps : list (pattern A P t)) : M (P t) :=
  match ps with
  | [] => raise NoPatternMatches
  | (p :: ps') =>
    ttry (open_pattern p) (fun e=>
      oeq <- munify e DoesNotMatch UniMatchNoRed;
      if oeq then tmatch t ps' else raise e
    )
  end.

Arguments ptele {A B t C} _.
Arguments pbase {A B t} _ _ _.


Notation "[? x .. y ] ps" := (ptele (fun x=> .. (ptele (fun y=>ps)).. ))
  (at level 202, x binder, y binder, ps at next level) : metaCoq_pattern_scope.
Notation "p => b" := (pbase p%core (fun _=>b%core) UniMatch)
  (no associativity, at level 201) : metaCoq_pattern_scope.
Notation "p => [ H ] b" := (pbase p%core (fun H=>b%core) UniMatch)
  (no associativity, at level 201, H at next level) : metaCoq_pattern_scope.
Notation "'_' => b " := (ptele (fun x=> pbase x (fun _=>b%core) UniMatch))
  (at level 201, b at next level) : metaCoq_pattern_scope.

Notation "p '=n>' b" := (pbase p%core (fun _=>b%core) UniMatchNoRed)
  (no associativity, at level 201) : metaCoq_pattern_scope.
Notation "p '=n>' [ H ] b" := (pbase p%core (fun H=>b%core) UniMatchNoRed)
  (no associativity, at level 201, H at next level) : metaCoq_pattern_scope.

Notation "p '=u>' b" := (pbase p%core (fun _=>b%core) UniCoq)
  (no associativity, at level 201) : metaCoq_pattern_scope.
Notation "p '=u>' [ H ] b" := (pbase p%core (fun H=>b%core) UniCoq)
  (no associativity, at level 201, H at next level) : metaCoq_pattern_scope.

Delimit Scope metaCoq_pattern_scope with metaCoq_pattern.

Notation "'with' | p1 | .. | pn 'end'" :=
  ((@cons (pattern _ _ _) p1%metaCoq_pattern (.. (@cons (pattern _ _ _) pn%metaCoq_pattern nil) ..)))
    (at level 91, p1 at level 210, pn at level 210) : mmatch_with.
Notation "'with' p1 | .. | pn 'end'" :=
  ((@cons (pattern _ _ _) p1%metaCoq_pattern (.. (@cons (pattern _ _ _) pn%metaCoq_pattern nil) ..)))
    (at level 91, p1 at level 210, pn at level 210) : mmatch_with.

Delimit Scope mmatch_with with mmatch_with.

Notation "'mmatch' x ls" := (@tmatch _ (fun _=>_) x ls%mmatch_with)
  (at level 90, ls at level 91) : Mtac_scope.
Notation "'mmatch' x 'return' 'M' p ls" := (@tmatch _ (fun x=>p) x ls%mmatch_with)
  (at level 90, ls at level 91) : Mtac_scope.
Notation "'mmatch' x 'as' y 'return' 'M' p ls" := (@tmatch _ (fun y=>p) x ls%mmatch_with)
  (at level 90, ls at level 91) : Mtac_scope.

Notation "'mtry' a ls" :=
  (ttry a (fun e=>
    (@tmatch _ (fun _=>_) e (app ls%mmatch_with (cons ([? x] x=>raise x)%metaCoq_pattern nil)))))
    (at level 82, a at level 100, ls at level 91, only parsing).

Definition Cevar (A : Type) (ctx : list Hyp) : M A := evar A (Some ctx).
Definition evar (A : Type) : M A := evar A None.

Notation "'mif' b 'then' t 'else' u" :=
  (cond <- b; if cond then t else u) (at level 200).

End MtacNotations.

Section GeneralUtilities.
Import MtacNotations.

Definition munify_cumul {A B} (x: A) (y: B) (u : Unification) : Mtac bool :=
  of <- munify_univ A B u;
  match of with
  | Some f =>
    let fx := reduce RedOneStep (f x) in
    oeq <- munify fx y u;
    match oeq with Some _ => ret true | None => ret false end
  | None => ret false
  end.

Definition names_of_hyp : M (list string) :=
  env <- hypotheses;
  fold_left (fun (ns:M (list string)) (h:Hyp)=>
    let (_, var, _) := h in
    n <- get_binder_name var;
    r <- ns; ret (n::r)) env (ret []).

Definition fresh_name (name: string) : M string :=
  names <- names_of_hyp;
  let find name : M bool :=
    let res := reduce RedNF (find (fun n => dec_bool (string_dec name n)) names) in
    match res with None => ret false | _ => ret true end
  in
  (mfix1 f (name: string) : M string :=
     mif find name then
       let name := reduce RedNF (name++"_") in
       f name
     else ret name) name.

Definition fresh_binder_name {A} (t: A) : M string :=
  name <- mtry get_binder_name t with WrongTerm=> ret "x" end;
  fresh_name name.

Definition unfold_projection {A} (t: A) : M A :=
  let x := rone_step t in
  let x := reduce (RedWhd (RedBeta::RedMatch::nil)) x in ret x.

Definition mid {A} (x: A) : M A := ret x.
End GeneralUtilities.
