(* Need to load Unicoq to get the module dependency right *)
Declare ML Module "unicoq".
(** Load library "MetaCoqPlugin.cma". *)
Declare ML Module "MetaCoqPlugin".

Require Import Strings.String.
Require Import Lists.List.
Require Import NArith.BinNat.
Require Import NArith.BinNatDef.
Import ListNotations.

Module MetaCoq.

Inductive Exception : Type := exception : Exception.

Definition TermNotGround : Exception. exact exception. Qed.

Definition NoPatternMatches : Exception. exact exception. Qed.

Definition WrongTerm : Exception. exact exception. Qed.

Definition MissingDependency : Exception. exact exception. Qed.

Definition LtacError (s:string) : Exception. exact exception. Qed.

Definition NotUnifiable {A} (x y : A) : Exception. exact exception. Qed.

Definition Failure (s : string) : Exception. exact exception. Qed.

Definition NameExistsInContext (s : string) : Exception. exact exception. Qed.

Definition ExceptionNotGround (s : string) : Exception. exact exception. Qed.

Record dyn := Dyn { type : Type; elem : type }.
Arguments Dyn {_} _.

Inductive RedFlags : Set := RedBeta | RedDelta | RedIota | RedZeta.

Inductive Reduction : Set :=
| RedNone
| RedSimpl
| RedOneStep
| RedWhd : list RedFlags -> Reduction
| RedStrong : list RedFlags -> Reduction.

Notation RedNF := (RedStrong [RedBeta;RedDelta;RedZeta;RedIota]).
Notation RedHNF := (RedWhd [RedBeta;RedDelta;RedZeta;RedIota]).

Inductive Unification : Type :=
| UniCoq : Unification
| UniMatch : Unification
| UniMatchNoRed : Unification
| UniEvarconv : Unification.

Inductive Hyp : Type :=
| ahyp : forall {A}, A -> option A -> Hyp.

Inductive Hyps : Type :=
| hlocal : Hyps
| hminus : Hyps -> Hyps -> Hyps
| hhyps : list Hyp -> Hyps.

Record Case :=
    mkCase {
        case_ind : Type;
        case_val : case_ind;
        case_type : Type;
        case_return : dyn;
        case_branches : list dyn
        }.

(* Reduction primitive *)
Definition reduce (r : Reduction) {A} (x : A) := x.

(** Pattern matching without pain *)
Inductive pattern (M : Type->Prop) A (B : A -> Type) (t : A) : Prop :=
| pbase : forall (x:A), (t = x -> M (B x)) -> Unification -> pattern M A B t
| ptele : forall {C}, (forall (x : C), pattern M A B t) -> pattern M A B t.

(** goal type *)
Inductive goal :=
| TheGoal : forall {A}, A -> goal
| AHyp : forall {A}, option A -> (A -> goal) -> goal.

(** THE definition of MetaCoq *)
Inductive MetaCoq : Type -> Prop :=
| tret : forall {A}, A -> MetaCoq A
| bind : forall {A B}, MetaCoq A -> (A -> MetaCoq B) -> MetaCoq B
| ttry : forall {A}, MetaCoq A -> (Exception -> MetaCoq A) -> MetaCoq A
| raise : forall {A}, Exception -> MetaCoq A
| tfix1' : forall {A B} (S : Type -> Prop),
  (forall a, S a -> MetaCoq a) ->
  ((forall x : A, S (B x)) -> (forall x : A, S (B x))) ->
  forall x : A, MetaCoq (B x)
| tfix2' : forall {A1 A2 B} (S : Type -> Prop),
  (forall a, S a -> MetaCoq a) ->
  ((forall (x1 : A1) (x2 : A2 x1), S (B x1 x2)) ->
    (forall (x1 : A1) (x2 : A2 x1), S (B x1 x2))) ->
  forall (x1 : A1) (x2 : A2 x1), MetaCoq (B x1 x2)
| tfix3' : forall {A1 A2 A3 B} (S : Type -> Prop),
  (forall a, S a -> MetaCoq a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), S (B x1 x2 x3)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), S (B x1 x2 x3))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), MetaCoq (B x1 x2 x3)
| tfix4' : forall {A1 A2 A3 A4 B} (S : Type -> Prop),
  (forall a, S a -> MetaCoq a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), S (B x1 x2 x3 x4)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), S (B x1 x2 x3 x4))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), MetaCoq (B x1 x2 x3 x4)
| tfix5' : forall {A1 A2 A3 A4 A5 B} (S : Type -> Prop),
  (forall a, S a -> MetaCoq a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), S (B x1 x2 x3 x4 x5)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), S (B x1 x2 x3 x4 x5))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), MetaCoq (B x1 x2 x3 x4 x5)

| is_var : forall {A}, A -> MetaCoq bool
(* if the 4th argument is Some t, it adds x:=t to the local context *)
| tnu : forall {A B}, string -> option A -> (A -> MetaCoq B) -> MetaCoq B
| abs : forall {A P} (x : A), P x -> MetaCoq (forall x, P x)
| abs_let : forall {A P} (x: A) (t: A), P x -> MetaCoq (let x := t in P x)
| abs_prod : forall {A P} (x : A), P x -> MetaCoq Type
(** [abs_fix f t n] creates a fixpoint with variable [f] as name,
    with body t,
    and reducing the n-th product of [f]. This means that [f]'s type
    is expected to be of the form [forall x1, ..., xn, T] *)
| abs_fix : forall {A}, A -> A -> N -> MetaCoq A

(* [get_binder_name t] returns the name of variable [x] if:
   - [t = x],
   - [t = forall x, P x],
   - [t = fun x=>b],
   - [t = let x := d in b].
*)
| get_binder_name : forall {A}, A -> MetaCoq string
| remove : forall {A B}, A -> MetaCoq B -> MetaCoq B

| evar : forall A, MetaCoq A
| Cevar : forall A, list Hyp -> MetaCoq A
| is_evar : forall {A}, A -> MetaCoq bool

| hash : forall {A}, A -> N -> MetaCoq N
| solve_typeclasses : MetaCoq unit

| print : string -> MetaCoq unit
| pretty_print : forall {A}, A -> MetaCoq string

| hypotheses : MetaCoq (list Hyp)

| destcase : forall {A} (a : A), MetaCoq (Case)
| constrs : forall {A : Type} (a : A), MetaCoq (list dyn)
| makecase : forall (C : Case), MetaCoq dyn

(** [munify x y r] uses reduction strategy [r] to equate [x] and [y].
    It uses convertibility of universes. *)
| munify {A} (x y : A) : Unification -> MetaCoq (option (x = y))

| call_ltac : forall {A : Type}, string -> list dyn -> MetaCoq (A * list goal)
| list_ltac : MetaCoq unit

| match_and_run : forall {A B t}, pattern MetaCoq A B t -> MetaCoq (option (B t))

(** [munify_cumul x y r] uses reduction strategy [r] to equate [x] and [y].
    Note that they might have different types.
    It uses cumulativity of universes, e.g., it succeeds if [x] is [Prop] and [y] is [Type]. *)
| munify_cumul {A B} (x: A) (y: B) : Unification -> MetaCoq bool
.

Arguments MetaCoq (_%type).

Definition failwith {A} s : MetaCoq A := raise (Failure s).

Definition tfix1 {A} B := @tfix1' A B MetaCoq (fun _ x => x).
Definition tfix2 {A1 A2} B := @tfix2' A1 A2 B MetaCoq (fun _ x => x).
Definition tfix3 {A1 A2 A3} B := @tfix3' A1 A2 A3 B MetaCoq (fun _ x => x).
Definition tfix4 {A1 A2 A3 A4} B := @tfix4' A1 A2 A3 A4 B MetaCoq (fun _ x => x).
Definition tfix5 {A1 A2 A3 A4 A5} B := @tfix5' A1 A2 A3 A4 A5 B MetaCoq (fun _ x => x).

(** Defines [eval f] to execute after elaboration the Mtactic [f].
    It allows e.g. [rewrite (eval f)]. *)
Class runner A  (f : MetaCoq A) := { eval : A }.
Arguments runner {A} _.
Arguments Build_runner {A} _ _.
Arguments eval {A} _ {_}.

Hint Extern 20 (runner ?f) =>
  (exact (Build_runner f ltac:(mrun f)))  : typeclass_instances.



Definition print_term {A} (x: A) : MetaCoq unit :=
  bind (pretty_print x) (fun s=> print s).

End MetaCoq.

Export MetaCoq.


Module MetaCoqNotations.

Bind Scope MetaCoq_scope with MetaCoq.
Delimit Scope MetaCoq_scope with MC.
Open Scope MetaCoq_scope.

Notation "'M'" := MetaCoq : type_scope.

Notation "'rsimpl'" := (reduce RedSimpl).
Notation "'rhnf'" := (reduce RedHNF).
Notation "'rone_step'" := (reduce RedOneStep).

Notation "'ret'" := (fun a => (@tret _ a) % MC).
Notation "'retS' e" := (let s := rsimpl e in ret s) (at level 20) : MetaCoq_scope.

Notation "r '<-' t1 ';' t2" := (@bind _ _ t1 (fun r=> t2%MC))
  (at level 81, right associativity, format "'[' r  '<-'  '[' t1 ;  ']' ']' '/' t2 ") : MetaCoq_scope.
Notation "t1 ';;' t2" := (@bind _ _ t1 (fun _=>t2%MC))
  (at level 81, right associativity, format "'[' '[' t1 ;;  ']' ']' '/' t2 ") : MetaCoq_scope.
Notation "f @@ x" := (bind f (fun r=>(ret (r x))%MC)) (at level 70) : MetaCoq_scope.
Notation "f >> x" := (bind f (fun r=>(x r) % MC)) (at level 70) : MetaCoq_scope.
Open Scope string.

(* We cannot make this notation recursive, so we loose
   notation in favor of naming. *)
Notation "'nu' x , a" := (
  let f := fun x=>a in
  n <- get_binder_name f;
  tnu n None f) (at level 81, x at next level, right associativity) : MetaCoq_scope.

Notation "'nu' x : A , a" := (
  let f := fun x:A=>a in
  n <- get_binder_name f;
  tnu n None f) (at level 81, x at next level, right associativity) : MetaCoq_scope.

Notation "'nu' x := t , a" := (
  let f := fun x=>a in
  n <- get_binder_name f;
  tnu n (Some t) f) (at level 81, x at next level, right associativity) : MetaCoq_scope.

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


Definition NoPatternMatches : Exception. exact exception. Qed.
Definition Anomaly : Exception. exact exception. Qed.
Definition Continue : Exception. exact exception. Qed.

Notation pattern := (pattern MetaCoq).

Fixpoint tmatch {A P} t (ps : list (pattern A P t)) : M (P t) :=
  match ps with
  | [] => raise NoPatternMatches
  | (p :: ps') =>
    v <- match_and_run p;
    match v with
    | None => tmatch t ps'
    | Some v => ret v
    end
  end.

Arguments ptele {_ A B t C} _.
Arguments pbase {_ A B t} _ _ _.


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

Delimit Scope metaCoq_pattern_scope with metaCoq_pattern.

Notation "'with' | p1 | .. | pn 'end'" :=
  ((@cons (pattern _ _ _) p1%metaCoq_pattern (.. (@cons (pattern _ _ _) pn%metaCoq_pattern nil) ..)))
    (at level 91, p1 at level 210, pn at level 210).
Notation "'with' p1 | .. | pn 'end'" :=
  ((@cons (pattern _ _ _) p1%metaCoq_pattern (.. (@cons (pattern _ _ _) pn%metaCoq_pattern nil) ..)))
    (at level 91, p1 at level 210, pn at level 210).

Notation "'mmatch' x ls" := (@tmatch _ (fun _=>_) x ls)
  (at level 90, ls at level 91) : MetaCoq_scope.
Notation "'mmatch' x 'return' 'M' p ls" := (@tmatch _ (fun x=>p) x ls)
  (at level 90, ls at level 91) : MetaCoq_scope.
Notation "'mmatch' x 'as' y 'return' 'M' p ls" := (@tmatch _ (fun y=>p) x ls)
  (at level 90, ls at level 91) : MetaCoq_scope.


Notation "'mtry' a ls" :=
  (ttry a (fun e=>
    (@tmatch _ (fun _=>_) e (app ls (cons ([? x] x=>raise x)%metaCoq_pattern nil)))))
    (at level 82, a at level 100, ls at level 91, only parsing).

End MetaCoqNotations.

Section GeneralUtilities.
Import MetaCoqNotations.

Definition fresh_binder_name {A} (t: A) : M string :=
  env <- hypotheses;
  let namef := reduce RedNF (
    fold_left (fun (ns:M (list string)) (h:Hyp)=>
      let (_, var, _) := h in
      n <- get_binder_name var;
      r <- ns; ret (n::r)) env (ret [])
    ) in
  names <- namef;
  name <- mtry get_binder_name t with WrongTerm=> ret "x" end;
  let find name : M bool :=
    let f := reduce RedNF (
      fold_left (fun (found: M bool) (n: string)=>
        b <- found;
        if b then
          ret true
        else
         munify_cumul name n UniMatchNoRed
        ) names (ret false))
    in
    f
  in
  b <- find name;
  if b then
    (mfix2 f (name: string) (i: string) : M string :=
      let name := reduce RedNF (name ++ i) in
      b <- find name;
      if b then f name i
      else ret name) name "_"
  else
    ret name.

End GeneralUtilities.
