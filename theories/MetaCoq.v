(* Need to load Unicoq to get the module dependency right *)
Declare ML Module "unicoq".
(** Load library "MetaCoqPlugin.cma". *)
Declare ML Module "MetaCoqPlugin".

Require Import Strings.String.
Require Import Lists.List.
Require Import NArith.BinNat.
Require Import NArith.BinNatDef.

Module MetaCoq.

Inductive Exception : Type := exception : Exception.

Definition NullPointer : Exception. exact exception. Qed.

Definition TermNotGround : Exception. exact exception. Qed.

Definition ArrayOutOfBounds : Exception. exact exception. Qed.

Definition NoPatternMatches : Exception. exact exception. Qed.

Definition WrongTerm : Exception. exact exception. Qed.

Definition MissingDependency : Exception. exact exception. Qed.

Definition LtacError (s:string) : Exception. exact exception. Qed.

Definition NotUnifiable {A} (x y : A) : Exception. exact exception. Qed.

Definition Failure (s : string) : Exception. exact exception. Qed.

Record dyn := Dyn { type : Type; elem :> type }.
Arguments Dyn {_} _.

Definition index := N.
Definition length := N.

Inductive array (A:Type) : Type :=
| carray : index -> length -> array A.

Inductive Reduction : Type :=
| RedNone : Reduction
| RedSimpl : Reduction
| RedWhd : Reduction
| RedOneStep : Reduction.

Inductive Unification : Type :=
| UniNormal : Unification
| UniMatch : Unification
| UniCoq : Unification.

Inductive Hyp : Type :=
| ahyp : forall {A}, A -> option A -> Hyp.

Inductive Hyps : Type :=
| hlocal : Hyps
| hminus : Hyps -> Hyps -> Hyps
| hhyps : list Hyp -> Hyps.


Polymorphic Inductive ITele : Type :=
| iBase : forall {T}, T -> ITele
| iTele : forall {T}, (T -> ITele) -> ITele.

Section ExampleRemove.
Inductive reflect (P :Prop) : bool -> Type :=
| RTrue : P -> reflect P true
| RFalse : ~P -> reflect P false.

Example reflect_reflect P := iTele (fun b=>iBase (reflect P b)).
End ExampleRemove.

Polymorphic Inductive CTele : ITele -> Type :=
| cBase : forall {T:Type}, T -> CTele (iBase T)
| cInst : forall {T f} (t:T), CTele (f t) -> CTele (iTele f)
| cProd : forall {T it}, (T -> CTele it) -> CTele it.


Polymorphic Inductive ATele : ITele -> Type :=
| aBase : forall {T:Type}, ATele (iBase T)
| aTele : forall {T f} (a:T), ATele (f a) -> ATele (iTele f).

Polymorphic Inductive RTele : ITele -> Type :=
| rBase : forall {T U} {t:T}, U -> RTele (iBase t)
| rTele : forall {T f}, (forall (t : T), RTele (f t)) -> RTele (iTele f).

Section ExampleRemove2.

Example reflect_RTrue P : CTele (reflect_reflect P) :=
  cInst true (cProd (fun p=>@cBase (reflect P true) (RTrue P p))).

Example reflect_args P b : ATele (reflect_reflect P) :=
  aTele b aBase.

End ExampleRemove2.

Record IndType := mkIndType {
  ind_type : ITele;
  ind_constructors : list (CTele ind_type);
  ind_num_params : nat
}.

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
| pbase : forall (x:A), (t = x -> M (B x)) -> pattern M A B t
| ptele : forall {C}, (forall (x : C), pattern M A B t) -> pattern M A B t.

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
| abs_let : forall {A B}, A -> B -> MetaCoq B
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

| array_make : forall {A}, N -> A -> MetaCoq (array A)
| array_get : forall {A}, array A -> N -> MetaCoq A
| array_set : forall {A}, array A -> N -> A -> MetaCoq unit

| print : string -> MetaCoq unit
| pretty_print : forall {A}, A -> MetaCoq string

| hypotheses : MetaCoq (list Hyp)

| destcase : forall {A} (a : A), MetaCoq (Case)
| constrs : forall {A : Type} (a : A), MetaCoq (list dyn)
| makecase : forall (C : Case), MetaCoq dyn

| munify {A} (x y : A) : Unification -> MetaCoq (option (x = y))

| call_ltac : forall {A : Type}, string -> list dyn -> MetaCoq (A * list dyn)
| list_ltac : forall {A : Type} {_ : A}, MetaCoq A

| match_and_run : forall {A B t}, pattern MetaCoq A B t -> MetaCoq (option (B t))

| get_inductive : Type -> MetaCoq IndType
.

Definition failwith {A} s : MetaCoq A := raise (Failure s).

Definition array_length : forall {A}, array A -> length :=
  fun A m => match m with carray _ _ l => l end.


Definition tfix1 {A} B := @tfix1' A B MetaCoq (fun _ x => x).
Definition tfix2 {A1 A2} B := @tfix2' A1 A2 B MetaCoq (fun _ x => x).
Definition tfix3 {A1 A2 A3} B := @tfix3' A1 A2 A3 B MetaCoq (fun _ x => x).
Definition tfix4 {A1 A2 A3 A4} B := @tfix4' A1 A2 A3 A4 B MetaCoq (fun _ x => x).
Definition tfix5 {A1 A2 A3 A4 A5} B := @tfix5' A1 A2 A3 A4 A5 B MetaCoq (fun _ x => x).

Definition Ref := array.

Definition ref : forall {A}, A -> MetaCoq (Ref A) :=
  fun A x=> array_make 1%N x.

Definition read : forall {A}, Ref A -> MetaCoq A :=
  fun A r=> array_get r 0%N.

Definition write : forall {A}, Ref A -> A -> MetaCoq unit :=
  fun A r c=> array_set r 0%N c.

(** Defines [eval f] to execute after elaboration the Mtactic [f].
    It allows e.g. [rewrite (eval f)]. *)
Class runner A  (f : MetaCoq A) := { eval : A }.
Arguments runner {A} _.
Arguments Build_runner {A} _ _.
Arguments eval {A} _ {_}.

Hint Extern 20 (runner ?f) =>
  (exact (Build_runner f ltac:(mrun f)))  : typeclass_instances.



Definition print_term {A} (x : A) : MetaCoq unit :=
  bind (pretty_print x) (fun s=> print s).

End MetaCoq.

Export MetaCoq.


Module MetaCoqNotations.

Notation "'M'" := MetaCoq.

Notation "'simpl'" := (reduce RedSimpl).
Notation "'hnf'" := (reduce RedWhd).
Notation "'one_step'" := (reduce RedOneStep).

Notation "'ret'" := (tret).
Notation "'retS' e" := (let s := simpl e in ret s) (at level 20).

Notation "r '<-' t1 ';' t2" := (@bind _ _ t1 (fun r=> t2))
  (at level 81, right associativity).
Notation "t1 ';;' t2" := (@bind _ _ t1 (fun _=>t2))
  (at level 81, right associativity).
Notation "f @@ x" := (bind f (fun r=>ret (r x))) (at level 70).
Notation "f >> x" := (bind f (fun r=>x r)) (at level 70).
Open Scope string.

(* We cannot make this notation recursive, so we loose
   notation in favor of naming. *)
Notation "'nu' x , a" := (
  let f := fun x=>a in
  n <- get_binder_name f;
  tnu n None f) (at level 81, x at next level, right associativity).

Notation "'nu' x : A , a" := (
  let f := fun x:A=>a in
  n <- get_binder_name f;
  tnu n None f) (at level 81, x at next level, right associativity).

Notation "'nu' x := t , a" := (
  let f := fun x=>a in
  n <- get_binder_name f;
  tnu n (Some t) f) (at level 81, x at next level, right associativity).

Notation "'mfix1' f ( x : A ) : 'M' T := b" := (tfix1 (fun x=>T) (fun f (x : A)=>b))
  (at level 85, f at level 0, x at next level, format
  "'[v  ' 'mfix1'  f  '(' x  ':'  A ')'  ':'  'M'  T  ':=' '/  ' b ']'").

Notation "'mfix2' f ( x : A ) ( y : B ) : 'M' T := b" :=
  (tfix2 (fun (x : A) (y : B)=>T) (fun f (x : A) (y : B)=>b))
  (at level 85, f at level 0, x at next level, y at next level, format
  "'[v  ' 'mfix2'  f  '(' x  ':'  A ')'  '(' y  ':'  B ')'  ':'  'M'   T  ':=' '/  ' b ']'").

Notation "'mfix3' f ( x : A ) ( y : B ) ( z : C ) : 'M' T := b" :=
  (tfix3 (fun (x : A) (y : B) (z : C)=>T) (fun f (x : A) (y : B) (z : C)=>b))
  (at level 85, f at level 0, x at next level, y at next level, z at next level, format
  "'[v  ' 'mfix3'  f  '(' x  ':'  A ')'  '(' y  ':'  B ')'  '(' z  ':'  C ')'  ':'  'M'  T  ':=' '/  ' b ']'").

Notation "'mfix4' f ( x1 : A1 ) ( x2 : A2 ) ( x3 : A3 ) ( x4 : A4 ) : 'M' T := b" :=
  (tfix4 (fun (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4)=>T) (fun f (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4) =>b))
  (at level 85, f at level 0, x1 at next level, x2 at next level, x3 at next level, x4 at next level, format
  "'[v  ' 'mfix4'  f  '(' x1  ':'  A1 ')'  '(' x2  ':'  A2 ')'  '(' x3  ':'  A3 ')'  '(' x4  ':'  A4 ')'  ':'  'M'  T  ':=' '/  ' b ']'").

Notation "'mfix5' f ( x1 : A1 ) ( x2 : A2 ) ( x3 : A3 ) ( x4 : A4 ) ( x5 : A5 ) : 'M' T := b" :=
  (tfix5 (fun (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4) (x5 : A5)=>T) (fun f (x1 : A1) (x2 : A2) (x3 : A3) (x4 : A4) (x5 : A5) =>b))
  (at level 85, f at level 0, x1 at next level, x2 at next level, x3 at next level, x4 at next level, x5 at next level, format
  "'[v  ' 'mfix5'  f  '(' x1  ':'  A1 ')'  '(' x2  ':'  A2 ')'  '(' x3  ':'  A3 ')'  '(' x4  ':'  A4 ')'  '(' x5  ':'  A5 ')'  ':'  'M'  T  ':=' '/  ' b ']'").


Definition type_inside {A} (x : M A) := A.


Definition NoPatternMatches : Exception. exact exception. Qed.
Definition Anomaly : Exception. exact exception. Qed.
Definition Continue : Exception. exact exception. Qed.
Import ListNotations.

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

Arguments ptele {_ A B t C} f.
Arguments pbase {_ A B t} x b.


Notation "[? x .. y ] ps" := (ptele (fun x=> .. (ptele (fun y=>ps)).. ))
  (at level 202, x binder, y binder, ps at next level) : metaCoq_pattern_scope.
Notation "p => b" := (pbase p%core (fun _=>b%core))
  (no associativity, at level 201) : metaCoq_pattern_scope.
Notation "p => [ H ] b" := (pbase p%core (fun H=>b%core))
  (no associativity, at level 201, H at next level) : metaCoq_pattern_scope.
Notation "'_' => b " := (ptele (fun x=> pbase x (fun _=>b%core)))
  (at level 201, b at next level) : metaCoq_pattern_scope.

Delimit Scope metaCoq_pattern_scope with metaCoq_pattern.

Notation "'with' | p1 | .. | pn 'end'" :=
  ((cons p1%metaCoq_pattern (.. (cons pn%metaCoq_pattern nil) ..)))
    (at level 91, p1 at level 210, pn at level 210).
Notation "'with' p1 | .. | pn 'end'" :=
  ((cons p1%metaCoq_pattern (.. (cons pn%metaCoq_pattern nil) ..)))
    (at level 91, p1 at level 210, pn at level 210).

Notation "'mmatch' x ls" := (@tmatch _ (fun _=>_) x ls)
  (at level 90, ls at level 91).
Notation "'mmatch' x 'return' 'M' p ls" := (@tmatch _ (fun x=>p) x ls)
  (at level 90, ls at level 91).
Notation "'mmatch' x 'as' y 'return' 'M' p ls" := (@tmatch _ (fun y=>p) x ls)
  (at level 90, ls at level 91).


Notation "'mtry' a ls" :=
  (ttry a (fun e=>
    (@tmatch _ (fun _=>_) e (app ls (cons ([? x] x=>raise x)%metaCoq_pattern nil)))))
    (at level 82, a at level 100, ls at level 91, only parsing).

Notation "! a" := (read a) (at level 80).
Notation "a ::= b" := (write a b) (at level 80).

End MetaCoqNotations.


Module Array.
  Require Import Arith_base.

  Import MetaCoqNotations.

  Definition t A := array A.

  Definition make {A} n (c : A)  :=
    MetaCoq.array_make n c.

  Definition length {A} (a : t A) :=
    MetaCoq.array_length a.

  Definition get {A} (a : t A) i :=
    MetaCoq.array_get a i.

  Definition set {A} (a : t A) i (c : A) :=
    MetaCoq.array_set a i c.

  Definition iter {A} (a : t A) (f : N -> A -> M unit) : M unit :=
    let n := length a in
    N.iter n (fun i : M N =>
      i' <- i;
      e <- get a i';
      f i' e;;
      retS (N.succ i'))
      (ret 0%N);;
    ret tt.

  Definition No0LengthArray : Exception. exact exception. Qed.

  Definition init {A:Type} n (f : N -> M A) : M (t A) :=
    match n with
    | N0 => raise No0LengthArray
    | _ =>
      c <- f 0%N;
        a <- make n c;
        N.iter (N.pred n) (fun i : M N =>
            i' <- i;
            e <- f i';
            set a i' e;;
            retS (N.succ i'))
          (ret 1%N);;
        ret a
    end.

  Definition to_list {A} (a : t A) :=
    let n := length a in
    r <- N.iter n (fun l : M (N * list A)%type =>
      l' <- l;
      let (i, s) := l' in
      e <- get a i;
      retS (N.succ i, e :: s))
    (ret (0%N, nil));
    retS (snd r).

  Definition copy {A} (a b : t A) :=
    let n := length a in
    N.iter n (fun i : M N =>
      i' <- i;
      e <- get a i';
      set b i' e;;
      retS (N.succ i'))
      (ret 0%N).

End Array.
