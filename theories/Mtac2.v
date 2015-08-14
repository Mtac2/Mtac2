(** Load library "mtac2Plugin.cma". *)
Declare ML Module "mtac2Plugin".

Require Import Strings.String.
Require Import Lists.List.
Require Import NArith.BinNat.
Require Import NArith.BinNatDef.


Module Mtac.

Inductive Exception : Type := exception : Exception.

Definition NullPointer : Exception. exact exception. Qed.

Definition TermNotGround : Exception. exact exception. Qed.

Definition ArrayOutOfBounds : Exception. exact exception. Qed.

Definition NoPatternMatches : Exception. exact exception. Qed.

Polymorphic Record dyn := Dyn { type : Type; elem : type }.

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
| UniRed : Unification
| UniSimpl : Unification
| UniMuni : Unification.

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

Inductive Mtac : Type -> Prop :=
| tret : forall {A}, Reduction -> A -> Mtac A
| bind : forall {A B}, Mtac A -> (A -> Mtac B) -> Mtac B
| ttry : forall {A}, Mtac A -> (Exception -> Mtac A) -> Mtac A
| raise : forall {A}, Exception -> Mtac A
| tfix1' : forall {A B} (S : Type -> Prop),
  (forall a, S a -> Mtac a) ->
  ((forall x : A, S (B x)) -> (forall x : A, S (B x))) ->
  forall x : A, Mtac (B x)
| tfix2' : forall {A1 A2 B} (S : Type -> Prop),
  (forall a, S a -> Mtac a) ->
  ((forall (x1 : A1) (x2 : A2 x1), S (B x1 x2)) ->
    (forall (x1 : A1) (x2 : A2 x1), S (B x1 x2))) ->
  forall (x1 : A1) (x2 : A2 x1), Mtac (B x1 x2)
| tfix3' : forall {A1 A2 A3 B} (S : Type -> Prop),
  (forall a, S a -> Mtac a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), S (B x1 x2 x3)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), S (B x1 x2 x3))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), Mtac (B x1 x2 x3)
| tfix4' : forall {A1 A2 A3 A4 B} (S : Type -> Prop),
  (forall a, S a -> Mtac a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), S (B x1 x2 x3 x4)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), S (B x1 x2 x3 x4))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3), Mtac (B x1 x2 x3 x4)
| tfix5' : forall {A1 A2 A3 A4 A5 B} (S : Type -> Prop),
  (forall a, S a -> Mtac a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), S (B x1 x2 x3 x4 x5)) ->
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), S (B x1 x2 x3 x4 x5))) ->
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) (x5 : A5 x1 x2 x3 x4), Mtac (B x1 x2 x3 x4 x5)
| tmatch : forall {A} B (t : A), list (tpatt A B t) -> Mtac (B t)
| print : string -> Mtac unit
| tnu : forall {A B}, (A -> Mtac B) -> Mtac B
| is_var : forall {A}, A -> Mtac bool
| abs : forall {A P} (x : A), P x -> Mtac (forall x, P x)
| abs_eq : forall {A} {P} (x : A) (y : P x),
  Mtac (sigT (fun f : (forall x':A, P x')=> f x = y))
| evar : forall A, Mtac A
| is_evar : forall {A}, A -> Mtac bool

| hash : forall {A}, A -> N -> Mtac N

| tnu_let : forall {A B}, forall t : A, (forall y : A, y = t -> Mtac B) -> Mtac B

| solve_typeclasses : Mtac unit

| array_make : forall {A}, N -> A -> Mtac (array A)
| array_get : forall {A}, array A -> N -> Mtac A
| array_set : forall {A}, array A -> N -> A -> Mtac unit
| print_term : forall {A}, A -> Mtac unit
| hypotheses : Mtac (list Hyp)

| destcase : forall {A} (a : A), Mtac (Case)
| constrs : forall {A : Type} (a : A), Mtac (list dyn)
| makecase : forall (C : Case), Mtac dyn

| Cevar : forall A, list Hyp -> Mtac A

| pabs : forall {A P} (x : A), P x -> Mtac Type

with tpatt : forall A (B : A -> Type) (t : A), Prop :=
| base : forall {A B t} (x:A) (b : t = x -> Mtac (B x)), Unification -> tpatt A B t
| tele : forall {A B C t}, (forall (x : C), tpatt A B t) -> tpatt A B t.

Definition array_length : forall {A}, array A -> length :=
  fun A m => match m with carray _ _ l => l end.


Definition tfix1 {A} B := @tfix1' A B Mtac (fun _ x => x).
Definition tfix2 {A1 A2} B := @tfix2' A1 A2 B Mtac (fun _ x => x).
Definition tfix3 {A1 A2 A3} B := @tfix3' A1 A2 A3 B Mtac (fun _ x => x).
Definition tfix4 {A1 A2 A3 A4} B := @tfix4' A1 A2 A3 A4 B Mtac (fun _ x => x).
Definition tfix5 {A1 A2 A3 A4 A5} B := @tfix5' A1 A2 A3 A4 A5 B Mtac (fun _ x => x).

Definition Ref := array.

Definition ref : forall {A}, A -> Mtac (Ref A) :=
  fun A x=> array_make 1%N x.

Definition read : forall {A}, Ref A -> Mtac A :=
  fun A r=> array_get r 0%N.

Definition write : forall {A}, Ref A -> A -> Mtac unit :=
  fun A r c=> array_set r 0%N c.

(** Defines [eval f] to execute after elaboration the Mtactic [f].
    It allows e.g. [rewrite (eval f)]. *)
Class runner A  (f : Mtac A) := { eval : A }.
Arguments runner {A} _.
Arguments Build_runner {A} _ _.
Arguments eval {A} _ {_}.

End Mtac.

Export Mtac.


Module Mtac2Notations.

Notation "'M'" := Mtac.

Notation "'ret'" := (tret RedNone).
Notation "'retS'" := (tret RedSimpl).
Notation "'retW'" := (tret RedWhd).
Notation "'retO'" := (tret RedOneStep).

Notation "r '<-' t1 ';' t2" := (@bind _ _ t1 (fun r=> t2))
  (at level 81, right associativity).
Notation "t1 ';;' t2" := (@bind _ _ t1 (fun _=>t2))
  (at level 81, right associativity).
Notation "f @@ x" := (bind f (fun r=>ret (r x))) (at level 70).
Notation "f >> x" := (bind f (fun r=>x r)) (at level 70).

Notation "[? x .. y ] ps" := (tele (fun x=> .. (tele (fun y=>ps)).. ))
  (at level 202, x binder, y binder, ps at next level) : mtac_patt_scope.
Notation "p => b" := (base p%core (fun _=>b%core) UniRed)
  (no associativity, at level 201) : mtac_patt_scope.
Notation "p => b 'return' T" := (@base _ T _ p%core (fun _=>b%core) UniRed)
  (no associativity, at level 201) : mtac_patt_scope.
Notation "p => [ H ] b" := (base p%core (fun H=>b%core) UniRed)
  (no associativity, at level 201, H at next level) : mtac_patt_scope.
Notation "p '=s>' b" := (base p%core (fun _=>b%core) UniSimpl)
  (no associativity, at level 201) : mtac_patt_scope.
Notation "p =m> b" := (base p%core (fun _=>b%core) UniMuni)
  (no associativity, at level 201) : mtac_patt_scope.
Notation "p =m> [ H ] b" := (base p%core (fun H=>b%core) UniMuni)
  (no associativity, at level 201, H at next level) : mtac_patt_scope.
Notation "p =c> b" := (base p%core (fun _=>b%core) UniRed)
  (no associativity, at level 201) : mtac_patt_scope.
Notation "p =c> [ H ] b" := (base p%core (fun H=>b%core) UniRed)
  (no associativity, at level 201, H at next level) : mtac_patt_scope.
Notation "'_' => b " := (tele (fun x=> base x (fun _=>b%core) UniRed))
  (at level 201, b at next level) : mtac_patt_scope.
Notation "'_' =m> b " := (tele (fun x=> base x (fun _=>b%core) UniMuni))
  (at level 201, b at next level) : mtac_patt_scope.
Notation "'_' =c> b " := (tele (fun x=> base x (fun _=>b%core) UniRed))
  (at level 201, b at next level) : mtac_patt_scope.

Delimit Scope mtac_patt_scope with mtac_patt.

Notation "'with' | p1 | .. | pn 'end'" :=
  ((cons p1%mtac_patt (.. (cons pn%mtac_patt nil) ..)))
    (at level 91, p1 at level 210, pn at level 210).
Notation "'with' p1 | .. | pn 'end'" :=
  ((cons p1%mtac_patt (.. (cons pn%mtac_patt nil) ..)))
    (at level 91, p1 at level 210, pn at level 210).

Notation "'mmatch' t ls" :=
  (tmatch (fun _=>_) t ((fun l : list (tpatt _ (fun _=>_) _)=>l) ls))
    (at level 90, ls at level 91, only parsing).
Notation "'mmatch' t 'return' 'M' p ls" :=
  (tmatch (fun _=>p) t ((fun l : list (tpatt _ (fun _=>p) _)=>l) ls))
    (at level 90, p at level 0, ls at level 91, only parsing).
Notation "'mmatch' t 'as' x 'return' 'M' p ls" :=
  (tmatch (fun x=>p) t ((fun l : list (tpatt _ (fun x=>p) _)=>l) ls))
    (at level 90, p at level 0, ls at level 91, format
  "'[v' 'mmatch'  t  'as'  x  'return'  'M'  p  '/'  ls ']'").

Notation "'nu' x .. y , a" := (tnu (fun x=>.. (tnu (fun y=> a))..))
(at level 81, x binder, y binder, right associativity).


Definition MFixException (s : string) : Exception.
  exact exception.
Qed.

Program
Definition mk_rec (Ty : Prop) (b : Ty) : M dyn :=
  mmatch Ty as Ty' return M _ with
  | [? A B] (forall x:A, M (B x)) -> forall x:A, M (B x) =c> [H]
    retS (Dyn _ (tfix1 B (eq_ind _ id b _ H)))
  | [? A B C] (forall (x:A) (y : B x), M (C x y)) -> forall (x:A) (y : B x), M (C x y) =c>[H]
    retS (Dyn _ (tfix2 C (eq_ind _ id b _ H)))
  | [? A1 A2 A3 B] (forall (x1:A1) (x2:A2 x1) (x3:A3 x1 x2), M (B x1 x2 x3))
    -> forall (x1:A1) (x2:A2 x1) (x3:A3 x1 x2), M (B x1 x2 x3) =c> [H]
    retS (Dyn _ (tfix3 B (eq_ind _ id b _ H)))
  | [? A1 A2 A3 A4 B] (forall (x1:A1) (x2:A2 x1) (x3:A3 x1 x2) (x4:A4 x1 x2 x3), M (B x1 x2 x3 x4))
    -> forall (x1:A1) (x2:A2 x1) (x3:A3 x1 x2) (x4:A4 x1 x2 x3), M (B x1 x2 x3 x4) =c> [H]
    retS (Dyn _ (tfix4 B (eq_ind _ id b _ H)))
  | [? A1 A2 A3 A4 A5 B] (forall (x1:A1) (x2:A2 x1) (x3:A3 x1 x2) (x4:A4 x1 x2 x3) (x5:A5 x1 x2 x3 x4), M (B x1 x2 x3 x4 x5))
    -> forall (x1:A1) (x2:A2 x1) (x3:A3 x1 x2) (x4:A4 x1 x2 x3) (x5:A5 x1 x2 x3 x4), M (B x1 x2 x3 x4 x5) =c> [H]
    retS (Dyn _ (tfix5 B (eq_ind _ id b _ H)))
  | _ => raise (MFixException "Cannot typecheck the fixpoint. Perhaps you provided more than 5 arguments? If not, you can try providing the type to the fixpoint.")
  end.

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

(* Not working. Must do in Ocaml. *)
Notation "'mfix' f x .. y := b" := (
  let T := (forall x, .. (forall y, M _) ..) in
  let func := mk_rec (forall f : T, _ : Prop) (fun f =>(fun x => .. (fun y => b) ..)) in
  eval (r <- func; retW (elem r))
  )
  (at level 85, f at level 0, x binder, y binder, only parsing).

Notation "'mfix' f x .. y : 'M' A := b" := (
  let T := (forall x, .. (forall y, M A) ..) in
  let func := mk_rec (forall f : T, _ : Prop) (fun f =>(fun x => .. (fun y => b) ..)) in
  eval (r <- func; retW (elem r))
  )
  (at level 85, f at level 0, x binder, y binder, only parsing).


Definition type_inside {A} (x : M A) := A.

Notation "'mtry' a ls" :=
  (ttry a (fun e=>
    (tmatch _ e (app ls (cons ([? x] x=>raise x)%mtac_patt nil)))))
    (at level 82, a at level 100, ls at level 91, only parsing).

Notation "! a" := (read a) (at level 80).
Notation "a ::= b" := (write a b) (at level 80).

End Mtac2Notations.


Module Array.
  Require Import Arith_base.

  Import Mtac2Notations.

  Definition t A := array A.

  Definition make {A} n (c : A)  :=
    Mtac.array_make n c.

  Definition length {A} (a : t A) :=
    Mtac.array_length a.

  Definition get {A} (a : t A) i :=
    Mtac.array_get a i.

  Definition set {A} (a : t A) i (c : A) :=
    Mtac.array_set a i c.

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