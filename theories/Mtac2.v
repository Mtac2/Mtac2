Declare ML Module "mtac2_plugin".


Inductive Exception : Type := exception : Exception.

Parameter LazyList : Type -> Type.

Inductive dyn := Dyn { dynt : Type; elem : dynt }.

Record Case :=
    mkCase {
        case_ind : Type;
        case_val : case_ind;
        case_type : Type;
        case_return : dyn;
        case_branches : list dyn
        }.

Inductive goal : Type := opaque : forall {A : Type}, goal.

(* Assumption: when one has [Named patt name], [name] comes from a [Mtele] (see
 * under) and its type will be unified with the pattern. *)
Inductive hypothesis := Named : forall A : Type, A -> hypothesis.

Inductive local_telescope (A:Type) (P: A -> Type) : Type :=
  lTele : forall x:A, P x -> local_telescope A P.

(* Assumption: the first parameter of enum will actually be (nested) dependent
 * pairs; e.g. {x : nat & {H : x = 3 & unit}}
 * Of course we will provide a notation for it, so the user doesn't have to
 * write that. *)
Inductive hyp_pattern : Type :=
| Simple : hypothesis -> hyp_pattern
| Enum   : forall A:Type, LazyList A -> hyp_pattern.

Inductive Mtac2 : Type -> Prop :=
| Mret : forall {A}, A -> Mtac2 A
| Mbind : forall {A B}, Mtac2 A -> (A -> Mtac2 B) -> Mtac2 B
| Mtry : forall {A}, Mtac2 A -> (Exception -> Mtac2 A) -> Mtac2 A
| Mraise : forall {A}, Exception -> Mtac2 A
| Mfix1' : forall {A B} (S : Type -> Prop), 
  (forall a, S a -> Mtac2 a) ->
  ((forall x : A, S (B x)) -> (forall x : A, S (B x))) -> 
  forall x : A, Mtac2 (B x)
| Mfix2' : forall {A1 A2 B} (S : Type -> Prop), 
  (forall a, S a -> Mtac2 a) ->
  ((forall (x1 : A1) (x2 : A2 x1), S (B x1 x2)) -> 
    (forall (x1 : A1) (x2 : A2 x1), S (B x1 x2))) -> 
  forall (x1 : A1) (x2 : A2 x1), Mtac2 (B x1 x2)
| Mfix3' : forall {A1 A2 A3 B} (S : Type -> Prop), 
  (forall a, S a -> Mtac2 a) ->
  ((forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), S (B x1 x2 x3)) -> 
    (forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), S (B x1 x2 x3))) -> 
  forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2), Mtac2 (B x1 x2 x3)
| Mmatch : forall {A} B (t : A), list (Mpatt A B t) -> Mtac2 (B t)
| Mprint : forall {A}, A -> Mtac2 unit
| Mnu : forall {A B}, (A -> Mtac2 B) -> Mtac2 B
| Mis_var : forall {A}, A -> Mtac2 bool
| Mabs : forall {A P} (x : A), P x -> Mtac2 (forall x, P x)
| Mevar : forall A, Mtac2 A
| Mis_evar : forall {A}, A -> Mtac2 bool
| Mgoals : Mtac2 (list goal)
| Mrefine : forall {A}, goal -> A -> Mtac2 (list goal)
| Mgmatch : forall {A} (g:goal), list (Mpatt goal (fun g => A) g) -> Mtac2 A
| Mnext : forall {A:Type}, LazyList A -> Mtac2 (option (A * LazyList A))
| Mshow : goal -> Mtac2 unit
| Mdestcase : forall {A} (a : A), Mtac2 (Case)
| Mconstrs : forall {A : Type} (a : A), Mtac2 (list dyn)
| Mmakecase : forall (C : Case), Mtac2 dyn

with Mpatt : forall A (B : A -> Type) (t : A), Type := 
| Mbase : forall {A B t} (x:A) (b : t = x -> Mtac2 (B x)), Mpatt A B t
| Mgoal : forall {A G g}, list hyp_pattern -> G -> Mtac2 A -> Mpatt goal (fun g => A) g
| Mtele : forall {A B C t}, (forall (x : C), Mpatt A B t) -> Mpatt A B t.


Definition Mfix1 {A} B := @Mfix1' A B Mtac2 (fun _ x => x).
Definition Mfix2 {A1 A2} B := @Mfix2' A1 A2 B Mtac2 (fun _ x => x).
Definition Mfix3 {A1 A2 A3} B := @Mfix3' A1 A2 A3 B Mtac2 (fun _ x => x).


(** Defines [eval f] to execute after elaboration the Mtactic [f]. 
    It allows e.g. [rewrite (eval f)]. *)
Class runner A  (f : Mtac2 A) := { eval : A }.
Arguments runner {A} _.
Arguments Build_runner {A} _ _.
Arguments eval {A} _ {_}.

Ltac run_matching f :=
  refine (Build_runner f _);
  let H := fresh "H" in
  f;
  exact H.

Hint Extern 20 (runner ?f) => (run_matching f)  : typeclass_instances.


Module Mtac2Notations.

Notation "'M'" := Mtac2.

Notation "'ret'" := Mret.
Notation "'raise'" := Mraise.

Notation "'print'" := Mprint.

Notation "r '<-' t1 ';' t2" := (@Mbind _ _ t1 (fun r=> t2)) 
  (at level 80, right associativity). 
Notation "t1 ';;' t2" := (@Mbind _ _ t1 (fun _=>t2)) 
  (at level 81, right associativity).
Notation "f @@ x" := (Mbind f (fun r=>ret (r x))) (at level 70).
Notation "f >> x" := (Mbind f (fun r=>x r)) (at level 70).

Notation "[ x .. y ] ps" := (Mtele (fun x=> .. (Mtele (fun y=>ps)).. ))
  (at level 202, x binder, y binder, ps at next level) : mtac_patt_scope.
Notation "p => b" := (Mbase p%core (fun _=>b%core)) 
  (no associativity, at level 201) : mtac_patt_scope. 
Notation "p => b 'return' 'M' a" := (Mbase (B:=a) p%core (fun _=>b%core)) 
  (no associativity, at level 201) : mtac_patt_scope.
Notation "p => [ H ] b" := (Mbase p%core (fun H=>b%core)) 
  (no associativity, at level 201, H at next level) : mtac_patt_scope. 
Notation "'_' => b " := (Mtele (fun x=> Mbase x (fun _=>b%core))) 
  (at level 201, b at next level) : mtac_patt_scope.

Notation "{ } g => b" := (Mgoal nil g%type b%core)
  (no associativity, at level 201, b at next level) : mtac_patt_scope.

(* CARE: the following is a hack, I'm assuming [xi] will actually be of the form
 * [ident : type] so the wildcard in [Named _ xi] will get resolved. *)
Notation "x ::: ty" := (Simple (Named ty x))
  (no associativity, at level 10) : mtac_hyp_scope.
Notation "< ty >* 'as' l" := (Enum ty%type l) (no associativity, at level 10) : mtac_hyp_scope.

Delimit Scope mtac_hyp_scope with mtac_hyp.

Notation "{ x1 , .. , xn } g => b" :=
  (Mgoal (cons x1%mtac_hyp (.. (cons xn%mtac_hyp nil) ..)) g%type b%core)
    (no associativity, at level 201, b at next level) : mtac_patt_scope.

(*
(* CARE: the following is a hack, I'm assuming [xi] will actually be of the form
 * [ident : type] so the wildcard in [Named _ xi] will get resolved. *)
Notation "{ x1 , .. , xn } g => b" :=
  (Mgoal (cons (Simple (Named _ x1)) (.. (cons (Simple (Named _ xn)) nil) ..)) g%type b%core)
    (no associativity, at level 201, b at next level) : mtac_patt_scope.
*)

Delimit Scope mtac_patt_scope with mtac_patt.

Notation "'gmatch' g 'with' | p1 | .. | pn 'end'" := 
  (Mgmatch g (cons p1%mtac_patt (.. (cons pn%mtac_patt nil) ..))) 
    (at level 90, p1 at level 210, pn at level 210, format
  "'[v' 'gmatch'  g  'with' '/' '|'  p1 '/' '|'  .. '/' '|'  pn '/' end ']'").

Notation "'mmatch' t 'with' | p1 | .. | pn 'end'" := 
  (Mmatch (fun _=>_) t (cons p1%mtac_patt (.. (cons pn%mtac_patt nil) ..))) 
    (at level 90, p1 at level 210, pn at level 210, only parsing).
Notation "'mmatch' t 'return' 'M' p 'with' | p1 | .. | pn 'end'" := 
  (Mmatch (fun _=>p) t (cons p1%mtac_patt (.. (cons pn%mtac_patt nil) ..))) 
    (at level 90, p1 at level 210, pn at level 210, only parsing).
Notation "'mmatch' t 'as' x 'return' 'M' p 'with' | p1 | .. | pn 'end'" := 
  (Mmatch (fun x=>p) t (cons p1%mtac_patt (.. (cons pn%mtac_patt nil) ..))) 
    (at level 90, p1 at level 210, pn at level 210, format
  "'[v' 'mmatch'  t  'as'  x  'return'  'M'  p  'with' '/' '|'  p1 '/' '|'  .. '/' '|'  pn '/' 'end' ']'").

Notation "'mmatch' t 'with' p1 | .. | pn 'end'" := 
  (Mmatch (fun _=>_) t (cons p1%mtac_patt (.. (cons pn%mtac_patt nil) ..))) 
    (at level 90, p1 at level 210, pn at level 210, only parsing).
Notation "'mmatch' t 'return' 'M' p 'with' p1 | .. | pn 'end'" := 
  (Mmatch (fun _=>p) t (cons p1%mtac_patt (.. (cons pn%mtac_patt nil) ..))) 
    (at level 90, p1 at level 210, pn at level 210, only parsing).
Notation "'mmatch' t 'as' x 'return' 'M' p 'with' p1 | .. | pn 'end'" := 
  (Mmatch (fun x=>p) t (cons p1%mtac_patt (.. (cons pn%mtac_patt nil) ..))) 
    (at level 90, p1 at level 210, pn at level 210, only parsing).


Notation "'mfix1' f ( x : A ) : 'M' B := b" := (@Mfix1 A (fun x=>B) (fun f (x : A)=>b))
  (at level 85, f at level 0, x at next level, format
  "'[v  ' 'mfix1'  f  '(' x  ':'  A ')'  ':'  'M'  B  ':=' '/  ' b ']'").

Notation "'mfix2' f ( x : A1 ) ( y : A2 ) : 'M' B := b" := 
  (@Mfix2 A1 (fun x=> A2)%type (fun x y=>B) (fun f (x : A1) (y : A2)=>b))
  (at level 85, f at level 0, x at next level, y at next level, format
  "'[v  ' 'mfix2'  f  '(' x  ':'  A1 ')'  '(' y  ':'  A2 ')'  ':'  'M'  B  ':=' '/  ' b ']'").

Notation "'mfix3' f ( x : A1 ) ( y : A2 ) ( z : A3 ) : 'M' B := b" := 
  (@Mfix3 A1 (fun x=> A2)%type (fun x y=> A3)%type (fun x y z=>B) 
    (fun f (x : A1) (y : A2) (z : A3)=>b))
  (at level 85, f at level 0, x at next level, y at next level, z at next level, format
  "'[v  ' 'mfix3'  f  '(' x  ':'  A1 ')'  '(' y  ':'  A2 ')'  '(' z  ':'  A3 ')'  ':'  'M'  B  ':=' '/  ' b ']'").


Notation "'mtry' a 'with' | p1 | .. | pn 'end'" := 
  (Mtry a (fun e=>
    (Mmatch (fun _=>_) e (cons p1%mtac_patt (.. (cons pn%mtac_patt (cons (Mbase e (fun _ =>Mraise e)) nil)) ..)))))
    (at level 82, p1 at level 210, pn at level 210, only parsing).

Notation "'mtry' a 'with' p1 | .. | pn 'end'" := 
  (Mtry a (fun e=>
    (Mmatch (fun _=>_) e (cons p1%mtac_patt (.. (cons pn%mtac_patt (cons (Mbase e (fun _ =>Mraise e)) nil)) ..)))))
    (at level 82, p1 at level 210, pn at level 210, only parsing).

Notation "'mtry' a 'as' e 'in' | p1 | .. | pn 'end'" := 
  (Mtry a (fun e=>Mmatch (fun _=>_) e (cons p1%mtac_patt (.. (cons pn%mtac_patt (cons (Mbase e (fun _=>raise e)) nil)) ..))))
    (at level 82, e at next level, p1 at level 210, pn at level 210, format 
   "'[v' 'mtry' '/  '  a  '/' 'as'  e  'in' '/' '|'  p1  '/' '|'  ..  '/' '|'  pn '/' 'end' ']'"
).

Notation "'nu' x .. y , a" := (Mnu (fun x=>.. (Mnu (fun y=> a))..)) 
(at level 81, x binder, y binder, right associativity). 

Notation "'is_var'" := Mis_var.
Notation "'abs'" := Mabs.
Notation "'evar'" := Mevar.
Notation "'is_evar'" := Mis_evar.

End Mtac2Notations.
