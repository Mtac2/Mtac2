(* -*- mode: coq; coq-prog-args: ("-emacs" "-top" "min_bug_univpoly") -*- *)
(* File reduced by coq-bug-finder from original input, then from 2673 lines to 1040 lines, then from 1056 lines to 1040 lines, then from 1055 lines to 696 lines, then from 704 lines to 696 lines *)
(* coqc version 8.6.1 (August 2017) compiled on Aug 8 2017 15:55:58 with OCaml 4.02.3
   coqtop version blackbox:/home/janno/.opam/ra-gps/build/coq.8.6.dev,master (6dbffe1db990966321ce47fede1840252dc67688) *)

(* commenting this makes it work *)
Set Universe Polymorphism.

Unset Universe Minimization ToSet.
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False := .
End LocalFalse.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Require Coq.Strings.String.

Module Import LocalFalse.
Inductive False := .
End LocalFalse.

Inductive False := .

Set Implicit Arguments.

Inductive eq (A:Type) (x:A) : A -> Prop :=
    eq_refl : x = x :>A

where "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (x <> y :>_) : type_scope.
Arguments eq_refl {A x} , [A] x.
Arguments eq_rect [A] x P _ y _ : rename.

Section Logic_lemmas.

  Section equality.
    Variables A B : Type.
    Variable f : A -> B.
    Variables x y z : A.

    Theorem eq_sym : x = y -> y = x.
admit.
Defined.

    Theorem eq_trans : x = y -> y = z -> x = z.
admit.
Defined.

    Theorem f_equal : x = y -> f x = f y.
admit.
Defined.

    Theorem not_eq_sym : x <> y -> y <> x.
admit.
Defined.

  End equality.

  Definition eq_ind_r :
    forall (A:Type) (x:A) (P:A -> Prop), P x -> forall y:A, y = x -> P y.
admit.
Defined.

  Definition eq_rec_r :
    forall (A:Type) (x:A) (P:A -> Set), P x -> forall y:A, y = x -> P y.
admit.
Defined.

  Definition eq_rect_r :
    forall (A:Type) (x:A) (P:A -> Type), P x -> forall y:A, y = x -> P y.
admit.
Defined.
End Logic_lemmas.
  Notation "'rew' H 'in' H'" := (eq_rect _ _ H' _ H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  H  in  '/' H' ']'").
  Notation "'rew' [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' <- H 'in' H'" := (eq_rect_r _ H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  <-  H  in  '/' H' ']'").

Lemma rew_opp_r : forall A (P:A->Type) (x y:A) (H:x=y) (a:P y), rew H in rew <- H in a = a.
admit.
Defined.

Lemma rew_opp_l : forall A (P:A->Type) (x y:A) (H:x=y) (a:P x), rew <- H in rew H in a = a.
admit.
Defined.

Theorem f_equal2 :
  forall (A1 A2 B:Type) (f:A1 -> A2 -> B) (x1 y1:A1)
    (x2 y2:A2), x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.
admit.
Defined.

Theorem f_equal3 :
  forall (A1 A2 A3 B:Type) (f:A1 -> A2 -> A3 -> B) (x1 y1:A1)
    (x2 y2:A2) (x3 y3:A3),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> f x1 x2 x3 = f y1 y2 y3.
admit.
Defined.

Theorem f_equal4 :
  forall (A1 A2 A3 A4 B:Type) (f:A1 -> A2 -> A3 -> A4 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> f x1 x2 x3 x4 = f y1 y2 y3 y4.
admit.
Defined.

Theorem f_equal5 :
  forall (A1 A2 A3 A4 A5 B:Type) (f:A1 -> A2 -> A3 -> A4 -> A5 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4) (x5 y5:A5),
    x1 = y1 ->
    x2 = y2 ->
    x3 = y3 -> x4 = y4 -> x5 = y5 -> f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5.
admit.
Defined.

Theorem f_equal_compose : forall A B C (a b:A) (f:A->B) (g:B->C) (e:a=b),
  f_equal g (f_equal f e) = f_equal (fun a => g (f a)) e.
admit.
Defined.

Theorem eq_trans_refl_l : forall A (x y:A) (e:x=y), eq_trans eq_refl e = e.
admit.
Defined.

Theorem eq_trans_refl_r : forall A (x y:A) (e:x=y), eq_trans e eq_refl = e.
admit.
Defined.

Theorem eq_sym_involutive : forall A (x y:A) (e:x=y), eq_sym (eq_sym e) = e.
admit.
Defined.

Theorem eq_trans_sym_inv_l : forall A (x y:A) (e:x=y), eq_trans (eq_sym e) e = eq_refl.
admit.
Defined.

Theorem eq_trans_sym_inv_r : forall A (x y:A) (e:x=y), eq_trans e (eq_sym e) = eq_refl.
admit.
Defined.

Theorem eq_trans_assoc : forall A (x y z t:A) (e:x=y) (e':y=z) (e'':z=t),
  eq_trans e (eq_trans e' e'') = eq_trans (eq_trans e e') e''.
admit.
Defined.

Theorem eq_id_comm_l : forall A (f:A->A) (Hf:forall a, a = f a), forall a, f_equal f (Hf a) = Hf (f a).
admit.
Defined.

Theorem eq_id_comm_r : forall A (f:A->A) (Hf:forall a, f a = a), forall a, f_equal f (Hf a) = Hf (f a).
admit.
Defined.

Lemma eq_refl_map_distr : forall A B x (f:A->B), f_equal f (eq_refl x) = eq_refl (f x).
admit.
Defined.

Lemma eq_trans_map_distr : forall A B x y z (f:A->B) (e:x=y) (e':y=z), f_equal f (eq_trans e e') = eq_trans (f_equal f e) (f_equal f e').
admit.
Defined.

Lemma eq_sym_map_distr : forall A B (x y:A) (f:A->B) (e:x=y), eq_sym (f_equal f e) = f_equal f (eq_sym e).
admit.
Defined.

Lemma eq_trans_sym_distr : forall A (x y z:A) (e:x=y) (e':y=z), eq_sym (eq_trans e e') = eq_trans (eq_sym e') (eq_sym e).
admit.
Defined.

Lemma eq_trans_rew_distr : forall A (P:A -> Type) (x y z:A) (e:x=y) (e':y=z) (k:P x),
    rew (eq_trans e e') in k = rew e' in rew e in k.
admit.
Defined.

Lemma rew_const : forall A P (x y:A) (e:x=y) (k:P),
    rew [fun _ => P] e in k = k.
admit.
Defined.

Inductive option (A:Type) : Type :=
  | Some : A -> option A
  | None : option A.
Arguments None {A}.

Definition option_map (A B:Type) (f:A->B) (o : option A) : option B :=
  match o with
    | Some a => @Some B (f a)
    | None => @None B
  end.

Inductive sum (A B:Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.

Inductive prod (A B:Type) : Type :=
  pair : A -> B -> prod A B.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.


Inductive list (A : Type) : Type :=
 | nil : list A
 | cons : A -> list A -> list A.

Arguments nil {A}.
Infix "::" := cons (at level 60, right associativity) : list_scope.

Local Open Scope list_scope.

Definition length (A : Type) : list A -> nat :=
  fix length l :=
  match l with
   | nil => O
   | _ :: l' => S (length l')
  end.

Definition app (A : Type) : list A -> list A -> list A :=
  fix app l m :=
  match l with
   | nil => m
   | a :: l1 => a :: app l1 m
  end.

Infix "++" := app (right associativity, at level 60) : list_scope.
Notation "[m: ]" := nil (format "[m: ]") : list_scope.
Notation "[m: x ]" := (cons x nil) : list_scope.

Import Strings.String.
Import NArith.BinNat.
Unset Implicit Arguments.

Inductive Exception : Type := exception : Exception.

Definition NotUnifiable {A} (x y : A) : Exception.
admit.
Defined.

Definition Failure (s : string) : Exception.
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

Polymorphic Record dyn := Dyn { type : Type; elem :> type }.

Inductive redlist A := rlnil | rlcons : A -> redlist A -> redlist A.

Arguments rlnil {_}.
Arguments rlcons {_} _ _.
Notation "[rl: x ; .. ; y ]" := (rlcons x (.. (rlcons y rlnil) ..)).

Inductive RedFlags :=
| RedBeta | RedDelta | RedMatch | RedFix | RedZeta
| RedDeltaC | RedDeltaX
| RedDeltaOnly : redlist dyn -> RedFlags
| RedDeltaBut : redlist dyn -> RedFlags.

Inductive Reduction :=
| RedNone
| RedSimpl
| RedOneStep
| RedWhd : redlist RedFlags -> Reduction
| RedStrong : redlist RedFlags -> Reduction
| RedVmCompute.

Inductive Unification : Set :=
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

Definition reduce (r : Reduction) {A} (x : A) := x.
Notation rone_step := (reduce RedOneStep).

Inductive goal :=
  | Goal : forall {A}, A -> goal
  | AHyp : forall {A}, option A -> (A -> goal) -> goal
  | HypRem : forall {A}, A -> goal -> goal.

Inductive pattern (M : Type -> Type) (A : Type) (B : A -> Type) (y : A) : Prop :=
  | pbase : forall x : A, (y = x -> M (B x)) -> Unification -> pattern M A B y
  | ptele : forall {C}, (forall x : C, pattern M A B y) -> pattern M A B y.

Arguments pbase {M A B y} _ _ _.
Arguments ptele {M A B y C} _.

Declare Scope pattern_scope.

Notation "[? x .. y ] ps" := (ptele (fun x => .. (ptele (fun y => ps)).. ))
  (at level 202, x binder, y binder, ps at next level) : pattern_scope.
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

Declare Scope with_pattern_scope.

Notation "'with' | p1 | .. | pn 'end'" :=
  ((@cons (pattern _ _ _ _) p1%pattern (.. (@cons (pattern _ _ _ _) pn%pattern nil) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.
Notation "'with' p1 | .. | pn 'end'" :=
  ((@cons (pattern _ _ _ _) p1%pattern (.. (@cons (pattern _ _ _ _) pn%pattern nil) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.

Delimit Scope with_pattern_scope with with_pattern.

Inductive t@{U1 U2 E1 L1 H1 O1} : Type@{U1} -> Prop :=
| ret : forall {A : Type@{U1}}, A -> t A
| bind : forall {A : Type@{U1}} {B : Type@{U1}},
   t A -> (A -> t B) -> t B
| mtry' : forall {A : Type@{U1}}, t A -> (Exception@{E1} -> t A) -> t A
| raise : forall {A : Type@{U1}}, Exception@{E1} -> t A

| nu : forall {A : Type@{U1}} {B : Type@{U1}}, string -> option A -> (A -> t B) -> t B

| gen_evar : forall (A : Type@{U1}), option (list@{L1} Hyp@{H1}) -> t A

| unify {A : Type@{U2}} (x y : A) : Unification -> t (option@{O1} (x = y))

| unify_univ (A B : Type@{U1}) : Unification -> t (option (A -> B))

.
(* Inductive t : Type -> Prop := *)
(* | ret : forall {A : Type}, A -> t A *)
(* | bind : forall {A : Type} {B : Type}, *)
(*    t A -> (A -> t B) -> t B *)
(* | mtry' : forall {A : Type}, t A -> (Exception -> t A) -> t A *)
(* | raise : forall {A : Type}, Exception -> t A *)

(* | nu : forall {A : Type} {B : Type}, string -> option A -> (A -> t B) -> t B *)

(* | gen_evar : forall (A : Type), option (list Hyp) -> t A *)

(* | unify {A : Type} (x y : A) : Unification -> t (option (x = y)) *)

(* | unify_univ (A B : Type) : Unification -> t (option (A -> B)) *)

(* . *)

Definition evar (A : Type) : t A := gen_evar A None.

Definition failwith {A} (s : string) : t A := raise (Failure s).

(* Definition print_term {A} (x : A) : t unit := *)
(*   bind (pretty_print x) (fun s=> print s). *)

Module Export monad_notations.
  Declare Scope M_scope.
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
    | Some eq =>

      let h := reduce (RedStrong [rl:RedBeta;RedDelta;RedMatch]) (eq_sym eq) in
      let 'eq_refl := eq in

      let b := reduce (RedStrong [rl:RedBeta]) (f h) in b
    | None => raise DoesNotMatch
    end
  | @ptele _ _ _ _ C f => e <- evar C; open_pattern (f e)
  end.

Fixpoint mmatch' {A P} (y : A) (ps : list (pattern t A P y)) : t (P y) :=
  match ps with
  | [m:] => raise NoPatternMatches
  | p :: ps' =>
    mtry' (open_pattern p) (fun e =>
      mif unify e DoesNotMatch UniMatchNoRed then mmatch' y ps' else raise e)
  end.

Module Export notations.
  Export monad_notations.

  (* Notation "'mfix1' f ( x : A ) : 'M' T := b" := *)
  (*   (fix1 (fun x=>T%type) (fun f (x : A)=>b%MC)) *)
  (*   (at level 85, f at level 0, x at next level, format *)
  (*   "'[v  ' 'mfix1'  f  '(' x  ':'  A ')'  ':'  'M'  T  ':=' '/  ' b ']'") : M_scope. *)

  Notation "'mmatch' x ls" :=
    (@mmatch' _ (fun _ => _) x ls%with_pattern)
    (at level 90, ls at level 91) : M_scope.
End notations.

Definition unify_cumul {A B} (x: A) (y: B) (u : Unification) : t bool :=
  of <- unify_univ A B u;
  match of with
  | Some f =>
    let fx := reduce RedOneStep (f x) in
    oeq <- unify fx y u;
    match oeq with Some _ => ret true | None => ret false end
  | None => ret false
  end.


(* UNCOMMENT THE NEXT TWO COMMENTS TO MAKE IT COMPILE *)
(* Unset Universe Polymorphism. *)
Definition cumul_or_fail
           {A B} (x: A) (y: B) : t unit :=
  b <- unify_cumul x y UniCoq;
  if b then ret tt else raise (NotCumul x y).
(* Set Universe Polymorphism. *)

Notation M := t.

Import notations.

Definition NotAProduct : Exception.
admit.
Defined.

Definition gtactic (A : Type) := goal -> M (list (A * goal)).
Notation tactic := (gtactic unit).

Definition exact {A} (x:A) : tactic := fun g =>
  match g with
  | Goal g => cumul_or_fail x g;; ret [m:]
  | _ => raise NotAGoal
  end.

Fail Definition intro_base {A B} (var : string) (t : A -> gtactic B) : gtactic B := fun g =>
  mmatch g with
  | [? P e] @Goal (forall x:A, P x) e =u>
    @nu nat _ var None (fun x=>
                          exact nat g;;
                               raise exception)
    | _ => raise NotAProduct
  end.
