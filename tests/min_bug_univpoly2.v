(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "." "Top" "-top" "min_bug_poly2") -*- *)
(* File reduced by coq-bug-finder from original input, then from 469 lines to 112 lines, then from 128 lines to 112 lines *)
(* coqc version 8.6.1 (August 2017) compiled on Aug 22 2017 10:37:48 with OCaml 4.02.3
   coqtop version 8.6.1 (August 2017) *)
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.

(* commenting this makes it work *)
Set Universe Polymorphism.

Inductive list (A : Type) : Type :=
 | nil : list A
 | cons : A -> list A -> list A.

Arguments nil {A}.

Local Open Scope list_scope.
Notation "[m: ]" := nil (format "[m: ]") : list_scope.

Inductive option A := Some : A -> option A | None.
Arguments Some {A} _.
Arguments None {A}.

Inductive eq {A : Type} (x : A) : A -> Prop :=  eq_refl : eq x x.
Arguments eq_refl {A} _.

Inductive goal :=
  | Goal : forall {A}, A -> goal.

Inductive t : Type -> Prop :=
| ret : forall {A : Type}, A -> t A
| bind : forall {A : Type} {B : Type},
   t A -> (A -> t B) -> t B

| unify {A : Type} (x y : A) : t (option (x = y))

| unify_univ (A B : Type) : t (option (A -> B))

.
  Delimit Scope M_scope with MC.
  Open Scope M_scope.

  Notation "r '<-' t1 ';' t2" := (@bind _ _ t1 (fun r=> t2%MC))
    (at level 81, right associativity, format "'[' r  '<-'  '[' t1 ;  ']' ']' '/' t2 ") : M_scope.
  Notation "t1 ';;' t2" := (bind t1 (fun _ => t2%MC))
    (at level 81, right associativity, format "'[' '[' t1 ;;  ']' ']' '/' t2 ") : M_scope.
  Notation "t >>= f" := (bind t f) (at level 70) : M_scope.

Definition unify_cumul {A B} (x: A) (y: B) : t bool :=
  of <- unify_univ A B;
  match of with
  | Some f =>
    let fx := f x in
    oeq <- unify fx y;
    match oeq with Some _ => ret true | None => ret false end
  | None => ret false
  end.

Definition cumul_or_fail
           {A B} (x: A) (y: B) : t unit :=
  b <- unify_cumul x y;
  ret tt.

Notation M := t.

Definition gtactic (A : Type) := goal -> M (list (A * goal)).
Notation tactic := (gtactic unit).

Fail Definition exact {A} (x:A) : tactic := fun g =>
  match g with
  | Goal g => cumul_or_fail x g;; ret [m:]
  end.
