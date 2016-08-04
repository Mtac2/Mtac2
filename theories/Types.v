Module PolymorphicTypes.
Local Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Inductive prod (A B : Type) : Type :=
| pair : A -> B -> prod A B.
Arguments prod _ _.
Arguments pair [_ _] _ _.
Infix "*" := (prod) : type_scope.
Definition fst {A B : Type} (p : A * B) := let (x, _) := p in x.
Definition snd {A B : Type} (p : A * B) := let (_, y) := p in y.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z)
                      : core_scope.

Inductive option (T : Type) : Type :=
| None : option T
| Some (t : T) : option T.
Arguments None [_].
Arguments Some [_] _.

Reserved Notation "[]" (at level 0).
Reserved Notation "[ x ]" (at level 0).
Polymorphic Inductive list (X : Type) : Type :=
| nil : list X
| cons (x : X) (xs : list X) : list X
where "[]" := (nil _)
and "x :: xs" := (cons _ x xs)
and "[ x ]" := (cons _ x (nil _)).
Arguments nil [_].
Arguments cons [_] _ _.
Definition tl {X} (l : list X) : list X :=
  match l with
  | nil => nil
  | x :: xs => xs
  end.
Fixpoint app {X} (l1 l2 : list X) {struct l1} : list X :=
  match l1 with
  | nil => l2
  | x :: xs => x :: app xs l2
  end.
Infix "++" := app.
Fixpoint concat {X} (l : list (list X)) : list X :=
  match l with
  | nil => nil
  | x :: xs => x ++ (concat xs)
  end.
Fixpoint map {X Y} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | nil => nil
  | x :: xs => f x :: map f xs
  end.
Fixpoint length {X} (l : list X) : nat :=
  match l with
  | nil => 0
  | _ :: xs => S (length xs)
  end.
Fixpoint nth_error {X} (l:list X) (n:nat) {struct n} : option X :=
  match n, l with
  | O, x :: _ => Some x
  | S n, _ :: l => nth_error l n
  | _, _ => None
  end.
Fixpoint rev {X} (l:list X) : list X :=
  match l with
  | [] => []
  | x :: l' => rev l' ++ [x]
  end.


Inductive eq {X : Type} (x : X) : X -> Prop :=
| eq_refl : eq x x
where "x = y" := (@eq _ x y) : type_scope.
Arguments eq_refl [_] _.
End PolymorphicTypes.

Module StandardTypes.
  From Coq.Lists Require Export List.
  Export ListNotations.
End StandardTypes.

Export StandardTypes.