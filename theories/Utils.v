Require Import Lists.List.
Import ListNotations.

Definition dec_bool {P} (x : {P}+{~P}) : bool :=
  match x with
  | left _ => true
  | _ => false
  end.

Definition option_to_bool {A} (ox : option A) : bool :=
  match ox with Some _ => true | _ => false end.

Definition is_empty {A} (l: list A) : bool :=
  match l with [] => true | _ => false end.

Fixpoint but_last {A} (l : list A) : list A :=
  match l with
  | [] => []
  | [a] => []
  | a :: ls => a :: but_last ls
  end.

Fixpoint nsplit {A} (n : nat) (l : list A) : list A * list A :=
  match n, l with
  | 0, l => ([], l)
  | S n', x :: l' => let (l1, l2) := nsplit n' l' in (x :: l1, l2)
  | _, _ => ([], [])
  end.

Polymorphic Inductive poption (A : Type) : Type := PSome : A -> poption A | PNone : poption A.

Arguments PSome {_} _.
Arguments PNone {_}.

Polymorphic Inductive plist (A : Type) : Type := pnil : plist A | pcons : A -> plist A -> plist A.

Arguments pnil {_}.
Arguments pcons {_} _ _.

Delimit Scope list_scope with list.
Bind Scope list_scope with list.

Open Scope list_scope.

Infix "::" := pcons (at level 60, right associativity) : list_scope.

(** Standard notations for lists.
In a special module to avoid conflicts. *)
Module ListNotations.
Notation " [ ] " := pnil (format "[ ]") : list_scope.
Notation " [ x ] " := (pcons x pnil) : list_scope.
Notation " [ x ; y ; .. ; z ] " :=  (pcons x (pcons y .. (pcons z pnil) ..)) : list_scope.
End ListNotations.

Polymorphic Definition papp :=
fun {A : Type} =>
  fix papp (l m : plist A) {struct l} : plist A :=
  match l with
  | pnil => m
  | pcons a l1 => pcons a (papp l1 m)
  end.

Section Map.
  Import ListNotations.

  Polymorphic Definition pmap := fun {A : Type} {B : Type} (f : A -> B) =>
    fix pmap (l : plist A) : plist B :=
      match l with
      | [] => []
      | a :: t => (f a) :: (pmap t)
      end.

  Polymorphic Definition pconcat := fun {A : Type} =>
    fix pconcat (l : plist (plist A)) : plist A :=
      match l with
      | pnil => pnil
      | x :: l0 => papp x (pconcat l0)
     end.

End Map.

Polymorphic Definition pfold_left :=
fun {A B : Type}
  (f : A -> B -> A) =>
fix fold_left (l : plist B) (a0 : A) {struct l} : A :=
  match l with
  | pnil => a0
  | pcons b t => fold_left t (f a0 b)
  end.

Polymorphic Definition pfilter := fun {A} (f : A -> bool) =>
fix pfilter (l : plist A) : plist A :=
  match l with
  | pnil => pnil
  | pcons x l0 => if f x then pcons x (pfilter l0) else pfilter l0
  end.

Polymorphic Definition prev_append :=
fun {A : Type} =>
fix prev_append (l l' : plist A) {struct l} : plist A :=
  match l with
  | pnil => l'
  | pcons a l0 => prev_append l0 (pcons a l')
  end.

Polymorphic Definition prev' := fun {A : Type} (l : plist A) => prev_append l pnil.

Polymorphic Inductive peq (A : Type) (x : A) : A -> Prop := peq_refl : peq _ x x.

Arguments peq {_} _ _.
Notation "x 'p=' y" := (peq x y) (at level 70, no associativity).

Arguments peq_refl {A x} , [A] x.

Polymorphic Definition peq_sym :=
  fun {A : Type} {x y : A} (H : peq x y) =>
    match H in (peq _ y0) return (peq y0 x) with
    | peq_refl _ => peq_refl _
    end.

Polymorphic Inductive pprod (A B : Type) := ppair : A -> B -> pprod A B.
Arguments ppair {_ _} _ _.
Notation "x * y" := (pprod x y) : type_scope.
Notation "( x , y , .. , z )" := (ppair .. (ppair x y) .. z) : core_scope.

Polymorphic Definition pfst {A B} (p : A*B) := match p with ppair x _ => x end.
Polymorphic Definition psnd {A B} (p : A*B) := match p with ppair _ x => x end.
