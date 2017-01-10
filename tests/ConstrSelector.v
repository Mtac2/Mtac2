Require Import MetaCoq.MetaCoq.

(** Obtains the list of constructors of a type I from a type of the
   form A1 -> ... -> An -> I *)
Definition get_constrs :=
  mfix1 fill (T : Type) : M (list dyn) :=
    mmatch T with
    | [? A B] A -> B => fill B
    | _ =>
      l <- constrs T;
      let (_, l') := l in
      ret l'
    end.

Definition index {A} (c: A) :=
  l <- get_constrs A;
  (mfix2 f (i : nat) (l : list dyn) : M nat :=
    mmatch l with
    | [? l'] (Dyn c :: l') => ret i
    | [? d' l'] (d' :: l') => f (S i) l'
    end) 0 l.

Eval compute in eval (index 0).
Eval compute in eval (index S).
Eval compute in eval (index eq_refl).
Eval compute in eval (index nil).
Eval compute in eval (index (@cons _)).


Definition snth_index {A:Type} (c:A) (t:tactic) : selector :=
  i <- index c; snth i t.

Notation "'case' c 'do' t" := (snth_index c t) (at level 40).

Goal forall b, orb b (negb b) = true.
MProof.
  destructn 0 &> case true do reflexivity.
  reflexivity.
Qed.

Definition elim0 : tactic := fun g=>
  gT <- goal_type g;
  m <- fresh_binder_name gT;
  A <- evar Type;
  intro_base m (fun x:A=>elim x) g.

Definition rrewrite {A} (x: A) := trewrite RightRewrite [Dyn x].

Goal forall n, n + 0 = n.
MProof.
  elim0 &> case 0 do reflexivity.
  intros. simpl. select (_ = _) rrewrite.
  reflexivity.
Qed.