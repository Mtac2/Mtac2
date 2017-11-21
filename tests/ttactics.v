From Mtac2 Require Import Mtac2.

(** We use a synonim to prod to emulate typed goals. The idea
    is that at the left we have the hypotheses, and at the right
    the goal type. A goal H1, ..., Hn |- G is then written
    (H1 * ... * Hn) =m> G

    A lemma lifted to this type will produce an element of type G given
    promises (evars) for H1, ..., Hn.
*)

Definition myprod := prod.
Arguments myprod _%type _%type.

Notation "T1 '=m>' G" := (myprod T1 G)
  (at level 98, no associativity,
   format "T1  =m>  G") : type_scope.


Import M. Import M.notations.

(** composes on the left of the arrow *)
Definition compl {A} {B} (f: M (A =m> B)) (g : M A) : M B :=
  ''(a, b) <- f;
  a' <- g;
  mif unify a a' UniCoq then
    ret b
  else failwith "nope".

(** composes a product *)
Definition compi {A} {B} (g : M A) (h : M B) : M (A * B) :=
  g >>= fun xg=> h >>= fun xh => ret (xg, xh).

(** A typed assumption tactic *)
Definition assumption {A} : M A :=
  l <- hyps;
  let f := mfix1 f (l : mlist Hyp) : M A :=
    mmatch l with
    | [? x d l'] (@ahyp A x d :m: l') => M.ret x
    | [? ah l'] (ah :m: l') => f l'
    | _ => failwith "no ass"
    end in
  f l.

(** Solves goal A provided tactic t *)
Definition use_tactic {A} (t: tactic) : M A :=
  e <- evar A;
  l <- t (Goal e);
  l' <- T.filter_goals l;
  match l' with mnil => ret e | _ => failwith "couldn't solve" end.

Definition is_prod T :=
  mmatch T with
  | [? A B] (A * B)%type => ret true
  | _ => ret false
  end.

Definition dest_pair {T} (x:T) : M (dyn * dyn) :=
  mmatch Dyn x with
  | [? A B a b] @Dyn (A*B) (a, b) => ret (Dyn a, Dyn b)
  end.

(** Given an element with type of the form (A1 * ... * An),
    it generates a goal for each unsolved variable in the pair. *)
Definition to_goals : forall {A}, A -> M (mlist (unit * goal)) :=
  mfix2 to_goals (A: Type) (a: A) : M _ :=
  mif is_evar a then ret [m: (tt, Goal a)]
  else
    mif is_prod A then
      ''(d1, d2) <- dest_pair a;
      let 'Dyn x := d1 in
      let 'Dyn y := d2 in
      t1s <- to_goals _ x;
      t2s <- to_goals _ y;
      ret (t1s +m+ t2s)
    else
      ret [m:].

(** From a typed tactic with type A =m> B, it generates an untyped one *)
Definition to_tactic {A B} (f: M (A =m> B)) : tactic := fun g=>
  gT <- goal_type g;
  mif unify gT B UniCoq then
    ''(a, b) <- f;
    al <- to_goals a;
    ls <- T.filter_goals al;
    T.exact b g;;
    ret ls
  else
    failwith "nope".


(** Example: transitivity *)
Definition trans {x y z: nat} : M ((x < z) * (z < y) =m> x < y) :=
  tg1 <- evar _;
  tg2 <- evar _;
  ret ((tg1, tg2), PeanoNat.Nat.lt_trans _ _ _ tg1 tg2).

Goal 1 < 3 -> 3 < 4 -> 1 < 4.
MProof.
  intros.
  compl trans (compi assumption assumption).
Qed.

Goal 1 < 3 -> 3 < 4 -> 1 < 4.
MProof.
  intros.
  compl trans (compi (use_tactic T.assumption) assumption).
Qed.

Goal 1 < 3 -> 3 < 4 -> 1 < 4.
MProof.
  intros.
  to_tactic trans &> T.try T.assumption.
Qed.


(** The idea is to generically lift lemmas like lt_trans into typed tactics like
trans *)
