From Mtac2 Require Import Mtac2 Datatypes List MTeleMatch MFix.
Import M.notations Mtac2.List.ListNotations.

Require Import Arith.
Lemma silly x1 x2 y : x2 + x1 = y -> x1 + x2 = y.
Proof. intros <-. rewrite plus_comm. reflexivity. Qed.


Definition coerce_evar {A B : Type} : A -> M B
  := fun (x : A) =>
       'oH <- M.unify A B UniEvarconv;
       match oH with
       | mSome H =>
         match H in (_ =m= T) return (M T) with
         | meq_refl => M.ret x
         end
       | mNone => M.raise CantCoerce
       end.

Definition coerce_evar_app {A} {P : A -> Type} a1 a2 : P a1 -> M (P a2) :=
  coerce_evar (A := P a1) (B:= P a2).

Polymorphic Cumulative Structure execV {A} (f : M A) B := ExecV { value : B } .

Canonical Structure the_value {A} (f : M A) v := ExecV _ f (lift f v) v.

Arguments value {A} f {B} {e}.

Set Use Unicoq.

Notation "'Σ' x .. y ,  t" :=
  (sigT (fun x => .. (sigT (fun y => t)) ..)) (at level 200, x binder, y binder).

(* Definition test {T} (t : T) : M (Σ X (x : X) f, f x = t) := *)
(*   mmatch T return M (Σ X x f, f x = t) with *)
(*   | [? X] (X -> T) => _ *)
(*   end. *)

Set Unicoq Debug.
(* Goal True. *)
(* refine (let H := _ in let _ : value (M.ret I) =m= H := meq_refl in H). *)
(* Qed. *)

Notation "'[run'  t ]" :=
  (let H := _ in let _ : value t = H := eq_refl in H).
Set Printing Universes.
Definition coerce_evar_app_eq {A B} {P : A -> Type} a1 a2 (b : B) : B =m= P a1 -> M (P a2).
  intros H. rewrite H in b. apply (coerce_evar_app a1 a2 b).
Defined.

Notation "'[cap'  y  'for'  x  'in'  t ]" :=
  (let T := M.type_of t in
   let _ : T := t in
   let P' :=
       [run
          M.print "bla1";;
          M.abs_fun (P:=fun _ => Type) x T]
   in
   [run
      t' <- M.coerce t;
    M.print "bla2";;
      (coerce_evar_app (P:=P') x y t')]).

Definition locked {X} (x : X) : X. auto. Qed.

Eval cbv -[coerce_evar_app plus] in (fun x : nat => [cap 1 for x in x + 1]).
Eval cbn in fun x => [run M.abs_fun (P:=fun _ => Type) (x) (locked x = 1)].
Eval cbv in fun x y (f : locked x = y) => [cap 3 for x in f].
Definition bla y := Eval cbv -[coerce_evar_app plus] in (fun x' x1 x2 : nat => fun (f : x' = y) => [cap 5+3 for x' in f]) _ 3 5 : _ -> M (5+3 = y).
Compute M.eval (bla ltac:(auto)).
Eval cbn in fun x => [run (M.abs_fun (P:=fun _=>nat) (3+5) (x+3+5+1))].

(* Notation "s '<$s'  x > t" := *)
(*   ([cap x in t]) (at level 61, x at next level, left associativity). *)

Notation "s '<$s' n  > t" :=
  (s
     [run
        M.ret t
    ]
  ) (at level 61, n at next level, left associativity).
`
Check fun x => (fun t => [run M.abs_fun x (type_of t)]) (x + 1).
Definition test_l {x1 x2 x' y : nat} (f : x' = y) : M (x1 + x2 = y) :=
  silly _ _ _ <$> [cap (x2+x1) for x' in f].



Definition assumption_to_goal' : forall A, M ({T : Type & T -> A}) :=
  mfix rec A : M {T : Type & T -> A } :=
  mtmmatch A as A return M {T : Type & T -> A} with
  | [? X] ((M X) : Type) =c> M.ret (existT _ X (fun x => M.ret x))
  | [? X F] (forall x : X, F x) =c>
    s <- M.fresh_binder_name A;
    M.nu s mNone (fun x =>
      M.print_term ("F", F);;
      let Fx := rone_step (F x) in
      ''(existT _ T G) <- rec (Fx);
      T' <- M.abs_fun x T;
      M.print_term ("T'", T');;
      (* T' = forall x, T *)
      G <- M.coerce G;
      G <- M.abs_fun (P:=fun x => T' x -> F x) x G;
      M.print_term ("G", G);;
      let G' := fun t' : (forall x : X, T' x) => fun x : X => G x (t' x) in
      let G' := reduce (RedStrong RedAll) G' in (* TODO: fixme! too strong *)
      M.print_term ("G'", G');;
      M.ret (existT _ (forall x, T' x) G')
    )
    | A =n> M.ret (existT _ _ (fun x => x))
  end.

Check ltac:(mrun (assumption_to_goal' (forall x : nat, x > 0 -> M (x = x)))).

(* Definition assumption_to_goal (A : Type) : tactic := *)
(*   \tactic g => *)
(*   ''(existT _ T G) <- assumption_to_goal' A; *)
(*   t <- M.evar T; *)
(*   T.exact (G t) g;; *)
(*   M.ret [m: (tt, Goal t)] *)
(* . *)

Definition mtac_to_tactic {T : Type} (t : T) : tactic :=
  \tactic g =>
  gty <- M.goal_type g;
  (mfix rec T : T -> M (mlist (unit * goal)) :=
    mtmmatch T as T return T -> M (mlist (unit * goal)) with
    | (M gty : Type) =c> fun t => p <- t; T.exact p g
    | [? P Q] P -> Q =c> fun H : P -> Q =>
        ''(existT _ T G) <- assumption_to_goal' P;
        t <- M.evar T;
        let Gt := rone_step (G t) in
        let HGt := rone_step (H Gt) in
        gl <- rec _ HGt;
        M.print_term "??";;
        M.ret (mcons (tt, Goal t) gl)
    | T =n> fun _ => M.failwith "The given mtac function does not solve goals of this shape."
    end
  )
  T t
.

(* Goal (1 = 1). *)
(* MProof. *)
(* mtac_to_tactic (fun (H : M False) => t <- H; M.ret (match t with end)). *)
(* Abort. *)


(* Goal (1 = 1). *)
(* MProof. *)
(* mtac_to_tactic (fun (H : forall x : nat, False) => M.ret (match H 1 with end)). *)
(* Abort. *)