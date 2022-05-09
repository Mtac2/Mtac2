(** A simple example showcasing Mtac2 for PL proofs *)

(** The language are if-then-elses with conditional (bool) expressions
    and a nil value (to make it sligthly more interesting). *)
Inductive binop := band | bor.
Inductive unop := bnot.

Inductive exp := ttrue | ffalse | nil
                 | B : binop -> exp -> exp -> exp
                 | U : unop -> exp -> exp.

Inductive st :=
| ife : exp -> st -> st -> st
| sc.

Notation ";;" := sc.
Notation "'If' e 'then' s1 'else' s2 'end'" := (ife e s1 s2) (at level 10).
Notation "a 'or' b" := (B bor a b) (at level 10).
Notation "a 'and' b" := (B band a b) (at level 10).

Check (If ffalse or nil then ;; else If ttrue then ;; else ;; end end).

Definition delta : exp -> exp := fun e=>
                                   match e with
                                   | B band ffalse e' => ffalse
                                   | B band nil e' => ffalse
                                   | B band _ e' => e'
                                   | B bor ffalse e' => e'
                                   | B bor nil e' => e'
                                   | B bor v e' => v
                                   | U not ffalse => ttrue
                                   | U not nil => ttrue
                                   | U not _ => ffalse
                                   | _ => e
                                   end.

Inductive is_val : exp -> Prop :=
| vnil : is_val nil
| vtrue : is_val ttrue
| vfalse : is_val ffalse.

Inductive step : st -> st -> Prop :=
| IfT : forall s1 s2 v, is_val v -> v <> nil -> v <> ffalse ->
                        step (If v then s1 else s2 end) s1
| IfF : forall s1 s2, step (If ffalse then s1 else s2 end) s2
| IfN : forall s1 s2, step (If nil then s1 else s2 end) s2
| Ife : forall s1 s2 e1 e2, estep e1 e2 ->
        step (If e1 then s1 else s2 end) (If e2 then s1 else s2 end)
with
estep : exp -> exp -> Prop :=
| BinV : forall op v e, estep (B op v e) (delta (B op v e))
| BinS : forall op e e1 e2, estep e1 e2 -> estep (B op e1 e) (B op e2 e)
| UnV : forall op v, estep (U op v) (delta (U op v))
| UnS : forall op e1 e2, estep e1 e2 -> estep (U op e1) (U op e2).

Inductive steps : st -> st -> Prop :=
| steps0: forall m, steps m m
| stepsn: forall p p' p'', step p p' ->
           steps p' p'' ->
           steps p p''.


Example test : steps (If nil or ffalse then ;; else ;; end) ;;.
Proof.
  eapply stepsn. eapply Ife. econstructor. simpl.
  eapply stepsn. eapply IfF. econstructor.
Qed.

#[global] Hint Constructors is_val st exp step estep steps unop binop.

(** We prove that every program terminates in a ;;. We do it first in plain
    Ltac. *)
Lemma always_sc : forall p, steps p ;;.
Proof.
  induction 0; eauto.
  induction e; eauto.
  - eapply stepsn; repeat (assumption || econstructor || discriminate).
  - case b; induction e1; eauto.
  - case u; induction e; eauto.
    + eapply stepsn. eapply Ife. econstructor. simpl.
      eapply stepsn. eapply IfT. econstructor.
      discriminate. discriminate. assumption.
    + eapply stepsn. eapply Ife. econstructor. simpl.
      eapply stepsn. eapply IfT. econstructor.
      discriminate. discriminate. assumption.
Qed.

(** Now we do it in Mtac2. *)

From Mtac2 Require Import Mtac2 ConstrSelector.
Import T.
Import T.notations.

Polymorphic Definition stepNdo {A} (l : A) :=
  (apply stepsn |1> apply l |1> constructor) &> simpl.

Polymorphic Definition stepInIf := stepNdo Ife.

Polymorphic Definition stepIfTrue :=
  (stepNdo IfT) &> try (discriminate || T.assumption).

Definition UnsoledGoals : Exception. constructor. Qed.
Notation "t '[x]'" := (t &> T.raise UnsoledGoals) (at level 0).

Lemma alwas_sc_mtac2 : forall p, steps p ;;.
MProof.
  intros p.
  (select st >>= induction) &> case steps0 do eauto [x].
  (select exp >>= induction) &> case false, nil do eauto [x].
  + stepIfTrue.
  + (select binop >>= destruct) &> (select exp >>= induction) &> eauto [x].
  + (select unop >>= destruct) &> (select exp >>= induction)
           &> case true, B, U do eauto [x] &> (stepInIf &> stepIfTrue).
Qed.