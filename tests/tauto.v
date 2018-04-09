From Mtac2 Require Import Base.
From Mtac2 Require Tactics. (* necessary for `mrun` to work *)
From Coq Require Import List.
Import M.notations.
Import M.
Import ListNotations.

Set Universe Polymorphism.

Module Mtac_V1.
  Definition NotFound : Exception. constructor. Qed.
  Fixpoint lookup (P : Prop) (l : list dyn) : M P :=
    match l with
    | D :: l => mmatch D with | [? (p : P)] Dyn p =u> ret p | _ => lookup P l end
    |     [] => raise NotFound
    end.

  Definition TautoFail : Exception. constructor. Qed.
  Program Definition solve_tauto : forall (l : list dyn) {P : Prop}, M P :=
    mfix2 f (l : list dyn) (P : Prop) : M P :=
      mtry
        lookup P l
      with
      | NotFound =>
        mmatch P as P' return M P' with
        | True => ret I
        | [? Q1 Q2] Q1 /\ Q2 =>
          q1 <- f l Q1;
          q2 <- f l Q2;
          ret (conj q1 q2)
        | [? Q1 Q2] Q1 \/ Q2 =>
          mtry
            q1 <- f l Q1; ret (or_introl q1)
          with
          | TautoFail =>
            q2 <- f l Q2; ret (or_intror q2)
          end
        | [? (Q1 Q2 : Prop)] Q1 -> Q2 =>
          \nu q1,
            q2 <- f (Dyn q1 :: l) Q2;
            abs_fun q1 q2
        | [? X (Q : X -> Prop)] (exists x : X, Q x) =>
          x <- evar X;
          q <- f l (Q x);
          b <- is_evar x;
          if b then
            raise TautoFail
          else
            ret (ex_intro Q x q)
        | _ => raise TautoFail
        end
      end.

  Goal 5 = 7 -> exists x, x = 7.
  Proof.
    Mtac Do Unset_Trace.
    apply (eval (solve_tauto nil)).
  Qed.
End Mtac_V1.


From Mtac2 Require Import Ttactics List.
From Mtac2 Require Import Tactics.
Open Scope M_scope.
Import Mtac2.List.ListNotations.
Module Mtac_V2.
  Import TT.
  Import TT.notations.
  Definition TautoFail : Exception. constructor. Qed.

  Import Tactics.T.notations.

  Program Definition solve_tauto : tactic :=
    mfix0 solve_tauto : gtactic _ :=
    (match_goal with
     | [[ |- True ] ] => ret I
     | [[? Q1 Q2 |- Q1 /\ Q2 ] ] =>
       TT.apply (@conj _ _)
       <**> TT.by' solve_tauto
       <**> TT.by' solve_tauto
     | [[? Q1 Q2 |- Q1 \/ Q2 ] ] =>
       mtry
         TT.apply (@or_introl _ _) <**> TT.by' solve_tauto
       with
       | TautoFail =>
         TT.apply (@or_intror _ _) <**> TT.by' solve_tauto
       end
     | [[? (Q1 Q2 : Prop) |- Q1 -> Q2 ] ] =>
       TT.by' (T.introsn 1 &> solve_tauto)
     | [[? X (Q : X -> Prop) |- (exists x : X, Q x)] ] =>
       TT.by' (T.eexists &> [m: solve_tauto | T.idtac])
     | [[? P | (p : P) |- P ] ] => TT.apply p
     | [[? G |- G ] ] => raise TautoFail
     end
    )%TT%MC.

  Ltac solve_tauto := mrun solve_tauto.

  Definition x : tactic := (fun g : goal => t <- goal_prop g; T.select (t) g >>= (fun x => M.print_term x);; M.ret [m:])%MC.
  Goal 5 = 7 -> exists x, x = 7.
  Proof.
    solve_tauto.
  Qed.
End Mtac_V2.


Module Mtac_V3.
  Import T.
  Import T.notations.
  Mtac Do New Exception TautoFail.

  Definition solve_tauto : tactic :=
    mfix0 solve_tauto : gtactic _ :=
      assumption || exact I || (split &> solve_tauto)
      || (left &> solve_tauto) || (right &> solve_tauto)
      || (introsn_cont solve_tauto 1)
      || (eexists |1> solve_tauto) || raise TautoFail.
  Ltac solve_tauto := mrun solve_tauto.

  Goal 5 = 7 -> exists x, x = 7.
  Proof.
    solve_tauto.
  Qed.

End Mtac_V3.


Module Mtac_V4.
  Import TT.
  Import TT.notations.
  Definition TautoFail : Exception. constructor. Qed.

  Import Tactics.T.notations.
  Import ProdNotations.
  Definition tintro {A P} (f: forall (x:A), TT.ttac (P x))
  : TT.ttac (forall (x:A), P x) :=
  (M.nu (FreshFrom f) mNone (fun x=>
    ''(m: v, gs) <- f x;
    a <- M.abs_fun x v;
    b <- T.close_goals x (mmap (fun g=>(m: tt, g)) gs);
    let b := mmap msnd b in
    M.ret (m: a, b)))%MC.
  Definition pass {A} := TT.lift (M.evar A).

Definition texists {A} {Q:A->Prop} : ttac (exists (x:A), Q x) :=
  (e <- M.evar A;
  pf <- M.evar (Q e);
  M.ret (m: ex_intro _ e pf, [m: Goal Sorts.Sorts.SProp pf]))%MC.

  Mtac Do New Exception NotFound.

  Definition find {A:Type} :=
    (mfix1 f (l : mlist Hyp) : M A :=
      mmatch l with
      | [? x d (l': mlist Hyp)] (@ahyp A x d) :m: l' =u> M.ret x
      | [? ah l'] ah :m: l' =n> f l'
      | _ => M.raise NotFound
      end)%MC.

Definition tassumption {A:Type} : ttac A :=
  lift (hyps >>= find).

Definition tor {A:Type} (t u : ttac A) : ttac A := (mtry r <- t; M.ret r with _ => r <- u; M.ret r end)%MC.
Require Import Strings.String.
Definition ucomp1 {A B:Prop} (t: ttac A) (u: ttac B) : ttac A :=
  (''(m: v1, gls1) <- t;
  match gls1 with
  | [m: gl] =>
    ''(m: v2, gls) <- u;
    T.exact v2 gl;;
    M.ret (m: v1, gls)
  | _ => mfail "more than a goal"%string
  end)%MC.

  Program Definition solve_tauto : forall {P:Prop}, ttac P :=
    (mfix1 solve_tauto (P : Prop) : M _ :=
      mmatch P as P' return M (P' *m _) with
      | True:Prop => apply I
      | [? Q1 Q2] Q1 /\ Q2 =>
        apply (@conj _ _)
        <**> solve_tauto Q1
        <**> solve_tauto Q2
      | [? Q1 Q2] Q1 \/ Q2 =>
        mtry
          apply (@or_introl _ _) <**> solve_tauto Q1
        with
        | TautoFail =>
          apply (@or_intror _ _) <**> solve_tauto Q2
        end
      | [? (Q1 Q2 : Prop)] Q1 -> Q2 =>
        tintro (fun x:Q1=> solve_tauto Q2)
      | [? X (Q : X -> Prop)] (exists x : X, Q x) =>
        x <- M.evar X;
        apply (@ex_intro _ _ _) <**> solve_tauto (Q x)
        (* P <- M.evar Prop; *)
        (* ucomp1 texists (solve_tauto P) *)
      | _ => tor tassumption (raise TautoFail)
      end
    )%MC.

 Ltac solve_tauto := mrun solve_tauto.
Mtac Do Unset_Trace.
  Goal 5 = 7 -> exists x, x = 7.
  MProof.
    (r <- solve_tauto; M.ret (mfst r))%MC.
  Qed.
End Mtac_V4.
