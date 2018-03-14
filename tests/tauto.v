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
