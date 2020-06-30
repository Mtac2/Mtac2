From Mtac2 Require Import Mtac2.
Close Scope tactic_scope.

Mtac Do (e <- M.evar unit; e <- M.replace_evar_type (B:=id unit) e (meq_refl unit); M.ret tt).

Mtac Do (mtry M.replace_evar_type tt (meq_refl unit) with | NotAnEvar tt => M.ret tt end).

Section Test.
  Variable H : unit =m= nat.
  Fail Mtac Do (e <- M.evar unit; e <- M.replace_evar_type (B:=nat) e (H); M.print_term e).

  Fixpoint slow (n: nat) :=
    match n with
    | S n => match slow n with | 0 => slow n | _ => 0 end
    | 0 => 0
    end.

  (* Time Check eq_refl : (slow 22 = 0). *)

  (* Eval compute in slow 22. *)

  Lemma slow_is_0 n : slow n =m= 0.
  Proof. induction n; cbn; try rewrite IHn; constructor. Defined.

  Set Unicoq Trace.
  Fail Timeout 1 Mtac Do (e <- M.evar (slow 23 = 0); M.cumul_or_fail UniCoq e (eq_refl 0);; M.print_term e).

  Variable Vec : nat -> Type.
  Variable vnil : Vec 0.

  Timeout 1 Mtac Do (e <- M.evar (Vec (slow 23));
                    e <- M.replace_evar_type (B:= Vec 0) e (match meq_sym (slow_is_0 23) in _ =m= X return Vec X =m= Vec 0 with |meq_refl => meq_refl end);
                    M.cumul_or_fail UniCoq e vnil;;
                    M.ret tt).
End Test.
