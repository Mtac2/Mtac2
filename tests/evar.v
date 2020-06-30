From Mtac2 Require Import Mtac2.
Close Scope tactic_scope.


(* Cyclic instantations are not allowed! *)
Fail Mtac Do (e <- M.evar unit; M.set_evar e (e :unit);; M.print_term e).

Mtac Do (e <- M.evar unit; M.unify e (tt : unit) UniCoq;; M.print_term e).

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

  Variable Vec : nat -> Type.
  Variable vnil : Vec 0.
  Variable vslow : forall n, Vec (slow n).

  (* Unification will reduce things very slowly *)
  Fail Timeout 1 Mtac Do (e <- M.evar (Vec (slow 23)); M.cumul_or_fail UniCoq e (vnil);; M.ret tt).
  Fail Timeout 1 Mtac Do (e <- M.evar (Vec 0); M.cumul_or_fail UniCoq e (vslow 23);; M.ret tt).
  (* Even when we statically know that the types match we still run into slow reduction. *)
  Fail Timeout 1 Mtac Do (e <- M.evar (Vec 0);
                         match meq_sym (slow_is_0 23) in _ =m= X return Vec X -> unit with
                         | meq_refl => fun e =>
                                         M.unify e (vslow 23) UniCoq;;
                                         M.ret tt
                         end
                         ).


  (* [replace_evar_type] can help *)
  Timeout 1 Mtac Do (e <- M.evar (Vec (slow 23));
                    e <- M.replace_evar_type (B:= Vec 0) e (match meq_sym (slow_is_0 23) in _ =m= X return Vec X =m= Vec 0 with |meq_refl => meq_refl end);
                    M.cumul_or_fail UniCoq e vnil;;
                    M.ret tt).

  (* With [set_evar] we don't even need to change the evar's type. It will also
     preserve casts and not attempt any unification whatsoever. *)
  Timeout 1 Mtac Do (e <- M.evar (Vec 0);
          match slow_is_0 23 in _ =m= X return Vec X -> M unit with
          | meq_refl =>
            fun e : Vec (slow 23) =>
              M.set_evar (A:=Vec (slow 23)) e (vslow 23);;
              M.ret tt
          end e
          ).
End Test.
