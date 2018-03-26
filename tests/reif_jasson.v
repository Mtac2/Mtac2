Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Set Implicit Arguments.
Reserved Notation "'dlet' x .. y := v 'in' f"
         (at level 200, x binder, y binder, f at level 200, format "'dlet'  x .. y  :=  v  'in' '//' f").
Reserved Notation "'nllet' x .. y := v 'in' f"
         (at level 200, x binder, y binder, f at level 200, format "'nllet'  x .. y  :=  v  'in' '//' f").
Reserved Notation "'elet' x := v 'in' f"
         (at level 200, f at level 200, format "'elet'  x  :=  v  'in' '//' f").
Definition Let_In {A P} (v : A) (f : forall x : A, P x) : P v
  := let x := v in f x.
Notation "'dlet' x .. y := v 'in' f" := (Let_In v (fun x => .. (fun y => f) .. )).
Definition Let_In_nat : nat -> (nat -> nat) -> nat
  := (@Let_In nat (fun _ => nat)).
Definition key : unit. exact tt. Qed.
Definition lock {A} (v : A) : A := match key with tt => v end.
Lemma unlock {A} (v : A) : lock v = v.
Proof. unfold lock; destruct key; reflexivity. Qed.
Definition LockedLet_In_nat : nat -> (nat -> nat) -> nat
  := lock Let_In_nat.
Definition locked_nat_mul := lock Nat.mul.
Notation "'nllet' x .. y := v 'in' f"
  := (LockedLet_In_nat v (fun x => .. (fun y => f) .. )).
Definition lock_Let_In_nat : @Let_In nat (fun _ => nat) = LockedLet_In_nat
  := eq_sym (unlock _).
Definition lock_Nat_mul : Nat.mul = locked_nat_mul
  := eq_sym (unlock _).


Module Import PHOAS.
  Inductive expr {var : Type} : Type :=
  | NatO : expr
  | NatS : expr -> expr
  | LetIn (v : expr) (f : var -> expr)
  | Var (v : var)
  | NatMul (x y : expr).

  Bind Scope expr_scope with expr.
  Delimit Scope expr_scope with expr.

  Infix "*" := NatMul : expr_scope.
  Notation "'elet' x := v 'in' f" := (LetIn v (fun x => f%expr)) : expr_scope.
  Notation "$$ x" := (Var x) (at level 9, format "$$ x") : expr_scope.

  Fixpoint denote (e : @expr nat) : nat
    := match e with
       | NatO => O
       | NatS x => S (denote x)
       | LetIn v f => dlet x := denote v in denote (f x)
       | Var v => v
       | NatMul x y => denote x * denote y
       end.

  Definition Expr := forall var, @expr var.
  Definition Denote (e : Expr) := denote (e _).
End PHOAS.

(* cf COQBUG(https://github.com/coq/coq/issues/5448), COQBUG(https://github.com/coq/coq/issues/6315) *)
Ltac refresh n :=
  let n' := fresh n in
  let n' := fresh n in
  n'.

Ltac Reify_of reify x :=
  constr:(fun var : Type => ltac:(let v := reify var x in exact v)).

Ltac error_cant_elim_deps f :=
  let __ := match goal with
            | _ => idtac "Failed to eliminate functional dependencies in" f
            end in
  constr:(I : I).

Ltac error_bad_function f :=
  let __ := match goal with
            | _ => idtac "Bad let-in function" f
            end in
  constr:(I : I).

Ltac error_bad_term term :=
  let __ := match goal with
            | _ => idtac "Unrecognized term:" term
            end in
  let ret := constr:(term : I) in
  constr:(I : I).

(** Take care of initial locking of mul, letin, etc. *)
Ltac make_pre_Reify_rhs nat_of untag do_lock_letin do_lock_natmul :=
  let RHS := lazymatch goal with |- _ = ?RHS => RHS end in
  let e := fresh "e" in
  let T := fresh in
  evar (T : Type);
  evar (e : T);
  subst T;
  cut (untag (nat_of e) = RHS);
  [ subst e
  | lazymatch do_lock_letin with
    | true => rewrite ?lock_Let_In_nat
    | false => idtac
    end;
    lazymatch do_lock_natmul with
    | true => rewrite ?lock_Nat_mul
    | false => idtac
    end;
    cbv [e]; clear e ].

Fixpoint big (a : nat) (sz : nat) : nat
  := match sz with
     | O => a
     | S sz' => dlet a' := a * a in big a' sz'
     end.

Definition big_flat_op {T} (op : T -> T -> T) (a : T) (sz : nat) : T
  := Eval cbv [Z_of_nat Pos.of_succ_nat Pos.iter_op Pos.succ] in
      match Z_of_nat sz with
      | Z0 => a
      | Zpos p => Pos.iter_op op p a
      | Zneg p => a
      end.
Definition big_flat (a : nat) (sz : nat) : nat
  := big_flat_op Nat.mul a sz.

Module CanonicalStructuresPHOAS.
  (** * Canonical-structure based reification to [@expr nat], with let-binders *)

  Local Notation context := (list nat).

  Structure tagged_nat (ctx : context) := tag { untag :> nat }.

  Structure reified_of (ctx : context) :=
    reify { nat_of : tagged_nat ctx ; reified_nat_of :> forall var, list var -> (forall T, T) -> @expr var }.

  Definition var_tl_tag := tag.
  Definition var_hd_tag := var_tl_tag.
  Definition S_tag := var_hd_tag.
  Definition O_tag := S_tag.
  Definition mul_tag := O_tag.

  (** N.B. [Canonical] structures follow [Import], so they must be
    imported for reification to work. *)
  Module Export Exports.
    Canonical Structure letin_tag ctx n := mul_tag ctx n.

    Canonical Structure reify_O ctx
      := reify (O_tag ctx 0) (fun var _ _ => @NatO var).
    Canonical Structure reify_S ctx x
      := reify (@S_tag ctx (S (@nat_of ctx x))) (fun var vs phantom => @NatS var (x var vs phantom)).
    Canonical Structure reify_mul ctx x y
      := reify (@mul_tag ctx (@nat_of ctx x * @nat_of ctx y))
               (fun var vs phantom => @NatMul var (x var vs phantom) (y var vs phantom)).
    Canonical Structure reify_var_hd n ctx
      := reify (var_hd_tag (n :: ctx) n)
               (fun var vs phantom => @Var var (List.hd (phantom _) vs)).
    Canonical Structure reify_var_tl n ctx x
      := reify (var_tl_tag (n :: ctx) (@nat_of ctx x))
               (fun var vs phantom => reified_nat_of x (List.tl vs) phantom).
    Canonical Structure reify_letin ctx v f
      := reify (letin_tag ctx (nllet x := @nat_of ctx v in @nat_of (x :: ctx) (f x)))
               (fun var vs phantom => elet x := reified_nat_of v vs phantom in reified_nat_of (f (phantom _)) (x :: vs) phantom)%expr.
  End Exports.

  Definition ReifiedNatOf (e : reified_of nil) : (forall T, T) -> Expr
    := fun phantom var => reified_nat_of e nil phantom.

  Ltac pre_Reify_rhs _ := make_pre_Reify_rhs (@nat_of nil) (@untag nil) true false.
End CanonicalStructuresPHOAS.
Export CanonicalStructuresPHOAS.Exports.

Module LtacTacInTermExplicitCtx.
  Module var_context.
    Inductive var_context {var : Type} := nil | cons (n : nat) (v : var) (xs : var_context).
  End var_context.

  Ltac reify_helper var term ctx :=
    let reify_rec term := reify_helper var term ctx in
    lazymatch ctx with
    | context[var_context.cons term ?v _]
      => constr:(@Var var v)
    | _
      =>
      lazymatch term with
      | O => constr:(@NatO var)
      | S ?x
        => let rx := reify_rec x in
           constr:(@NatS var rx)
      | ?x * ?y
        => let rx := reify_rec x in
           let ry := reify_rec y in
           constr:(@NatMul var rx ry)
      | (dlet x := ?v in ?f)
        => let rv := reify_rec v in
           let not_x := refresh x in
           let not_x2 := refresh not_x in
           let not_x3 := refresh not_x2 in
           let rf
               :=
               lazymatch
                 constr:(
                   fun (x : nat) (not_x : var)
                   => match f, @var_context.cons var x not_x ctx return @expr var with (* c.f. COQBUG(https://github.com/coq/coq/issues/6252#issuecomment-347041995) for [return] *)
                      | not_x2, not_x3
                        => ltac:(let fx := (eval cbv delta [not_x2] in not_x2) in
                                 let ctx := (eval cbv delta [not_x3] in not_x3) in
                                 clear not_x2 not_x3;
                                 let rf := reify_helper var fx ctx in
                                 exact rf)
                      end)
               with
               | fun _ => ?f => f
               | ?f => error_cant_elim_deps f
               end in
           constr:(@LetIn var rv rf)
      | ?v
        => error_bad_term v
      end
    end.

  Ltac reify var x :=
    reify_helper var x (@var_context.nil var).
  Ltac Reify x := Reify_of reify x.
End LtacTacInTermExplicitCtx.

(*
Require Ltac2.Ltac2.
Module Import Ltac2Common.
  Import Ltac2.Init.
  Import Ltac2.Notations.

  Module List.
    Ltac2 rec map f ls :=
      match ls with
      | [] => []
      | l :: ls => f l :: map f ls
      end.
  End List.
  Module Ident.
    Ltac2 rec find_error id xs :=
      match xs with
      | [] => None
      | x :: xs
        => let ((id', val)) := x in
           match Ident.equal id id' with
           | true => Some val
           | false => find_error id xs
           end
      end.
    Ltac2 find id xs :=
      match find_error id xs with
      | None => Control.zero Not_found
      | Some val => val
      end.
  End Ident.
  Module Array.
    Ltac2 rec to_list_aux (ls : 'a array) (start : int) :=
      match Int.equal (Int.compare start (Array.length ls)) -1 with
      | true => Array.get ls start :: to_list_aux ls (Int.mul start 1)
      | false => []
      end.
    Ltac2 to_list (ls : 'a array) := to_list_aux ls 0.
  End Array.
  Module Constr.
    Ltac2 rec strip_casts term :=
      match Constr.Unsafe.kind term with
      | Constr.Unsafe.Cast term' _ _ => strip_casts term'
      | _ => term
      end.
    Module Unsafe.
      Ltac2 beta1 (c : constr) :=
        match Constr.Unsafe.kind c with
        | Constr.Unsafe.App f args
          => match Constr.Unsafe.kind f with
             | Constr.Unsafe.Lambda id ty f
               => Constr.Unsafe.substnl (Array.to_list args) 0 f
             | _ => c
             end
        | _ => c
        end.
      Ltac2 zeta1 (c : constr) :=
        match Constr.Unsafe.kind c with
        | Constr.Unsafe.LetIn id v ty f
          => Constr.Unsafe.substnl [v] 0 f
        | _ => c
        end.
    End Unsafe.
  End Constr.
  Module Ltac1.
    Class Ltac1Result {T} (v : T) := {}.
    Class Ltac1Results {T} (v : list T) := {}.
    Class Ltac2Result {T} (v : T) := {}.
    Ltac save_ltac1_result v :=
      match goal with
      | _ => assert (Ltac1Result v) by constructor
      end.
    Ltac clear_ltac1_results _ :=
      match goal with
      | _ => repeat match goal with
                    | [ H : Ltac1Result _ |- _ ] => clear H
                    end
      end.
    Ltac2 get_ltac1_result () :=
      (lazy_match! goal with
      | [ id : Ltac1Result ?v |- _ ]
        => Std.clear [id]; v
       end).

    Ltac save_ltac1_results v :=
      match goal with
      | _ => assert (Ltac1Result v) by constructor
      end.
    Ltac2 save_ltac2_result v :=
      Std.cut '(Ltac2Result $v);
        Control.dispatch
          [(fun ()
            => Std.intros false [Std.IntroNaming (Std.IntroFresh @res)])
           ;
           (fun () => Notations.constructor)].
    Ltac get_ltac2_result _ :=
      lazymatch goal with
      | [ res : Ltac2Result ?v |- _ ]
        => let __ := match goal with
                     | _ => clear res
                     end in
           v
      end.
    Ltac2 from_ltac1 (save_args : constr) (tac : unit -> unit) :=
      let beta_flag :=
          {
            Std.rBeta := true; Std.rMatch := false; Std.rFix := false; Std.rCofix := false;
            Std.rZeta := false; Std.rDelta := false; Std.rConst := [];
          } in
      let c := '(ltac2:(save_ltac2_result save_args;
                          tac ();
                          let v := get_ltac1_result () in
                          Control.refine (fun () => v))) in
      Constr.Unsafe.zeta1 (Constr.Unsafe.zeta1 (Std.eval_cbv beta_flag c)).
  End Ltac1.
End Ltac2Common.

Module Ltac2LowLevel.
  Import Ltac2.Init.
  Import Ltac2.Notations.

  Ltac2 rec unsafe_reify_helper
        (mkVar : constr -> 'a)
        (mkO : 'a)
        (mkS : 'a -> 'a)
        (mkNatMul : 'a -> 'a -> 'a)
        (mkLetIn : 'a -> ident option -> constr -> 'a -> 'a)
        (gO : constr)
        (gS : constr)
        (gNatMul : constr)
        (gLetIn : constr)
        (unrecognized : constr -> 'a)
        (term : constr)
    :=
      let reify_rec term := unsafe_reify_helper mkVar mkO mkS mkNatMul mkLetIn gO gS gNatMul gLetIn unrecognized term in
      let kterm := Constr.Unsafe.kind term in
      match Constr.equal term gO with
      | true
        => mkO
      | false
        =>
        match kterm with
        | Constr.Unsafe.Rel _ => mkVar term
        | Constr.Unsafe.Var _ => mkVar term
        | Constr.Unsafe.Cast term _ _ => reify_rec term
        | Constr.Unsafe.App f args
          =>
          match Constr.equal f gS with
          | true
            => let x := Array.get args 0 in
               let rx := reify_rec x in
               mkS rx
          | false
            =>
            match Constr.equal f gNatMul with
            | true
              => let x := Array.get args 0 in
                 let y := Array.get args 1 in
                 let rx := reify_rec x in
                 let ry := reify_rec y in
                 mkNatMul rx ry
            | false
              =>
              match Constr.equal f gLetIn with
              | true
                => let x := Array.get args 2 (* assume the first two args are type params *) in
                   let f := Array.get args 3 in
                   match Constr.Unsafe.kind f with
                   | Constr.Unsafe.Lambda idx ty body
                     => let rx := reify_rec x in
                        let rf := reify_rec body in
                        mkLetIn rx idx ty rf
                   | _ => unrecognized term
                   end
              | false
                => unrecognized term
              end
            end
          end
        | _
          => unrecognized term
        end
      end.

  Ltac2 unsafe_reify (var : constr) (term : constr) :=
    let cVar := '@Var in
    let cO := '@NatO in
    let cS := '@NatS in
    let cNatMul := '@NatMul in
    let cLetIn := '@LetIn in
    let gO := 'O in
    let gS := 'S in
    let gNatMul := '@Nat.mul in
    let gLetIn := '@Let_In in
    let mk0VarArgs :=
        let args := Array.make 1 var in
        args in
    let mk1VarArgs (x : constr) :=
        let args := Array.make 2 var in
        let () := Array.set args 1 x in
        args in
    let mk2VarArgs (x : constr) (y : constr) :=
        let args := Array.make 3 var in
        let () := Array.set args 1 x in
        let () := Array.set args 2 y in
        args in
    let mkApp0 (f : constr) :=
        Constr.Unsafe.make (Constr.Unsafe.App f mk0VarArgs) in
    let mkApp1 (f : constr) (x : constr) :=
        Constr.Unsafe.make (Constr.Unsafe.App f (mk1VarArgs x)) in
    let mkApp2 (f : constr) (x : constr) (y : constr) :=
        Constr.Unsafe.make (Constr.Unsafe.App f (mk2VarArgs x y)) in
    let mkVar (v : constr) := mkApp1 cVar v in
    let mkO := mkApp0 cO in
    let mkS (v : constr) := mkApp1 cS v in
    let mkNatMul (x : constr) (y : constr) := mkApp2 cNatMul x y in
    let mkcLetIn (x : constr) (y : constr) := mkApp2 cLetIn x y in
    let mkLetIn (x : constr) (idx : ident option) (ty : constr) (fbody : constr)
        := mkcLetIn x (Constr.Unsafe.make (Constr.Unsafe.Lambda idx var fbody)) in
    let ret := unsafe_reify_helper mkVar mkO mkS mkNatMul mkLetIn gO gS gNatMul gLetIn (fun term => term) term in
    ret.
  Ltac2 check_result (ret : constr) :=
    match Constr.Unsafe.check ret with
    | Val rterm => rterm
    | Err exn => Control.zero exn
    end.
  Ltac2 reify (var : constr) (term : constr) :=
    check_result (unsafe_reify var term).

  Ltac2 unsafe_Reify (term : constr) :=
    let fresh_set := Fresh.Free.of_constr term in
    let idvar := Fresh.fresh fresh_set @var in
    let var := Constr.Unsafe.make (Constr.Unsafe.Var idvar) in
    let rterm := unsafe_reify var term in
    let rterm := Constr.Unsafe.closenl [idvar] 1 rterm in
    Constr.Unsafe.make (Constr.Unsafe.Lambda (Some idvar) 'Type rterm).

  Ltac2 do_Reify (term : constr) :=
    check_result (unsafe_Reify term).

  Ltac2 unsafe_mkApp1 (f : constr) (x : constr) :=
    let args := Array.make 1 x in
    Constr.Unsafe.make (Constr.Unsafe.App f args).
  Ltac2 mkApp1 (f : constr) (x : constr) :=
    check_result (unsafe_mkApp1 f x).

  Ltac2 all_flags :=
    {
      Std.rBeta := true; Std.rMatch := true; Std.rFix := true; Std.rCofix := true;
      Std.rZeta := true; Std.rDelta := true; Std.rConst := [];
    }.
  Ltac2 betaiota_flags :=
    {
      Std.rBeta := true; Std.rMatch := true; Std.rFix := true; Std.rCofix := true;
      Std.rZeta := false; Std.rDelta := false; Std.rConst := [];
    }.
  Ltac2 in_goal :=
    { Std.on_hyps := None; Std.on_concl := Std.AllOccurrences }.

  Ltac2 do_Reify_rhs_fast () :=
    let g := Control.goal () in
    match Constr.Unsafe.kind g with
    | Constr.Unsafe.App f args (* App eq [ty; lhs; rhs] *)
      => let v := Array.get args 2 in
         let rv := Control.time (Some "actual reif") (fun _ => unsafe_Reify v) in
         let rv := Control.time (Some "eval lazy") (fun _ => Std.eval_lazy all_flags rv) in
         Control.time (Some "lazy beta iota") (fun _ => Std.lazy betaiota_flags in_goal);
           Control.time (Some "transitivity (Denote rv)") (fun _ => Std.transitivity (unsafe_mkApp1 'Denote rv))
    | _
      => Control.zero (Tactic_failure (Some (Message.concat (Message.of_string "Invalid goal in Ltac2Unsafe.do_Reify_rhs_fast: ") (Message.of_constr g))))
    end.

  Ltac2 do_Reify_rhs () :=
    lazy_match! goal with
  | [ |- _ = ?v ]
    => let rv := do_Reify v in
       let rv := Std.eval_lazy all_flags rv in
       Std.transitivity (mkApp1 'Denote rv)
  | [ |- ?g ] => Control.zero (Tactic_failure (Some (Message.concat (Message.of_string "Invalid goal in Ltac2Unsafe.do_Reify_rhs: ") (Message.of_constr g))))
  end.

  Ltac reify var term :=
    let __ := Ltac1.save_ltac1_result (var, term) in
    let ret :=
        constr:(ltac2:(let args := Ltac1.get_ltac1_result () in
                       (lazy_match! args with
                       | (?var, ?term)
                         => let rv := reify var term in
                            Control.refine (fun () => rv)
                       | _ => Control.throw Not_found
                        end))) in
    let __ := Ltac1.clear_ltac1_results () in
    ret.

  Ltac Reify x := Reify_of reify x.
  (*Ltac do_Reify_rhs _ := do_Reify_rhs_of Reify ().*)
  Ltac do_Reify_rhs _ := ltac2:(do_Reify_rhs_fast ()).
End Ltac2LowLevel.
*)

Require Mtac2.Mtac2.

Module Mtac2Mmatch.
  Import Mtac2.Mtac2.
  Import M.notations.

  Module var_context.
    Inductive var_context {var : Type} := nil | cons (n : nat) (v : var) (xs : var_context).
  End var_context.

  Definition find_in_ctx {var : Type} (term : nat) (ctx : @var_context.var_context var) : M (option var)
    := (mfix1 find_in_ctx (ctx : @var_context.var_context var) : M (option var) :=
          (mmatch ctx with
          | [? v xs] (var_context.cons term v xs)
            =n> M.ret (Some v)
          | [? x v xs] (var_context.cons x v xs)
            =n> find_in_ctx xs
          | _ => M.ret None
           end)) ctx.

   Definition reify_helper {var : Type} (term : nat) (ctx : @var_context.var_context var) : M (@expr var)
     := ((mfix2 reify_helper (term : nat) (ctx : @var_context.var_context var) : M (@expr var) :=
            lvar <- find_in_ctx term ctx;
              match lvar with
              | Some v => M.ret (@Var var v)
              | None =>
                 mmatch term with
                 | O
                   =n> M.ret (@NatO var)
                 | [? x] (S x)
                   =n> (rx <- reify_helper x ctx;
                          M.ret (@NatS var rx))
                 | [? x y] (x * y)
                   =n> (rx <- reify_helper x ctx;
                          ry <- reify_helper y ctx;
                          M.ret (@NatMul var rx ry))
                  | [? v f] (@Let_In nat (fun _ => nat) v f)
                    =n> (rv <- reify_helper v ctx;
                        x <- M.fresh_binder_name f;
                        let vx := String.append "var_" x in
                        rf <- (M.nu x mNone
                                    (fun x : nat
                                     => M.nu vx mNone
                                             (fun vx : var
                                              => let fx := reduce (RedWhd [rl:RedBeta]) (f x) in
                                                 rf <- reify_helper fx (var_context.cons x vx ctx);
                                                   M.abs_fun vx rf)));
                          M.ret (@LetIn var rv rf))
                end
             end) term ctx).

  Definition reify (var : Type) (term : nat) : M (@expr var)
    := reify_helper term var_context.nil.

  Definition Reify (term : nat) : M Expr
    := \nu var:Type, r <- reify var term; M.abs_fun var r.


  Ltac Reify' x := constr:(ltac:(mrun (@Reify x))).
  Ltac Reify x := Reify' x.

End Mtac2Mmatch.

Module MTac2.
  Import Mtac2.Mtac2.
  Import M.notations.

  Module var_context.
    Inductive var_context {var : Type} := nil | cons (n : nat) (v : var) (xs : var_context).
  End var_context.

  Fixpoint find_in_ctx {var : Type} (term : nat) (ctx : @var_context.var_context var) {struct ctx} : M (option var)
    := match ctx with
        | var_context.cons term' v xs =>
          mif M.unify term term' UniMatchNoRed then
            M.ret (Some v)
          else
            find_in_ctx term xs
        | _ => M.ret None
       end.

  Definition mor {A} (t1 t2 : M A) : M A :=
    mtry t1 with _ => t2 end.
  Notation "a '_or_' b" := (mor a b)  (at level 50).
Require Import Mtac2.DecomposeApp.
Import M.notations.
  Definition reify_helper {var : Type} (term : nat) (ctx : @var_context.var_context var) : M (@expr var)
    := ((mfix2 reify_helper (term : nat) (ctx : @var_context.var_context var) : M (@expr var) :=
           lvar <- find_in_ctx term ctx;
             match lvar with
             | Some v => M.ret (@Var var v)
             | None
               =>
               <[decapp term with O]> UniMatchNoRed (M.ret (@NatO var)) _or_
               <[decapp term with S]> UniMatchNoRed (fun x:nat=>
                  rx <- reify_helper x ctx;
                  M.ret (@NatS var rx)) _or_
               <[decapp term with Nat.mul]> UniMatchNoRed (fun x y:nat=>
                  rx <- reify_helper x ctx;
                  ry <- reify_helper y ctx;
                  M.ret (@NatMul var rx ry)) _or_
               <[decapp term with @Let_In nat (fun _=>nat)]> UniMatchNoRed (fun v f=>
                  rv <- reify_helper v ctx;
                  x <- M.fresh_binder_name f;
                  let vx := String.append "var_" x in
                  rf <- (M.nu x mNone
                              (fun x : nat
                               => M.nu vx mNone
                                       (fun vx : var
                                        => let fx := reduce (RedWhd [rl:RedBeta]) (f x) in
                                           rf <- reify_helper fx (var_context.cons x vx ctx);
                                             M.abs_fun vx rf)));
                  M.ret (@LetIn var rv rf))
             end) term ctx).

  Definition reify (var : Type) (term : nat) : M (@expr var)
    := reify_helper term var_context.nil.

  Definition Reify (term : nat) : M Expr
    := \nu var:Type, r <- reify var term; M.abs_fun var r.


  Ltac Reify' x := constr:(ltac:(mrun (@Reify x))).
  Ltac Reify x := Reify' x.
End MTac2.
