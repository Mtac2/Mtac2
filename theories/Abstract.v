From Mtac2 Require Import Base Logic Datatypes.

Import M. Import M.notations.

Set Implicit Arguments.
Unset Strict Implicit.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

Structure result A B x t := R { fu : A -> B; pf : t =m= fu x }.
Implicit Arguments R [A B x t].


Notation reduce_dyns := (reduce (RedStrong [rl:RedBeta; RedMatch; RedZeta;
           RedDeltaOnly [rl: Dyn elemr; Dyn typer;
                           Dyn case_return; Dyn case_val; Dyn case_branches;
                        Dyn case_ind]])).

Lemma abs_app
  (A : Type) (x : A) (A' : Type) r (t1 : A' -> typer r) (t2 : A') (r1 : result x t1) (r2 : result x t2):
  result x (t1 t2).
Proof.
elim r1. intros f1 p1.
elim r2. intros f2 p2.
rewrite p1, p2.
exact (R (fun y=>f1 y (f2 y)) (meq_refl _)).
Defined.



Lemma match_eq :
   forall A B : Type,
   forall x : A,
   forall (r : dynr) (b : bool) (P Q : typer r),
   result x b ->
   result x P ->
   result x Q ->
   result x (if b then P else Q).
Proof.
intros A B x r b P Q r1 r2 r3.
elim r1; intros f1 b1.
elim r2; intros f2 b2.
elim r3; intros f3 b3.
rewrite b1, b2, b3.
exact (R (fun y=>if (f1 y) then (f2 y) else f3 y) (meq_refl _)).
Defined.

Implicit Arguments match_eq [A x r b P Q].

Definition non_dep_eq {A P Q} (x:A) (P' : result x P) (Q' : result x Q) :
  result x (P -> Q).
Proof.
  case P' as [fuP eqP]. case Q' as [fuQ eqQ].
  rewrite eqP, eqQ.
  refine (R (fun y=>fuP y -> fuQ y) meq_refl).
Defined.

Definition to_dynr (d: dyn) : M dynr := dcase d as e in ret (Dynr e).

Definition construct_case A (x: A) (loop: forall r: dynr, M (result x (elemr r))) C :=
  let 'mkCase _ val retrn branches := C in
  name <- M.fresh_name "v";
  nu name mNone (fun v=>
    new_val <- loop (Dynr val);
    let (fuv, _) := new_val in
    let fuv := reduce (RedWhd [rl:RedBeta]) (fuv v) in
    new_branches <- M.map (fun b=>
                            b <- to_dynr b;
                            r <- loop b;
                            let (fub, _) := r in
                            let fub := reduce (RedWhd [rl:RedBeta]) (fub v) in
                            ret (Dyn fub)) branches;
    let new_case := reduce_dyns {| case_val := fuv; case_return := retrn; case_branches := new_branches |} in
    d <- makecase new_case;
    dcase d as A0, cas in
    func <- abs_fun v cas;
    ret (@Dyn (A -> A0) func)).


Notation reduce_all := (reduce (RedStrong [rl:RedBeta; RedMatch; RedZeta;
           RedDeltaOnly [rl: Dyn elemr; Dyn typer; Dyn (@fu);
             Dyn (@abs_app); Dyn (@meq_rect_r); Dyn (@meq_rect); Dyn (@meq_sym); Dyn (@internal_meq_rew_r);
             Dyn (@match_eq); Dyn (@non_dep_eq)]])).

Definition abstract A B (x : A) (t : B) :=
   r <-
   (mfix1 loop (r : dynr) : M (result x (elemr r)) :=
   let r := reduce_dyns r in
   b <- is_evar (elemr r);
   if b then raise exception
   else
    mmatch r as r' return M (result x (elemr r')) with
    | Dynr x =n>
      ret (R (fun x=>x) (meq_refl _))
    (* | [? b (P:type r) (Q:type r)] Dyn (match b with *)
    (*       | true => P *)
    (*       | false => Q *)
    (*       end) *)
    (*   =u> *)
    (*   b' <- loop (Dyn b); *)
    (*   P' <- loop (Dyn P); *)
    (*   Q' <- loop (Dyn Q); *)
    (*   ret (match_eq B b' P' Q') *)
    | [? P Q] Dynr (P -> Q) =n>
      P' <- loop (Dynr P);
      Q' <- loop (Dynr Q);
      ret (non_dep_eq P' Q')
    | _ =n>
       let r' := dreduce (typer) (typer r) in
       mmatch r as r' return M (result x (elemr r')) with
       | [? A' (t1 : A' -> r') t2] Dynr (t1 t2)  =n>
           r1 <- loop (Dynr t1);
           r2 <- loop (Dynr t2);
           ret (abs_app r1 r2)
       | [? z] z =n>
         let def := R (fun _=>elemr z) (meq_refl) : (result x (elemr z)) in
         mtry
           let '@Dynr T e := z in
           C <- destcase e;
           cas <- construct_case loop C;
           mmatch cas with
           | [? el: A -> (typer z)] Dyn el =c>
             eq <- coerce (meq_refl (elemr z));
             ret (R (t:=elemr z) el eq)
           | [? e] e => print "nope:";; print_term e;; ret def
           end
         with NotAMatchExp =>
           ret def
         end
       end
    end) (Dynr t);
    let reduced := reduce_all r in
    ret reduced.

Lemma eq_fu (A : Type) (x y : A) (P : Type) (r : result x P) :
  x = y -> fu r y -> P.
Proof. elim r. intros f H1 H2. simpl. rewrite H1, H2. auto. Qed.
