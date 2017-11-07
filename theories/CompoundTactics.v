From Mtac2 Require Import Base Tactics ImportedTactics List Logic.

Import M. Import M.notations.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Notation reduce_dyns := (reduce (RedStrong [rl:RedBeta; RedMatch; RedZeta;
           RedDeltaOnly [rl: Dyn elem; Dyn type; Dyn (@id);
                           Dyn case_return; Dyn case_val; Dyn case_branches;
                        Dyn case_ind]])).

Module Abstract.

Structure result A B x t := R { fu : A -> B; pf : t =m= fu x }.
Implicit Arguments R [A B x t].

Lemma abs_app
  (A : Type) (x : A) (A' : Type) r (t1 : A' -> type r) (t2 : A') (r1 : result x t1) (r2 : result x t2):
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
   forall (r : dyn) (b : bool) (P Q : type r),
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


Definition construct_case A (x: A) (loop: forall r: dyn, M (result x (elem r))) C :=
  let val := reduce_dyns C.(case_val) in
  let retrn := reduce_dyns C.(case_return) in
  name <- M.fresh_name "v";
  nu name mNone (fun v=>
    new_val <- loop (Dyn val);
    let (fuv, _) := new_val in
    let fuv := reduce (RedWhd [rl:RedBeta]) (fuv v) in
    new_branches <- M.map (fun b=>r <- loop b;
                                    let (fub, _) := r in
                                    let fub := reduce (RedWhd [rl:RedBeta]) (fub v) in
                                    ret (Dyn fub)) C.(case_branches);
    let new_case := reduce_dyns {| case_val := fuv; case_return := retrn; case_branches := new_branches |} in
    d <- makecase new_case;
    let (_, cas) := d in
    func <- abs_fun v cas;
    ret (Dyn func)).

Definition abstract A B (x : A) (t : B) :=
   (mfix1 loop (r : dyn) : M (result x (elem r)) :=
   let r := reduce_dyns r in
   print_term r;;
   b <- is_evar (elem r);
   if b then raise exception
   else
    mmatch r as r' return M (result x (elem r')) with
    | Dyn x =>
      ret (R id (meq_refl _))
    | [? A' (t1 : A' -> type r) t2] Dyn (t1 t2)  =u>
        r1 <- loop (Dyn t1);
        r2 <- loop (Dyn t2);
        ret (abs_app r1 r2)
    (* | [? b (P:type r) (Q:type r)] Dyn (match b with *)
    (*       | true => P *)
    (*       | false => Q *)
    (*       end) *)
    (*   =u> *)
    (*   b' <- loop (Dyn b); *)
    (*   P' <- loop (Dyn P); *)
    (*   Q' <- loop (Dyn Q); *)
    (*   ret (match_eq B b' P' Q') *)
    | [? P Q] Dyn (P -> Q) =u>
      P' <- loop (Dyn P);
      Q' <- loop (Dyn Q);
      ret (non_dep_eq P' Q')
    | [?z:dyn] z =>
      let def := R (fun _=>elem z) (meq_refl) : (result x (elem z)) in
      mtry
        let '@Dyn T e := z in
        C <- destcase e;
        cas <- construct_case loop C;
        mmatch cas with
        | [? el: A -> (type z)] Dyn el =c>
          eq <- coerce (meq_refl (elem z));
          ret (R (t:=elem z) el eq)
        | [? e] e => print "nope:";; print_term e;; ret def
        end
      with NotAMatchExp =>
        ret def
      end
    end) (Dyn t).
Set Printing Universes.
Set Printing All.
Print abstract.

Notation reduce_all := (reduce (RedStrong [rl:RedBeta; RedMatch; RedZeta;
           RedDeltaOnly [rl: Dyn elem; Dyn type; Dyn (@fu); Dyn (@id);
             Dyn (@abs_app); Dyn (@meq_rect_r); Dyn (@meq_rect); Dyn (@meq_sym); Dyn (@internal_meq_rew_r);
             Dyn (@match_eq); Dyn (@non_dep_eq)]])).

Lemma eq_fu (A : Type) (x y : A) (P : Type) (r : result x P) :
  x =m= y -> fu r y -> P.
Proof. elim r. intros f H1 H2. rewrite H1, H2. auto. Qed.

End Abstract.

Import Abstract.
Set Printing Universes.
Definition simple_rewrite A {x y : A} (p : x =m= y) : tactic := fun g=>
  match g with
  | @Goal gT _ =>
    gT <- M.cast gT;
    r <- @abstract A Type x gT;
      let reduced := reduce_all (fu r y) in
      newG <- evar reduced;
        T.exact (eq_fu (r:=r) p newG) g;;
                ret [m: (tt, Goal newG)]
  | _ => raise NotAGoal
  end.

Import T.notations.
Set Printing Universes.
Definition variabilize {A} (t: A) name : tactic :=
  gT <- T.goal_type;
  gT <- M.cast gT;
  r <- abstract t gT;
  T.cpose_base name t (fun x=>
    let reduced := reduce_all (fu r x) in
    T.change reduced).


Require Import Arith String.
Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Import T.
Theorem sillyfun1_odd : forall (n : nat),
     (sillyfun1 n = true ->
     oddb n = true) : Type .
MProof.
  intros n. unfold sillyfun1.
  variabilize (beq_nat n 3) "t".
  assert (Heqe3 : t = (n =? 3)) |1> T.reflexivity.
  move_back Heqe3.
  destruct t &> intro Heqe3.
Abort.
