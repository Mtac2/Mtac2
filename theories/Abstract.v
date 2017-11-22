From Mtac2 Require Import Base Logic.

Import M. Import M.notations.

Set Implicit Arguments.
Unset Strict Implicit.

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

Definition non_dep_eqS {A} {P Q:Set} (x:A) (P' : result x P) (Q' : result x Q) :
  result x (P -> Q).
Proof.
  case P' as [fuP eqP]. case Q' as [fuQ eqQ].
  rewrite eqP, eqQ.
  refine (R (fun y=>fuP y -> fuQ y) meq_refl).
Defined.

Definition non_dep_eqP {A} {P Q:Prop} (x:A) (P' : result x P) (Q' : result x Q) :
  result x (P -> Q).
Proof.
  case P' as [fuP eqP]. case Q' as [fuQ eqQ].
  rewrite eqP, eqQ.
  refine (R (fun y=>fuP y -> fuQ y) meq_refl).
Defined.



Lemma eq_fu (A : Type) (x y : A) (P : Type) (r : result x P) :
  x = y -> fu r y -> P.
Proof. elim r. intros f H1 H2. rewrite H1, H2. auto. Qed.

Notation reduce_all := (reduce (RedStrong [rl:RedBeta; RedMatch; RedZeta;
           RedDeltaOnly [rl: Dyn elem; Dyn type; Dyn (@fu);
             Dyn (@abs_app); Dyn (@meq_rect_r); Dyn (@meq_rect); Dyn (@meq_sym); Dyn (@internal_meq_rew_r);
             Dyn (@match_eq); Dyn (@non_dep_eq); Dyn (@non_dep_eqS)]])).

Definition abstract A B (x : A) (t : B) :=
   r <-
   (mfix1 loop (r : dyn) : M (result x (elem r)) :=
   b <- is_evar (elem r);
   if b then raise exception
   else
    mmatch r as r' return M (result x (elem r')) with
    | Dyn x =>
      ret (R (fun x=>x) (meq_refl _))
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
    (* | [? P Q:Prop] @Dyn Prop (P -> Q) =n> *)
    (*   P' <- loop (Dyn P); *)
    (*   Q' <- loop (Dyn Q); *)
    (*   ret (non_dep_eqP P' Q') *)
    | [? P Q:Set] @Dyn Set (P -> Q) =n>
      P' <- loop (Dyn P);
      Q' <- loop (Dyn Q);
      ret (non_dep_eqS P' Q')
    (* | [? P Q] Dyn (P -> Q) =n> *)
    (*   P' <- loop (Dyn P); *)
    (*   Q' <- loop (Dyn Q); *)
    (*   ret (non_dep_eq P' Q') *)
    | [?z] z =>
      ret (R (fun _=>elem z) (meq_refl _))
    end) (Dyn t);
    let reduced := reduce_all r in
    ret reduced.

Require Import Vectors.Fin.
Set Printing All.
Fail Definition test := fun x => ltac:(mrun (a <- abstract (x+1) (Fin.t (x+1) -> unit); let t:= dreduce (fu) (fu a) in ret t)).