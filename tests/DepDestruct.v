From Mtac2
Require Import Datatypes List Mtac2 DepDestruct.
Import T.
Import Mtac2.List.ListNotations.

Goal forall n, 0 <= n.
MProof.
intros n.
new_destruct n.
Abort.

Section Bugs.

(** BUG: It fails with one constructor types, but not with two *)
Inductive one_constr : Prop :=
| the_one_constr : one_constr
.

Goal one_constr -> True.
MProof.
intros t.
new_destruct t.
Abort.

Inductive two_constrs : Prop :=
| first_constr : two_constrs
| second_constr : two_constrs
.

Goal two_constrs -> True.
MProof.
intros t.
new_destruct t.
- trivial.
- trivial.
Qed.
Unset Unicoq Debug.

End Bugs.

(* The 2nd new_destruct used to fail. *)
Goal forall n, n = S n -> False.
MProof.
  intros n H.
  Fail new_destruct H. (* fine, all indices need to be var *)
  pose (j := S n).
  assert (eq : j = S n) |1> reflexivity.
  move_back H (rewrite <- eq).
  intro H. (* now H has only indices *)
  move_back eq (idtac).
  new_destruct H.
Abort.


Section ExampleReflect.

  Inductive reflect (P :Prop) : bool -> Type :=
  | RTrue : P -> reflect P true
  | RFalse : ~P -> reflect P false.

Goal forall P b, reflect P b -> P <-> b = true.
MProof.
  intros P b r.
  new_destruct r.
  - intro xP &> split &> [m:reflexivity | intros &> assumption].
  - intro nxP &> split &> [m:intros &> contradiction | intros &> discriminate].
Qed.

  Example reflect_reflect P : ITele (SType) := iTele (fun b=>@iBase SType (reflect P b)).

  Example reflect_RTrue P : CTele (reflect_reflect P) :=
    (cProd (fun p=>@cBase SType _ (aTele _ (aBase)) (RTrue P p))).

  Example reflect_RFalse P : CTele (reflect_reflect P) :=
    (cProd (fun p=>@cBase SType _ (aTele _ (aBase)) (RFalse P p))).

  Example reflect_args P b : ATele (reflect_reflect P) :=
    aTele b aBase.

  Example bla P : RTele SProp (reflect_reflect P) :=
    Eval simpl in (fun b=>(fun _=>P <-> b = true)).
  Example bla_branch P := Eval simpl in get_type_of_branch (bla P) (reflect_RTrue P).


  Example bla_RTele P b (r : reflect P b) : RTele _ _ :=
    Eval compute in M.eval (abstract_goal (rsort := SProp) (reflect_args P b) ((P <-> b = true)) r).

  Example bla_goals P b r : list dyn :=
    Eval compute in
      map (fun cs => Dyn (get_type_of_branch (rsort := SProp) (bla_RTele P b r) cs))
          (reflect_RTrue P :: reflect_RFalse P :: nil).

  Example reflectP_it : ITele _ :=
    iTele (fun P => iTele (fun b => iBase (sort := SType) (reflect P b))).
  Program Example reflectP_RTrue : CTele reflectP_it :=
    cProd (fun P => cProd (fun p => (cBase (aTele _ (aTele _ aBase)) (@RTrue P p)))).
  Program Example reflectP_RFalse : CTele reflectP_it :=
    cProd (fun P => cProd (fun np => (cBase (aTele _ (aTele _ aBase)) (@RFalse P np)))).
  Example reflectP_args P b : ATele reflectP_it :=
    aTele P (aTele b (aBase)).

  Example reflect_app P b := Eval compute in ITele_App (reflect_args P b).

  Example blaP_RTele P b r : RTele _ _ :=
    Eval compute in M.eval (abstract_goal (rsort := SProp) (reflectP_args P b) ((P <-> b = true)) r).

  Example blaP_goals P b r : list dyn :=
    Eval compute in
      map (fun cs => Dyn (get_type_of_branch (blaP_RTele P b r) cs))
          (reflectP_RFalse :: reflectP_RTrue :: nil).

  Goal True.
    MProof.
    (\tactic g =>
       r <- M.destcase (match 3 with 0 => true | S _ => false end);
       M.print_term r;;
                  cpose r (fun r=>idtac) g).
    (\tactic g=>
       let c := reduce RedHNF r in
       case <- M.makecase c;
       cpose case (fun y=>idtac) g) : tactic.
  Abort.

  Goal forall P b, reflect P b -> P <-> b = true.
  Proof.
    intros P b r.
    pose (rG := (M.eval (abstract_goal (rsort := SType) (reflect_args P b) (P <-> b = true) r)) : RTele _ _).
    cbn delta -[RTele] in rG.
    assert (T : get_type_of_branch rG (reflect_RTrue P)).
    { now firstorder. }
    assert (F : get_type_of_branch rG (reflect_RFalse P)).
    { compute. firstorder. now discriminate. }
    pose (mc :=
            M.makecase {|
                case_val := r;
                case_return := Dyn (RTele_Fun rG);
                case_branches := (Dyn T) :: (Dyn F) :: nil
              |}).
    compute in mc.
    pose (c := M.eval mc).
    unfold M.eval in c.
    exact (elem c).
  Qed.

Notation "'mpose' ( x := t )" := (r <- t; cpose r (fun x=>idtac))
  (at level 40, x at next level).

Fixpoint unfold_funs {A} (t: A) (n: nat) {struct n} : M A :=
  match n with
  | 0 => M.ret t
  | S n' =>
    mmatch A as A' return M A' with
    | [? B (fty : B -> Type)] forall x, fty x => [H]
      let t' := reduce RedSimpl match H in eq _ P return P with eq_refl => t end in (* we need to reduce this *)
      name <- M.fresh_name "A";
      M.nu name None (fun x=>
        r <- unfold_funs (t' x) n';
        abs x r)
    | [? A'] A' => [H]
      match H in eq _ P return M P with eq_refl => M.ret t end
    end
  end%MC.

(* MetaCoq version *)
Goal forall P b, reflect P b -> P <-> b = true.
MProof.
  intros P b r.
  mpose (rG := abstract_goal (rsort := SType) (reflect_args P b) (P <-> b = true) r).
  simpl.
  assert (T : get_type_of_branch rG (reflect_RTrue P)).
  { simpl. cintros x {- split&> [m:cintros xP {- reflexivity -} | cintros notP {- assumption -}] -}. (* it doesn't work if intros is put outside *) }
  assert (F : get_type_of_branch rG (reflect_RFalse P)).
  { simpl. intros. split. intros. select (~ _) (fun a=>select P (fun x=>exact (match a x with end))). intros;; discriminate. }
  mpose (return_type := unfold_funs (RTele_Fun rG) 5).
  pose (mc :=
          M.makecase {|
              case_val := r;
              case_return := Dyn (return_type);
              case_branches := (Dyn T) :: (Dyn F) :: nil
            |}).
  let mc := reduce RedNF mc in r <- mc; pose (c := r).
  clear mc.
  unfold_in (@get_type_of_branch) T. simpl_in T.
  unfold_in (@get_type_of_branch) F. simpl_in F.
  clear return_type.
  (* TODO: figure out why `unfold` above doesn't work anymore. *)
  (* clear rG. *)
  match c with
  | Dyn c => exact c
  end.
Abort.


End ExampleReflect.


Module VectorExample.
Require Import Vector.
Goal forall n (v : t nat n), n = Coq.Lists.List.length (to_list v).
Proof.
  pose (it := iTele (fun n => @iBase (SType) (t nat n))).
  pose (vnil := ((@cBase SType _ (aTele 0 aBase) (nil nat))) : CTele it).
  pose (vcons := (cProd (fun a => cProd (fun n => cProd (fun (v : t nat n) => (@cBase SType _ (aTele (S n) aBase) (cons _ a _ v)))))) : CTele it).
  fix f 2.
  intros n v.
  pose (a := (aTele n (aBase)) : ATele it).
  pose (rt := M.eval (abstract_goal (rsort := SProp) a (n = Coq.Lists.List.length (to_list v)) v)).
  simpl in vcons.
  cbn beta iota zeta delta -[RTele] in rt.
  assert (N : get_type_of_branch rt vnil).
  { now auto. }
  assert (C : get_type_of_branch rt vcons).
  { intros x k v'. hnf. simpl. f_equal. exact (f _ _). }
  pose (mc :=
          M.makecase {|
              case_val := v;
              case_return := Dyn (RTele_Fun rt);
              case_branches := [m:Dyn N | Dyn C]
            |}
       ).
  unfold rt in mc. simpl RTele_Fun in mc.
  (* pose (ma := (match v as v' in t _ k return k = length (to_list v') with *)
  (*              | nil _ => N *)
  (*              | cons _ a k v => C a k v *)
  (*              end)). *)
  (* pose (c' := eval (destcase ma)). *)
  (* unfold eval in c'. *)
  pose (c := M.eval mc).
  unfold M.eval in c.
  exact (elem c).
Qed.
End VectorExample.


Example get_reflect_ITele := Eval compute in ltac:(mrun (get_ITele (reflect True)))%MC.
Example reflect_nindx := Eval compute in let (n, _) := get_reflect_ITele in n.
Example reflect_sort := Eval compute in let (sort, _) := snd get_reflect_ITele in sort.
Example reflect_itele : ITele reflect_sort :=
  Eval compute in
  match snd get_reflect_ITele as pair return let (sort, _) := pair in ITele sort with
  | existT _ s it => it
  end.
