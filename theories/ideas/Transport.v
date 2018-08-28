From Mtac2 Require Import Base Logic Datatypes List Sorts DepDestruct MTeleMatch.
Import Sorts.S.
Import M. Import M.notations. Import Mtac2.lib.List.ListNotations.
Import Mtac2.lib.Datatypes.ProdNotations.

Set Polymorphic Inductive Cumulativity.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Fixpoint combine {A B} (l : mlist A) (l' : mlist B) {struct l} : mlist (A *m B) :=
  match l with
  | mnil => mnil
  | (x :m: tl)%list => match l' with
                      | mnil => mnil
                      | (y :m: tl')%list => ((m: x, y) :m: combine tl tl')%list
                      end
  end.

Definition get_ind_cts (A : Type) (offset : nat) : M (nat * {s : Sort & { it : ITele s & mlist (NDCTele it)}}) :=
  ind <- get_ind A;
  let (nsortit, constrs) := ind in
  (* drop first `offset` constructors. *)
  let constrs := mskipn offset constrs in
  let (nindx, sortit) := nsortit in
  let (isort, it) := sortit in
  atele <- get_ind_atele it nindx A;
               (* Compute CTeles *)
  cts <- M.map (fun c_dyn : dyn =>
    dcase c_dyn as dtype, delem in
    let ty_c := reduce (RedWhd RedAll) (S.stype_of isort) in
    ty <- M.evar ty_c;
    b <- M.cumul UniMatchNoRed ty dtype;
    if b then
      let el_c := reduce (RedWhd RedAll) (S.selem_of ty) in
      el <- M.evar el_c;
      M.cumul UniMatchNoRed el delem;;
      get_NDCTele it nindx ty el
    else
      M.failwith "Couldn't unify the type of the inductive with the type of the constructor"
  ) constrs;
  M.ret (nindx, existT _ _ (existT _ _ cts)).

Local Notation lprod l := (mfold_right (fun T b => T *m b)%type unit l).

Definition Mnu {A B} (f : A -> M B) (n : name) : M B := (M.nu n mNone f).

Local Notation "\fnu x .. z , t" :=
  (M.nu Generate mNone (fun x => .. (M.nu Generate mNone (fun z => t)) ..))
(at level 101, x binder, z binder, right associativity) : M_scope.

Local Notation "'\sfnu' s 'for' x .. z , t" :=
(M.nu (FreshFromStr s) mNone (fun x => .. (M.nu (FreshFromStr s) mNone (fun z => t)) ..))
(at level 101, x binder, z binder).


Local Notation "\fnuf x .. z 'for' F , t" :=
(M.nu (FreshFrom F) mNone
      (fun x =>
         (* let F := reduce (RedWhd RedAll) F in *)
         ..(
             M.nu (FreshFrom F) mNone (fun z =>
                                         (* let F := reduce (RedWhd RedAll) F in *)
                                         t
                                      )
           )..
      )
)
  (at level 101, x binder, z binder).

Definition stype_type (sort : Sort) (t : stype_of sort) : Type := (selem_of t) : Type.

Definition gen_match_branch {T1 T2 X} (recursor : T1 -> M T2) (base : T2 -> M X) :=
  fix f (C1_types C2_types : mlist Type) :
    forall ndc : (NDCfold (@iBase SType T1) C1_types), (lprod C2_types -> M X) -> M (branch_of_NDCTele (rsort := SProp) (it := @iBase SType T1) (fun _ => M X) (existT _ C1_types ndc)) :=
    match C1_types as C1_types, C2_types as C2_types return
          forall ndc : (NDCfold (@iBase SType T1) C1_types), (lprod C2_types -> M X) -> M (branch_of_NDCTele (rsort := SProp) (it := @iBase SType T1) (fun _ => M X) (existT _ C1_types ndc))
    with
    | mnil, mnil =>
      fun (F1 : unit -> _) (F2 : unit -> _) =>
        let c2 := reduce RedVmCompute (F2 tt) in
        M.ret c2
    | X1:m:C1_types, X2:m:C2_types =>
      mtmmatch (m: X1, X2) as Xs return
          forall ndc : (NDCfold (@iBase SType T1) (mfst Xs:m:C1_types)),
            (lprod (msnd Xs:m:C2_types) -> M X) ->
            M (branch_of_NDCTele (rsort := SProp) (it := @iBase SType T1) (fun _ => M X) (existT _ (mfst Xs:m:C1_types) ndc))
        with
        | [? A : Type] (m: A, A) =u>
          fun (F1 : lprod (mfst (m: A,A):m:_) -> _) (F2 : lprod (msnd (m: A,A):m:_) -> M X)=>
            \fnuf a for F1,
            pat <- f C1_types C2_types (fun y=> F1 (m: a,y)) (fun lp => F2 (m: a,lp));
            M.abs_fun (P:=fun _ => _) a pat
        | (m: T1, T2) =u>
          fun (F1 : lprod (mfst (m:T1,T2):m:_) -> _) (F2 : lprod (msnd (m:T1,T2):m:_) -> M X) =>
            \fnuf a for F1,
            pat <- f C1_types C2_types (fun x=> F1 (m: a,x))
                (fun lp =>
                   b <- recursor a;
                   F2(m: b,lp));
            M.abs_fun (P:=fun _ => _) a pat
        end
    | _, _ => fun _ _ => M.failwith "Constructors have different arity."
    end.

Definition gen_match_from_to (T1 T2 : Type) X (offset : nat) : M (forall recursor : T1 -> M T2, forall base : T2 -> M X, T1 -> M X) :=
  i1 <- get_ind_cts T1 O;
  i2 <- get_ind_cts T2 offset;
  mmatch (m: i1, i2) with
  | [?(n1 : nat) (Cs1 : mlist (NDCTele (@iBase SType T1)))
      (n2 : nat) (Cs2 : mlist (NDCTele (@iBase SType T2)))]
      (m:
        ((n1, existT _ SType (existT _ (@iBase SType T1) Cs1))),
        ((n2, existT _ SType (existT _ (@iBase SType T2) Cs2)))
      ) =>
    let it1 := @iBase SType T1 in
    let it2 := @iBase SType T2 in
    (if Nat.eqb (mlength Cs1) (mlength Cs2) then M.ret unit else M.failwith "Number of remaining constructors of T2 does not match that of T1");;
    (* let Cs1 := reduce RedVmCompute Cs1 in *)
    (* let Cs2 := reduce RedVmCompute Cs2 in *)
    let zipped := combine Cs1 Cs2 in
    \sfnu "recursor" for recursor : T1 -> M T2,
    \sfnu "base"  for base : T2 -> M X,
    (* Construct MTele *)
    pats <- M.map
         (fun Csi =>
            let (Cs1_i, Cs2_i) := Csi : (NDCTele it1) *m NDCTele (it2) in
            (* M.print_term (Cs1_i, Cs2_i);; *)
            let c11 := reduce (RedVmCompute) (projT1 Cs1_i) in
            let c1 := reduce (RedVmCompute) (projT2 Cs1_i) in
            let c21 := reduce (RedVmCompute) (projT1 Cs2_i) in
            let c2 := reduce (RedVmCompute) (projT2 Cs2_i) in
            (* M.print_term c21;; *)
            t <-
              gen_match_branch recursor base
                               c11
                               c21
                               c1
                               (fun x => let '(existT _ _ y) := c2 x in base y);
            M.ret (Dyn t)
         )
         (zipped);
    (* M.print_term pats;; *)
    \sfnu "t1" for t1 : T1,
    c <- M.makecase (mkCase T1 t1 (Dyn (fun _ : T1 => M X)) (pats));
    dcase c as T, b in
    oeq <- M.unify (T) (M X) UniCoq;
    match oeq return (T) ->
                     M ((T1 -> M T2) -> (T2 -> M X) -> T1 -> M X) with
    | mSome eq =>
      match eq in _ =m= R return T ->
                               M ((T1 -> M T2) -> (T2 -> M X) -> T1 -> R) with
      | meq_refl => fun f =>
                     (* let f := reduce (RedWhd ([rl:RedMatch;RedBeta;RedDeltaOnly [rl:Dyn (@elem)]])) f in *)
                     (* let ty := reduce (RedWhd ([rl:RedMatch;RedBeta;RedDeltaOnly [rl:Dyn (@type)]])) T in *)
                     let ty := T in
                     (* M.print_term ty;; *)
                     f <- M.abs_fun (P:=fun _ => ty) t1 f;
                     f <- M.abs_fun base f;
                     f <- M.abs_fun recursor f;
                     M.ret (f)
      end
    | mNone => fun _  => M.failwith "Impossible branch."
    end b
end
.


Section Test.
  Inductive Rnat : Type :=
  | Rmult : Rnat -> Rnat -> Rnat
  | RO : Rnat
  | RS : Rnat -> Rnat.

  Set Printing Universes.
  Time Definition hl_expr_to_expr_coq {X : Type} : (nat -> M Rnat) -> (Rnat -> M X) -> nat -> M X :=
  fun f b => ltac:(mrun(
                         (gen_match_from_to nat Rnat X 1))
                    ) f b.
End Test.
