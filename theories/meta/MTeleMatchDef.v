From Mtac2 Require Import Base Logic Datatypes List MTele.
Import M.notations.
Import Sorts.S.
Import ListNotations.

Set Polymorphic Inductive Cumulativity.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.


Inductive mtpattern A (m : A -> Prop)  : Prop :=
| mtpbase : forall x : A, m x -> Unification -> mtpattern A m
| mtptele : forall {C}, (forall x : C, mtpattern A m) -> mtpattern A m
| mtpsort : (Sort -> mtpattern A m) -> mtpattern A m.


Arguments mtpbase {A m} _ _.
Arguments mtptele {A m C} _.
Arguments mtpsort {A m} _.


Local Notation MFA T := (MTele_val (MTele_C SType SProp M T)).

Polymorphic Definition mtmmatch' A m (T : forall x, MTele_Ty (m x)) (y : A)
           (ps : mlist (mtpattern A (fun x => MFA (T x)))) : selem_of (MFA (T y)) :=
  MTele_open
    M.t (T y)
    (fun R acc =>
       (fix mmatch' ps : M.t R :=
          match ps with
          | [m:] => M.raise NoPatternMatches
          | p :m: ps' =>
            (* M.print "dbg2";; *)
                    let g := (fix go p :=
                                (* M.print "inner";; *)
                                (* M.print_term p;; *)
                        match p return M.t _ with
                        | mtpbase x f u =>
                          (* M.print "mtpbase";; *)
                          oeq <- M.unify x y u;
                          match oeq return M.t R with
                          | mSome eq =>
                            (* eq has type x = t, but for the pattern we need t = x.
         we still want to provide eq_refl though, so we reduce it *)
                            let h := dreduce (meq_sym) (meq_sym eq) in
                            let 'meq_refl := eq in
                            (* For some reason, we need to return the beta-reduction of the pattern, or some tactic fails *)

                            (* M.print "dbg1";; *)
                            let f' := (match h in _ =m= z return MTele_ty M.t (T z) -> MTele_ty M.t (T y)
                                       with
                                       | meq_refl => fun f => f
                                       end f)
                            in
                            let a := acc _ f' in
                            let b := reduce (RedStrong [rl:RedBeta]) (a) in
                            (* b *)
                            b
                          | mNone =>
                            M.raise DoesNotMatch
                        end

                        | mtptele f =>
                          (* M.print "dbg3";; *)
                          c <- M.evar _;
                          go (f c)
                        | mtpsort f =>
                          M.mtry'
                            (go (f SProp))
                            (fun e =>
                              oeq <- M.unify e DoesNotMatch UniMatchNoRed;
                              match oeq with
                              | mSome _ => go (f SType)
                              | mNone => M.raise e
                              end
                            )
                        end
                     ) in
            (* M.print_term p;; *)
            let t := g p in
            M.mtry' t
                  (fun e =>
                     mif M.unify e DoesNotMatch UniMatchNoRed then mmatch' ps' else M.raise e)
            (* mtry' (open_mtpattern _ (fun _ => _)) *)
            (*       (fun e => *)
            (*          mif unify e DoesNotMatch UniMatchNoRed then mmatch' ps' else raise e) *)
          end) ps
    ).

Module TestFin.
Require Fin.
Polymorphic Definition mt : nat -> MTele := fun n => mTele (fun _ : Fin.t n => mBase).
Definition T : forall n, MTele_Ty (mt n) := fun n _ => True.
Definition pO u : mtpattern nat _ := @mtpbase _ (fun x => MTele_ty M (n:=mt x) (T x)) 0 ((* ex_intro _ 0 *) (fun x => Fin.case0 (fun _ => M True) x)) u.
Definition p1 u : mtpattern nat _ := @mtpbase _ (fun x => MTele_ty M (n:=mt x) (T x)) 1 ((* ex_intro _ 1 *) (fun n => M.ret I)) u.
Definition pi u : mtpattern nat (fun x => MTele_ty M (n:=mt x) (T x)) :=
  mtptele (fun i : nat =>
             @mtpbase _ _  i ((* ex_intro _ i *) (fun n => M.ret I)) u
          ).

Program Example pbeta : mtpattern nat (fun x => MTele_ty M (n:=mt x) (T x)) :=
  mtptele (fun i : nat =>
            @mtpbase _ (* (fun x => MTele_ty M (mt x)) *) _ (i+1) ((* ex_intro _ (i + 1) *) (fun n : Fin.t (i + 1) => M.ret I)) UniCoq
         ).
End TestFin.