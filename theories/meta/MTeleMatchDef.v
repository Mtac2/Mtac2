From Mtac2 Require Import Base Logic Datatypes List MTele.
Import M.notations.
Import Sorts.S.
Import ListNotations.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.


Inductive mtpattern A (M : A -> Prop)  : Prop :=
| mtpbase : forall x : A, M x -> Unification -> mtpattern A M
| mtptele : forall {C}, (forall x : C, mtpattern A M) -> mtpattern A M
| mtpsort : (Sort -> mtpattern A M) -> mtpattern A M.


Arguments mtpbase {A M} _ _.
Arguments mtptele {A M C} _.
Arguments mtpsort {A M} _.


Local Notation MFA T := (MTele_val (MTele_C SType SProp M T)).

Fixpoint open_branch {A} {m} {T : forall x, MTele_Ty (m x)} {y : A} {a : ArgsOf (m y)}
         (p : mtpattern A (fun x => MFA (T x))) : M (apply_sort (T y) a) :=
  match p return M _ with
  | mtpbase x f u =>
    oeq <- M.unify x y u;
    match oeq return M (apply_sort (T y) a) with
    | mSome eq =>
      match eq in meq _ z return forall a : ArgsOf (m z), M (apply_sort (T z) a) with
      | meq_refl => apply_C SProp f
      end a
    | mNone => M.raise DoesNotMatch
    end
  | mtptele f => c <- M.evar _; open_branch (f c)
  | mtpsort f =>
    M.mtry'
      (open_branch (f SProp))
      (fun e =>
         oeq <- M.unify e DoesNotMatch UniMatchNoRed;
         match oeq with
         | mSome _ => open_branch (f SType)
         | mNone => M.raise e
         end
      )
  end
.

Definition mtmmatch' A m (T : forall x, MTele_Ty (m x)) (y : A)
           (ps : mlist (mtpattern A (fun x => MFA (T x)))) : selem_of (MFA (T y)) :=
  curry_C
    SProp
    (fun a : ArgsOf (m y) =>
       (fix mmatch' (ps : mlist (mtpattern A (fun x => MFA (T x)))) :=
          match ps with
          | [m:] => M.raise NoPatternMatches
          | p :m: ps' =>
            M.mtry' (open_branch p)
                    (fun e =>
                       mif M.unify e DoesNotMatch UniMatchNoRed then mmatch' ps' else M.raise e)
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