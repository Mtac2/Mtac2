(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "." "Top" "-top" "bug_evar") -*- *)
(* File reduced by coq-bug-finder from original input, then from 433 lines to 278 lines, then from 294 lines to 278 lines *)
(* coqc version 8.6.1 (August 2017) compiled on Aug 22 2017 10:37:48 with OCaml 4.02.3
   coqtop version 8.6.1 (August 2017) *)
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Require Mtac2.Sorts.
Require Mtac2.Debugger.
Import Mtac2.Datatypes.
Import Mtac2.List Mtac2.Logic.
Import Mtac2.Sorts.
Import Mtac2.Tactics.
Import Sorts.
Import M.notations.
Import Mtac2.List.ListNotations.

Import M.
Fixpoint open_pattern {A P y} (p : pattern t A P y) : t (P y) :=
  match p with
  | pbase x f u =>
    oeq <- unify x y u;
    match oeq return t (P y) with
    | mSome eq =>
      let h := reduce (RedWhd [rl:RedBeta;RedDelta;RedMatch]) (meq_sym eq) in
      let 'meq_refl := eq in
      let b := reduce (RedWhd [rl:RedBeta]) (f h) in b
    | mNone => raise DoesNotMatch
    end
  | @ptele _ _ _ _ C f => e <- evar C; (* M.print_term f;; UNCOMMENTING THIS MAKES IT STACK OVERFLOW *) open_pattern (f e)
  end.

Fixpoint mmatch' {A P} (y : A) (ps : mlist (pattern t A P y)) : t (P y) :=
  match ps with
  | [m:] => raise NoPatternMatches
  | p :m: ps' =>
    mtry' (open_pattern p) (fun e =>
      mif unify e DoesNotMatch UniMatchNoRed then mmatch' y ps' else raise e)
  end.

  Notation "'mmatch' x ls" :=
    (@mmatch' _ (fun _ => _) x ls%with_pattern)
    (at level 200, ls at level 91) : M_scope.

Definition get_ITele : forall (T : Type) (ind : T), M (unit) :=
  mfix2 f (T : _) (ind : _) : M (unit)%type :=
    mmatch T with
    | [? (A : Type) (F : A -> Type)] forall a, F a => [H] let indFun := match H in _ =m= R return R with meq_refl => ind end in
                                                          M.ret tt
    end.


Definition Break : Exception. exact exception. Qed.

Require Import Strings.String.

Definition debug (trace: bool) {A:Type} (bks : mlist dyn) : M A -> M unit :=
  M.break (fun A (x:M A) =>
             v <- M.decompose x;
             let (hd, _) := v in
             let (_, hd) := hd : dyn in
               let x := reduce (RedWhd [rl:RedBeta;RedMatch;RedFix;RedZeta]) x in
               v <- M.decompose x;
               let (hd, _) := v in
               mif M.find (fun d=>M.cumul UniMatchNoRed d hd) bks then
                 M.print_term x;;
                 inp <- M.read_line;
                 match inp with
                 | "e"%string => M.raise Break
                 | _ => M.ret x
                 end
               else M.print_term x;; M.ret x).

Definition debugT {A} (trace: bool) (bks : mlist dyn) (t: gtactic A) : gtactic unit := fun g=>
  debug trace bks (t g) ;; M.ret [m:].

Goal unit.
MProof.
Set Printing All.
  (* No idea why this is failing horribly (just when debugging) *)
  (* debugT true [m:] (@get_ITele (nat -> Prop) (eq 0)). *)
Abort.
