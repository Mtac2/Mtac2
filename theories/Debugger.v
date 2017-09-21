From Mtac2 Require Import List Mtac2.

Import M.notations.
Require Import Strings.String.

Definition Break : Exception. exact exception. Qed.

Definition isReduce {A} (x:A) : M bool :=
  mmatch x with
  | [? T r t1 t2] let x := reduce r t1 : T in t2 x => M.ret true
  | _ => M.ret false
  end.

Definition debug (trace: bool) {A:Type} (bks : list dyn) : M A -> M unit :=
  M.break (fun A (x:M A) =>
             v <- M.decompose x;
             let (hd, _) := v in
             let (_, hd) := hd : dyn in
             mif isReduce hd then (* avoid computation of reduce *)
               M.print_term x;;
               M.ret x
             else
               let x := reduce (RedWhd [rl:RedBeta;RedMatch;RedFix;RedZeta]) x in
               v <- M.decompose x;
               let (hd, _) := v in
               mif M.find (fun d=>M.unify_cumul d hd UniMatchNoRed) bks then
                 M.print_term x;;
                 inp <- M.read_line;
                 match inp with
                 | "e" => M.raise Break
                 | _ => M.ret x
                 end
               else if trace then
                      M.print_term x;; M.ret x
                    else M.ret x) _.

Definition debugT {A} (trace: bool) (bks : list dyn) (t: gtactic A) : gtactic unit := fun g=>
  debug trace bks (t g) ;; M.ret nil.
Import Mtac2.List.ListNotations.

Import M.notations.

Definition test : unit := ltac:(mrun (debug true [m:] (M.ret I))).


Goal True.
MProof.
  debugT false [m: (*HAVE FUN Dyn (@M.ret) | Dyn (@M.unify) *)] (T.apply I).
Qed.

Goal unit.
MProof.
  (* Prints `6` *)
  Fail (let x := reduce (RedStrong RedAll) (3+3) in M.print_term x;; M.failwith "").
  (* Prints `rbcv (3+3)` *)
  Fail (debug true [m:Dyn (@M.ret)] (let x := reduce (RedStrong RedAll) (3+3) in M.print_term x;; M.failwith "")).
Abort.
