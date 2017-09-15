From Mtac2 Require Import List Mtac2.

Import M.notations.
Require Import Strings.String.

Definition Break : Exception. exact exception. Qed.

Definition debug {A:Type} (bks : list dyn) : M A -> M unit :=
  M.break (fun A (x:A) =>
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
             else M.ret x).

Definition debugT {A} (bks : list dyn) (t: gtactic A) : gtactic unit := fun g=>
  debug bks (t g) ;; M.ret nil.
Import Mtac2.List.ListNotations.


Definition test : True.
MProof.
  debugT [m: (*HAVE FUN Dyn (@M.ret) | Dyn (@M.unify) *)] (T.apply I).
Qed.