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
  let print_if_trace {A} (x:A) := (if trace then M.print_term x else M.ret tt);; M.ret x in
  M.break (fun A (x:M A) =>
             v <- M.decompose x;
             let (hd, _) := v in
             let (_, hd) := hd : dyn in
             mif isReduce hd then (* avoid computation of reduce *)
               print_if_trace x
             else
               let x := reduce (RedWhd [rl:RedBeta;RedMatch;RedFix;RedZeta]) x in
               v <- M.decompose x;
               let (hd, _) := v in
               mif M.find (fun d=> M.cumul UniMatchNoRed d hd) bks then
                 M.print_term x;;
                 inp <- M.read_line;
                 match inp with
                 | "e" => M.raise Break
                 | _ => M.ret x
                 end
               else print_if_trace x).

Definition debugT {A} (trace: bool) (bks : list dyn) (t: gtactic A) : gtactic unit := fun g=>
  debug trace bks (t g) ;; M.ret nil.
