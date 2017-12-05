Require Import Mtac2.Base.
Import M.
Import M.notations.

Goal True.
MProof.
  M.bind (M.ret I) (fun r => M.ret r).
Qed.

Goal True.
MProof.
  (r <- M.ret I; M.ret r)%MC.
Qed.

Goal True.
MProof.
  (M.ret tt;; M.ret I)%MC.
Qed.

Goal True.
MProof.
  (M.mtry' (M.ret tt;; M.ret I) (fun _ =>M.ret I))%MC.
Qed.

(* Local Variables: *)
(* coq-prog-name: "~/coq/coq8.6/coq-8.6/bin/coqtop.byte" *)
(* coq-load-path: nil *)
(* End: *)
