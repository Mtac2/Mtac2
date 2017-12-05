Require Import Mtac2.Base.
Import M.
Import notations.

Goal True.
MProof.
  mtry' (raise exception) (fun _=>ret I).
Qed.

Definition one : Exception. exact exception. Qed.

Goal True.
MProof.
  mtry' (unify one one UniCoq;; raise exception) (fun _=>ret I).
Qed.

Goal True.
MProof.
  mtry' (raise one) (fun e =>
    mtry' (unify_or_fail UniCoq e one ;; raise e) (fun _=>ret I)).
Qed.


Goal True.
MProof.
  mtry raise exception with _ => ret I end.
Qed.

Goal True.
MProof.
  mtry @raise True exception with exception => ret I end.
Qed.

Goal True.
MProof.
  Fail mtry @raise True one with exception => ret I end.
  ret I.
Qed.

(* Local Variables: *)
(* coq-prog-name: "~/coq/coq8.6/coq-8.6/bin/coqtop.byte" *)
(* coq-load-path: nil *)
(* End: *)
