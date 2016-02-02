Require Import MetaCoq.MetaCoq.
Require Import MetaCoq.Tactic.
Import MetaCoq.MetaCoqNotations.

Example basic : True.
MProof.
  Trefine I.
Qed.

Definition exact {A} (t:A) := Trefine t.

Infix "t ; u" := (Tthen t u) (at level 30).

Notation "'Mlet' x ':=' t 'in' u" := (Tlet t (fun x=>u)) (at level 50).

Example basic2 : True.
MProof.
  Mlet x := ret I in
  Trefine x.
Qed.

Example basic3 : True.
MProof.
  Tor (Mlet x := raise exception : M True in
       Trefine x)
  (fun _ => Trefine I).
Qed.

Example basic4 : True.
MProof.
  Tor (Traise exception)
  (fun _ => Trefine I).
Qed.

Example basic5 : True.
MProof.
  Tor (Trefine I)
  (fun _ => Trefine false).
Qed.

Example basic6 : True /\ True.
MProof.
  Trefine False. (* WHAT??? *)
Fail Qed.
Abort.

(* Local Variables: *)
(* coq-prog-name: "coqtop.byte" *)
(* coq-load-path: nil *)
(* End: *)
