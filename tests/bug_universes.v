From MetaCoq Require Import MetaCoq.

Set Printing Universes.

(* Demonstrate that id indeed has the right type *)
Definition test@{i j} : Type@{i} -> Type@{max(i,j)} := id.

(* Demonstrate that ltac gets it right *)
Lemma testL@{i j} : Type@{i} -> Type@{max(i,j)}.
Proof. exact id. Qed.

(* Demonstrate that M.ret gets it right *)
Lemma testM@{i j} : Type@{i} -> Type@{max(i,j)}.
MProof.
M.ret id.
Qed.

(* Demonstrate that runTac doesn't get it right *)
Lemma testMTac@{i j} : Type@{i} -> Type@{max(i,j)}.
MProof.
T.exact id.
Qed.
