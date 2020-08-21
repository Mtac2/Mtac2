From Mtac2 Require Import Mtac2.

Set Printing Universes.

(* Demonstrate that id indeed has the right type *)
Definition test@{i j} : Type@{i} -> Type@{max(i,j)} := id.

(* Demonstrate that ltac gets it right *)
Lemma testL@{i j} : Type@{i} -> Type@{max(i,j)}.
Proof. exact id. Qed.

(* M.ret somehow works in 8.8 *)
Lemma testM@{i j} : Type@{i} -> Type@{max(i,j)}.
MProof.
M.ret id.
Qed.

(* runTac works too *)
Lemma testMTac@{i j} : Type@{i} -> Type@{max(i,j)}.
MProof.
T.exact id.
Qed.

(* apply generates a universe index *)
Lemma testMTacApply@{i j} : Type@{i} -> Type@{max(i,j)}.
MProof.
T.apply (@id).
Qed.

(* but ltac's 8.8  doesn't do that *)
Lemma testLApply@{i j} : Type@{i} -> Type@{max(i,j)}.
Proof. apply @id. Qed.

Notation "p '=e>' b" := (pbase p%core (fun _ => b%core) UniEvarconv)
  (no associativity, at level 201) : pattern_scope.
Notation "p '=e>' [ H ] b" := (pbase p%core (fun H => b%core) UniEvarconv)
  (no associativity, at level 201, H at next level) : pattern_scope.

Definition test_match {A:Type(*k*)} (x:A) : tactic :=
  mmatch A with
  | [? B] B =e> T.exact x
  end.


Lemma testMmatch@{i j} : Type@{i} -> Type@{max(i,j)}.
MProof.
test_match (fun x=>x).
Qed.

Lemma testMmatch' : Type -> Type.
MProof.
test_match (fun x=>x).
Qed.
Print testMmatch.
Print testMmatch'.
(* These are the universe constraints: i <= j, i < m, i < test_match.k
   I think m is the univere free from mmatch. But why is it required to be > instead of >= i? *)

Definition testdef : Type -> Type := fun x=>x.
Lemma testret : Type -> Type.
MProof.
M.ret (fun x=>x).
Fail Qed. (* fails, I think it is not inferring the right universes? *)
Abort.
Fail Print testret.

Polymorphic Lemma testexact : Type -> Type.
MProof.
T.exact (fun x=>x).
Qed.
About testexact. (* there are way too many universes in this *)
