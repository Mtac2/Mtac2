From MetaCoq Require Import Mtac2 Tactics.
Import MtacNotations.
Import TacticsNotations.

Require Import Strings.String.
Require Import MetaCoq.Plist.
Import PlistNotations.

Definition qualify s := String.append "MetaCoq.ImportedTactics." s.

Ltac trivial := trivial.
Definition trivial : tactic := ltac (qualify "trivial") [].

Ltac discriminate := discriminate.
Definition discriminate : tactic := ltac (qualify "discriminate") [].

Ltac intuition := intuition.
Definition intuition : tactic := ltac (qualify "intuition") [].

Ltac auto := auto.
Definition auto : tactic := ltac (qualify "auto") [].

Ltac subst := subst.
Definition subst : tactic := ltac (qualify "subst") [].

Ltac contradiction := contradiction.
Definition contradiction : tactic := ltac (qualify "contradiction") [].

Ltac tauto' := tauto.
Definition tauto : tactic := ltac (qualify "tauto'") [].

Ltac unfold x := unfold x.
Definition unfold {A} (x: A) := ltac (qualify "unfold") [Dyn x].

Ltac rrewrite1 a := rewrite a.
Ltac rrewrite2 a b := rewrite a, b.
Ltac rrewrite3 a b c := rewrite a, b, c.
Ltac rrewrite4 a b c d := rewrite a, b, c, d.
Ltac rrewrite5 a b c d e := rewrite a, b, c, d, e.

Definition compute_terminator {A} (l: plist A) : M string :=
  match l with
  | [] => failwith "At least one required"
  | [_] => ret "1"
  | [_;_] => ret "2"
  | [_;_;_] => ret "3"
  | [_;_;_;_] => ret "4"
  | [_;_;_;_;_] => ret "5"
  | _ => failwith "Unsupported"
  end.

Ltac lrewrite1 a := rewrite <- a.
Ltac lrewrite2 a b := rewrite <- a, b.
Ltac lrewrite3 a b c := rewrite <- a, b, c.
Ltac lrewrite4 a b c d := rewrite <- a, b, c, d.
Ltac lrewrite5 a b c d e := rewrite <- a, b, c, d, e.

Inductive RewriteDirection := LeftRewrite | RightRewrite.

Definition trewrite (d: RewriteDirection) (args: plist dyn) : tactic := fun g=>
  ter <- compute_terminator args;
  let prefix := match d with LeftRewrite => "l" | RightRewrite => "r" end in
  let name := reduce RedNF (qualify (prefix++"rewrite"++ter)) in
  ltac name args g.


Notation "'rewrite' '->' x , .. , z" :=
  (trewrite RightRewrite (pcons (Dyn x) .. (pcons (Dyn z) pnil) ..))
    (at level 0, x at next level, z at next level).
Notation "'rewrite' '<-' x , .. , z" :=
  (trewrite LeftRewrite (pcons (Dyn x) .. (pcons (Dyn z) pnil) ..))
    (at level 0, x at next level, z at next level).
Notation "'rewrite' x , .. , z" :=
  (trewrite RightRewrite (pcons (Dyn x) .. (pcons (Dyn z) pnil) ..))
    (at level 0, x at next level, z at next level).

Ltac elim h := elim h.
Definition elim {A} (x:A) : tactic :=
  ltac (qualify "elim") [Dyn x].

Notation induction := elim.

Definition injection {A} (x: A) : tactic :=
  ltac ("Coq.Init.Notations.injection") [Dyn x].

Ltac inversion H := inversion H.
Definition inversion {A} (x: A) : tactic :=
  ltac (qualify "inversion") [Dyn x].
