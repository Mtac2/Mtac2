Require Import Strings.String.
From Mtac2.intf Require Import Name.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Inductive Exception : Prop := exception : Exception.

Definition StuckTerm : Exception. exact exception. Qed.

Definition NotAList : Exception. exact exception. Qed.

Definition HypsUniverseError : Exception. exact exception. Qed.

Definition NotAUnifStrategy : Exception. exact exception. Qed.
Definition ReductionFailure : Exception. exact exception. Qed.

Definition TermNotGround : Exception. exact exception. Qed.

Definition WrongTerm : Exception. exact exception. Qed.

Definition HypMissesDependency : Exception. exact exception. Qed.
Definition TypeMissesDependency : Exception. exact exception. Qed.
Definition DuplicatedVariable : Exception. exact exception. Qed.
Definition NotAVar : Exception. exact exception. Qed.

Definition NotAForall : Exception. exact exception. Qed.
Definition NotAnApplication : Exception. exact exception. Qed.

Definition LtacError (s:string) : Exception. exact exception. Qed.

Definition NotUnifiable {A} (x y : A) : Exception. exact exception. Qed.

Definition Failure (s : string) : Exception. exact exception. Qed.

Definition NameExistsInContext (n : Name.name) : Exception. exact exception. Qed.
Definition InvalidName (n : Name.name) : Exception. exact exception. Qed.

Definition ExceptionNotGround : Exception. exact exception. Qed.

Definition CannotRemoveVar (x : string) : Exception. exact exception. Qed.

Definition RefNotFound (x : string) : Exception. exact exception. Qed.

Definition AbsDependencyError : Exception. exact exception. Qed.
Definition AbsVariableIsADefinition : Exception. exact exception. Qed.
Definition AbsLetNotConvertible : Exception. exact exception. Qed.

Definition VarAppearsInValue : Exception. exact exception. Qed.

Definition NotALetIn : Exception. exact exception. Qed.
Definition NotTheSameType : Exception. exact exception. Qed.

Definition DoesNotMatch : Exception. exact exception. Qed.
Definition NoPatternMatches : Exception. exact exception. Qed.
Definition Anomaly : Exception. exact exception. Qed.
Definition Continue : Exception. exact exception. Qed.

Definition NameNotFound (n: string) : Exception. exact exception. Qed.
Definition WrongType (T: Type) : Exception. exact exception. Qed.

Definition EmptyList : Exception. exact exception. Qed.
Definition NotThatManyElements : Exception. exact exception. Qed.

Definition CantCoerce : Exception. exact exception. Qed.
Definition NotCumul {A B} (x: A) (y: B) : Exception. exact exception. Qed.

Definition NotAnEvar {A} (x: A) : Exception. exact exception. Qed.
Definition CantInstantiate {A} (x t: A) : Exception. exact exception. Qed.

Definition NotAReference {A} (x : A) : Exception. exact exception. Qed.
Definition AlreadyDeclared (name : string) : Exception. exact exception. Qed.
Definition UnboundVar : Exception. exact exception. Qed.

Definition NotAMatchExp : Exception. exact exception. Qed.
Definition NotAnInductive : Exception. exact exception. Qed.

Definition NoClassInstance (A : Type) : Exception. exact exception. Qed.

Definition NotFound : Exception. exact exception. Qed.

(* We don't want the user to catch this error: it's someone messing up the
invariant that goals are opened. *)
Notation NotAGoal := (Failure "Not a Goal").
