Require Import Mtac2.Mtac2.
Import T.

Goal True.
MProof.
  (mmatch I with
  [? i] i => M.ret i : M True
  end)%MC.
Qed.

Goal True.
MProof.
  (mmatch _ with
  [? i] i => M.ret i : M True
  end)%MC.
  Unshelve.
  (mmatch (fun x=>x) I with
  [? i] (fun x=>x) i => M.ret i : M True
  end)%MC.
Qed.

Goal True.
MProof.
  (* uninstantiated i *)
  (mmatch (fun x=>x) I with
  [? i] I => M.ret i : M True
  end)%MC.
  (* do not reduce pattern *)
  Fail (mmatch I with
  [? i] (fun x=>x) i => M.ret i : M True
  end)%MC.
  Unshelve.
  (mmatch I with
  | [? i] (fun x=>x) i => M.ret i : M True
  | [? i] i => M.ret i : M True
  end)%MC.
Qed.


Require Import List.
Import ListNotations.

(** Testing the construction of mmatch *)
Definition NotFound : Exception. exact exception. Qed.

Require Import Init.Datatypes.
Require Import Lists.List.
Import Base.M.
Import M.notations.

Definition inlist A (x : A) : forall (l : list A), M (In x l) :=
  mfix1 f (l : list A) : M (In x l) :=
  mmatch l with
  | [? l r] l ++ r =>
      M.mtry' (
        il <- f l;
        M.ret (in_or_app l r x (or_introl il)) )
      (fun e=>mmatch e with NotFound =>
        ir <- f r;
        M.ret (in_or_app l r x (or_intror ir))
      end)
  | [? s] (x :: s) => M.ret (in_eq _ _)
  | [? y s] (y :: s) => r <- f s; M.ret (in_cons y _ _ r)
  | _ => M.raise NotFound
  end.
Import ListNotations.

(** Testing the execution of mmatch *)
Example testM (
x01 x11 x21 x31 x41 x51 x61 x71 x81 x91
x02 x12 x22 x32 x42 x52 x62 x72 x82 x92
x03 x13 x23 x33 x43 x53 x63 x73 x83 x93
x04 x14 x24 x34 x44 x54 x64 x74 x84 x94
x05 x15 x25 x35 x45 x55 x65 x75 x85 x95
x06 x16 x26 x36 x46 x56 x66 x76 x86 x96
x07 x17 x27 x37 x47 x57 x67 x77 x87 x97
x08 x18 x28 x38 x48 x58 x68 x78 x88 x98
x09 x19 x29 x39 x49 x59 x69 x79 x89 x99
 : nat) : In x99 [
x01;x11;x21;x31;x41;x51;x61;x71;x81;x91;
x02;x12;x22;x32;x42;x52;x62;x72;x82;x92;
x03;x13;x23;x33;x43;x53;x63;x73;x83;x93;
x04;x14;x24;x34;x44;x54;x64;x74;x84;x94;
x05;x15;x25;x35;x45;x55;x65;x75;x85;x95;
x06;x16;x26;x36;x46;x56;x66;x76;x86;x96;
x07;x17;x27;x37;x47;x57;x67;x77;x87;x97;
x08;x18;x28;x38;x48;x58;x68;x78;x88;x98;
x09;x19;x29;x39;x49;x59;x69;x79;x89;x99
].
MProof.
  Time inlist _ _ _.
Qed.


(* This definition fails because Coq is unable to find the returning type*)
Fail Definition test (t : nat)  :=
  mmatch t with
  | 0 => ret (eq_refl 0)
  end.

(* We need the [return] clause *)
Definition test_return (t : nat) : M (t = t) :=
  mmatch t as x return M (x = x) with
  | 0 => M.ret (eq_refl 0)
  end.

(* testing with a different name *)
Definition test_return_in (t : nat) : M (t = t) :=
  mmatch 0+t as x return M (x = x) with
  | 0 => M.ret (eq_refl 0)
  end.

(* testing no reducing patterns *)
(* note that in this case we change the order (it doesn't matter) *)
Definition inlist_nored A (x : A) : forall (l : list A), M (In x l) :=
  mfix1 f (l : list A) : M (In x l) :=
  mmatch l with
  | [? s] (x :: s) =n> M.ret (in_eq _ _)
  | [? y s] (y :: s) =n> r <- f s; M.ret (in_cons y _ _ r)
  | [? l r] l ++ r =n>
    mtry
      il <- f l;
      M.ret (in_or_app l r x (or_introl il))
    with NotFound =>
      ir <- f r;
      M.ret (in_or_app l r x (or_intror ir))
    end
  | _ => M.raise NotFound
  end.

Example with_red : In 0 ([1;2]++[0;4]).
MProof.
  inlist _ _ _.
Defined.

Example with_nored : In 0 ([1;2]++[0;4]).
MProof.
  inlist_nored _ _ _.
Defined.

(* we prove that we get the same proof: the list wasn't reduce to cons
in the second case *)
Lemma are_equal : with_nored = with_red.
Proof. reflexivity. Qed.

(* if instead we use reduction (in the first two patterns),
   the proof is not the same: *)
Definition inlist_redcons A (x : A) : forall (l : list A), M (In x l) :=
  mfix1 f (l : list A) : M (In x l) :=
  mmatch l with
  | [? s] (x :: s) => M.ret (in_eq _ _)
  | [? y s] (y :: s) => r <- f s; M.ret (in_cons y _ _ r)
  | [? l r] l ++ r =n>
    mtry
      il <- f l;
      M.ret (in_or_app l r x (or_introl il))
    with NotFound =>
      ir <- f r;
      M.ret (in_or_app l r x (or_intror ir))
    end
  | _ => M.raise NotFound
  end.

Example with_redcons : In 0 ([1;2]++[0;4]).
MProof.
  inlist_redcons _ _ _.
Defined.

(* we can't prove we get the same proof: the list was reduce to cons
in the second case *)
Lemma are_not_equal : with_nored = with_redcons.
Proof. Fail reflexivity. Abort.


(* Test new `Sort` patterns *)

From Mtac2 Require Import Sorts.
Mtac Do ((fun (T : Type) =>
            mmatch T with [¿ s] [? (T : s)] (T : Type) =u>
              M.unify_or_fail UniMatchNoRed s Sorts.SProp;; M.ret I
          end) (True -> True)).
Mtac Do ((fun (T : Type) =>
            mmatch T with [¿ s] [? (T : s)] (T : Type) =u>
              M.unify_or_fail UniMatchNoRed s Sorts.SType;; M.ret I
          end) (True -> nat)).


(* Test new `Exception` parameter of `mmatch'` which is instantiated with an
exception different from `DoesNotMatch` for our encoding of `mtry`. The test
asserts that a `DoesNotMatch` exception can escape `mtry`. This is crucial for
certain backtracking metaprograms and tactics. *)

Mtac Do Set_Trace.
Mtac Do (
       M.mtry'
         (
          mtry
            M.raise DoesNotMatch
          with
          | DoesNotMatch =>
            mtry
              M.raise DoesNotMatch
            with
            | DoesNotMatch => M.raise DoesNotMatch
            end
          end)
         (fun e => M.unify_or_fail UniMatchNoRed e DoesNotMatch;; M.ret tt)
     ).