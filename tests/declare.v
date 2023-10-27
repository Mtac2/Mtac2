From Mtac2 Require Import Mtac2 Sorts MTele Specif.
Import M.notations.
Definition test := c <- M.declare dok_Definition "bla" false 1; M.print_term c.
Goal unit.
  MProof.
  (* TODO: inlining test here used to *not* work because of universes. *)
  c <- M.declare dok_Definition "bla" false 1; M.print_term c.
Qed.

Goal unit.
MProof. test. Qed.

Typeclasses eauto := debug.
Structure ST := mkS { s : nat }.

Require Mtac2.lib.List.
Import Mtac2.lib.List.ListNotations.
Definition cs := c1 <- M.declare dok_CanonicalStructure "bla" false (fun (x : nat) => (fun x => mkS x) x);
                    c2 <- M.declare dok_Definition "bli" true c1;
                    M.declare_implicits c2 [m: ia_MaximallyImplicit];;
                    M.ret tt.

Compute ltac:(mrun cs).
Print bla.
Print Coercions.
Print Canonical Projections.
Print bli.
Fail Compute (bli 1).
Compute (@bli 1).

Module DeclareTest.
  Fail Compute ltac:(mrun (M.declare_implicits (1+1) [m:])).
  Local Arguments Nat.add {_ _}.
  Fail Compute ltac:(mrun (M.declare_implicits (Nat.add) [m:])).
  Fail Compute ltac:(mrun (M.declare_implicits (Nat.add (n:=1)) [m:])).
  Compute ltac:(mrun (M.declare_implicits (@Nat.add) [m:])).
  Compute ltac:(mrun (M.declare_implicits (@Nat.add) [m: ia_MaximallyImplicit | ia_MaximallyImplicit])).
  Definition should_work0 := Nat.add (n:=3) (m :=2).
  Compute ltac:(mrun (M.declare_implicits (@Nat.add) [m: ia_Implicit | ia_Explicit])).
  Definition should_work2 := Nat.add (n:=3) 2.
  Compute ltac:(mrun (M.declare_implicits (@Nat.add) [m: ia_Explicit | ia_MaximallyImplicit])).
  Definition should_work1 := Nat.add (m :=3) 2.
  Compute ltac:(mrun (M.declare_implicits (@Nat.add) [m: ia_Explicit | ia_Explicit])).
  Definition should_work := Nat.add 3 2.
End DeclareTest.
Require Import Strings.String.
Import M.notations.

Fixpoint defineN (n : nat) : M unit :=
  match n with
  | 0 => M.ret tt
  | S n =>
    s <- M.pretty_print n;
    M.declare dok_Definition ("NAT"++s)%string false n;;
    defineN n
  end.
Fail Print NAT0.
Compute ltac:(mrun (defineN 4)).

Print NAT0.
Print NAT1.
Print NAT2.
Print NAT3.
Fail Print NAT4.

Set Printing All. (* nasty *)
Fail Compute ltac:(mrun (defineN 4)).
Search "NAT". (* Now there are no definitions like "NATS (S O)" *)
Fail Compute ltac:(mrun (M.get_reference "NATS O")).

Definition ev := c <- M.declare dok_Definition "_" true (S O); M.print_term c.
Compute (M.eval ev). (* it was failing *)

Unset Printing All.

(* ouch, there should be a catchable error. but what about previously declared objects? *)
Definition alrdecl := mtry defineN 5 with [?s] AlreadyDeclared s => M.print s;; M.ret tt end.
Compute ltac:(mrun alrdecl).

Print NAT4. (* definitions before the failing one are declared. *)

(* NOTE: We give a unidirectional version of Nat.succ_le_mono for compatibility. *)
Lemma succ_le_mono_lr (n m : nat) : n <= m -> S n <= S m.
Proof. now apply ->PeanoNat.Nat.succ_le_mono. Qed.

(* we should check that the terms are closed w.r.t. section variables *)
(* JANNO: for now we just raise an catchable exception. *)
Fail Compute fun x y =>
          ltac:(mrun (
                    mtry
                      M.declare dok_Definition "lenS" true (succ_le_mono_lr x y);; M.ret tt
                      with | UnboundVar => M.failwith "This must fail" | _ => M.ret tt end
               )).

(* This used to fail because of weird universe issues. *)
Compute ltac:(mrun (c <- M.declare dok_Definition "blu" true (succ_le_mono_lr); M.print_term c)).
Definition decl_blu := (c <- M.declare dok_Definition "blu" true (succ_le_mono_lr); M.print_term c).
(* This now fails because the previous failure no longer exists and [blu] is declared. *)
Fail Compute ltac:(mrun decl_blu).

Print blu.


Definition backtracking_test :=
  mtry
    M.declare dok_Definition "newone" false tt;;
    M.declare dok_Definition "blu" false tt;;
    M.ret tt
  with [?s] AlreadyDeclared s => M.ret tt end.

Compute ltac:(mrun backtracking_test).

Print newone. (* is this expected? or should the "state" of definitions be also backtracked? *)
Print blu.


Module Inductives.
  Set Polymorphic Inductive Cumulativity.
  Unset Universe Minimization ToSet.
  Import ListNotations.

Definition typ_of {A : Type} (a : A) := A.
Import TeleNotation.
Notation P := [tele (T : Type) (k : nat)].
Module M1.
  Notation I2 := (m: "blubb__"%string; fun T k => mexistT (MTele_ConstT _) ([tele _ : k = k]) (fun _ => Propₛ)).
  Definition mind_test := (M.declare_mind P ([m: I2])).
  Eval cbv beta iota fix delta [mfold_right typ_of] in typ_of mind_test.
  (* Eval cbv beta iota fix delta [mfold_right typ_of] in *)

  Definition testprog :=
    mind_test
      (fun I2 T k =>
         (m:
          mnil;
          tt)
      ).

  Eval cbv in testprog.

  Eval cbn in ltac:(mrun(
                        let t := dreduce ((@S.Fun), testprog) testprog in
                        t
                   )).

End M1.

Module M2.
  Notation I2 := (m: "blubb__"%string; fun T k => mexistT (MTele_ConstT _) ([tele _ : k = k]) (fun _ => Propₛ)).
  Definition mind_test := (M.declare_mind P ([m: I2])).
  Eval cbv beta iota fix delta [mfold_right typ_of] in typ_of mind_test.
  (* Eval cbv beta iota fix delta [mfold_right typ_of] in *)

  Definition testprog :=
    mind_test
      (fun I2 T k =>
         (m:
          [m:
             (m: "c1"%string,
                 mexistT
                   _
                   (mTele (fun t : T => mBase))
                   (S.Fun (sort:=Typeₛ) (fun t => ((mexistT _ eq_refl tt))))
             )
          ];
          tt)
      ).

  Eval cbv in testprog.

  Eval cbn in ltac:(mrun(
                        let t := dreduce ((@S.Fun), testprog) testprog in
                        t
                   )).

End M2.

Module M3.

Notation I1 := (m: "bla__"%string; fun T k => mexistT (MTele_ConstT _) ([tele]) (Typeₛ)).
Notation I2 := (m: "blubb__"%string; fun T k => mexistT (MTele_ConstT _ ) ([tele]) (Propₛ)).
Definition mind_test := (M.declare_mind P ([m: I1 |  I2])).
Eval cbv beta iota fix delta [mfold_right typ_of] in typ_of mind_test.
(* Eval cbv beta iota fix delta [mfold_right typ_of] in *)

Definition testprog :=
    mind_test
    (fun I1 I2 T k =>
       (m:
          [m:
             (m: "c1"%string,
                 mexistT
                   _
                   (mTele (fun t : I2 T k => mBase))
                   (S.Fun (sort:=Typeₛ) (fun t => tt))
             )
          ];
          [m:
             (m: "c2"%string,
                 mexistT
                   _
                   (mTele (fun t : I1 T k => mBase))
                   (S.Fun (sort:=Typeₛ) (fun t => tt))
             )
          ];
        tt)
    ).

Eval cbn in ltac:(mrun(
                      let t := dreduce ((@S.Fun), testprog) testprog in
                      t
    )).

End M3.

Module M4.
  Notation I1 := (m: "bla__"%string; fun T k => mexistT (MTele_ConstT _) ([tele x y : nat]) (fun x y => Typeₛ)).
  Notation I2 := (m: "blubb__"%string; fun T k => mexistT (MTele_ConstT _) ([tele _ : k = k]) (fun _ => Propₛ)).
  Definition mind_test := (M.declare_mind P ([m: I1 |  I2])).
  Eval cbv beta iota fix delta [mfold_right typ_of] in typ_of mind_test.
  (* Eval cbv beta iota fix delta [mfold_right typ_of] in *)

  Definition testprog :=
    mind_test
      (fun I1 I2 T k =>
         (m:
            [m:
               (m: "c1"%string,
                   mexistT
                     _
                     (mTele (fun t : I2 T k eq_refl => mBase))
                     (S.Fun (sort:=Typeₛ) (fun t => (mexistT _ 1 (mexistT _ 2 tt))))
               )
            ];
          mnil;
          tt)
      ).

  Eval cbn in ltac:(mrun(
                        let t := dreduce ((@S.Fun), testprog) testprog in
                        t
                   )).

End M4.
End Inductives.


Module ExistingInstance.
  Module Inner.
    Class dummy := Dummy { dummy_nat : nat; dummy_extra : string }.

    Definition test_global5 : dummy := Dummy 5 "5".
    Definition test_global55 : dummy := Dummy 55 "55".
    Definition test_local1 : dummy := Dummy 1 "1".

    Mtac Do (M.existing_instance "test_global5" (mSome 5%N) true ).
    Mtac Do (M.existing_instance "test_global55" (mSome 55%N) true ).
    Mtac Do (M.existing_instance "test_local1" (mSome 1%N) false).

    Mtac Do (M.ret (meq_refl : dummy_nat =m= 1)).
  End Inner.

  Fail Mtac Do (M.ret (meq_refl : Inner.dummy_nat =m= 1)).
  Mtac Do (M.ret (meq_refl : Inner.dummy_nat =m= 5)).
  Fail Mtac Do (M.ret (meq_refl : Inner.dummy_nat =m= 55)).

End ExistingInstance.
