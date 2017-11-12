From Mtac2 Require Import Mtac2.

Import M.

Require Import Lists.List.
Import ListNotations.

Set Use Unicoq.

Structure execV {A} (f : M A) B := ExecV { value : B } .

Canonical Structure the_value {A} (f : M A) v := ExecV _ f (lift f v) v.

Arguments value {A} f {B} {e}.


Definition exec {A} (f : M A) {v:A} : lift f v := v.



Goal True.
refine (let H := _ in let _ : value (ret I) = H := eq_refl in H).
Qed.

Goal True.
refine (exec (print "hola";; ret I)).
Qed.

Goal True.
refine (exec (raise exception)).
Abort. (* note that it doesn't fail, it just silently leaves the goal open
 (in fact, the proof will contain exec) *)

Notation "'[ex' t ']'" := (exec t) (at level 0).

Goal [ex ret True] = True.
  unfold exec.
  reflexivity.
Qed.
Import M.notations.
Definition silly :=
  fix f (n: nat) : M Prop :=
    match n with
    | 0 => ret True
    | S n' => f n' >>= fun r=>ret (True -> r)
    end.

Goal [ex silly 3] : _. (* we need the : to make sure it triggers the rule for lift *)
  unfold exec.
Abort.

(*
Module Second.
Import First.
Section Inlist.

Parameter A : Type.

Structure inlist x := Inlist { list_of :> list A; proof : In x list_of }.
Arguments list_of {x} i.
Arguments proof {x} i.

Program
Definition unify {A} (x y : A) (P : A -> Type) (f : P y) : M (P x) :=
    mmatch x with
    | y => [H] ret (meq_rect_r P f H)
    | _ => raise exception
    end.

Import M.notations.

Program Canonical Structure cons_inst x y s (f : execV (
  mtry
    unify y x (fun z=>In x (z :: s)) (in_eq x s)
  with exception =>
    e <- evar (inlist x);
    unify s (list_of e) (fun l=>In x (y :: l))
      (in_cons y x (list_of e) (proof e))
  end))
 := Inlist x (y :: value _ f) (result f).

Program Canonical app_inst x s1 (f : execV (fun s2=>
  e <- evar (inlist x);
  mtry
    unify s1 (list_of e) (fun s1 => In x (s1 ++ s2))
      (in_or_app (list_of e) s2 x (or_introl (proof e)))
  with NotUnifiableException =>
    unify s2 (list_of e) (fun s2 => In x (s1 ++ s2))
      (in_or_app s1 (list_of e) x (or_intror (proof e)))
  end))  := Inlist x (s1 ++ value _ f) (result f).

Definition test (x y z : A) : In x (x :: y :: z :: nil) := proof _.
Definition test1 (x y z : A) : In y (x :: y :: z :: nil) := proof _.
Definition test3 (x y z : A) : In y ([z;y] ++ [x;z]) := proof _.
Definition test4 (x y z : A) s : In z (s ++ [x;z]) := proof _.

End Inlist.

*)