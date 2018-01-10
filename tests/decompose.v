From Mtac2 Require Import List Mtac2 Debugger.
Import ListNotations.
Import M.
Import M.notations.
Definition decompose {T} (x : T) :=
  (mfix2 f (d : dyn) (args: mlist dyn) : M (dyn *m mlist dyn) :=
    M.print_term d;;
    mmatch d with
    | [? A B (t1: A -> B) t2] Dyn (t1 t2) => f (Dyn t1) (Dyn t2 :m: args)
    | [? A B (t1: forall (x:A), B x) t2] Dyn (t1 t2) => f (Dyn t1) (Dyn t2 :m: args)
    | _ => M.ret (m: d, args)
    end) (Dyn x) [m:].

(* If I'm not mistaken, the problem comes from the unification of

      ?t1 ?t2 =?= M.ret True

   Which first tries to unify ?t1 with M.ret, without the knoweldge of
   it being restricted by the second argument. I think it should first
   unify ?t2 and then ?t1 (or delay the unification. *)
Goal True.
  MProof.
   Fail mmatch Dyn (@M.ret True) with
   | [? (P : Type -> Prop) (t1 : forall X:Type, P X) (t2 : Prop) ]  @Dyn (P t2) (t1 t2) => M.ret I
    | _ => M.raise exception
  end.
Abort.
