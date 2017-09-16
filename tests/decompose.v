From Mtac2 Require Import List Mtac2.
Import ListNotations.

Definition decompose {A} (x : A) :=
  (mfix2 f (d : dyn) (args: list dyn) : M (dyn * list dyn) :=
    mmatch d with
    | [? A B (t1: A -> B) t2] Dyn (t1 t2) => f (Dyn t1) [m: Dyn t2 & args]
    | [? A B (t1: forall x:A, B x) t2] Dyn (t1 t2) => f (Dyn t1) [m: Dyn t2 & args]
    | _ => M.ret (d, args)
    end) (Dyn x) [m:].

Goal True.
MProof.
d <- decompose (M.ret I);
match d with
| (Dyn r, _) => mif M.unify_cumul M.ret r UniCoq then T.exact I else T.raise exception
end.
Qed.

Import M.notations.

Definition debug :=
  M.break (fun A (x:A) =>
             v <- decompose x;
               let (hd, _) := v in
               M.print_term hd;;
             mif M.unify (Dyn (@M.ret)) hd UniCoq then
               M.ret x
             else M.raise exception) (M.ret I);; M.ret I.

Import Mtac2.List.ListNotations.


Definition test : True.
MProof.
  Fail debug . (* it should unify with @M.ret, but it isn't because decompose returns [@M.ret True] *)
Abort.
