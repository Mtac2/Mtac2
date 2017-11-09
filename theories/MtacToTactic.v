From Mtac2 Require Import Mtac2 Datatypes List MTeleMatch MFix.
Import M.notations Mtac2.List.ListNotations.

Definition assumption_to_goal' : forall A, M ({T : Type & T -> A}) :=
  mfix rec A : M {T : Type & T -> A } :=
  mtmmatch A as A return M {T : Type & T -> A} with
  | [? X] ((M X) : Type) =c> M.ret (existT _ X (fun x => M.ret x))
  | [? X F] (forall x : X, F x) =c>
    s <- M.fresh_binder_name A;
    M.nu s mNone (fun x =>
      M.print_term ("F", F);;
      let Fx := rone_step (F x) in
      ''(existT _ T G) <- rec (Fx);
      T' <- M.abs_fun x T;
      M.print_term ("T'", T');;
      (* T' = forall x, T *)
      G <- M.coerce G;
      G <- M.abs_fun (P:=fun x => T' x -> F x) x G;
      M.print_term ("G", G);;
      let G' := fun t' : (forall x : X, T' x) => fun x : X => G x (t' x) in
      let G' := reduce (RedStrong RedAll) G' in (* TODO: fixme! too strong *)
      M.print_term ("G'", G');;
      M.ret (existT _ (forall x, T' x) G')
    )
    | A =n> M.ret (existT _ _ (fun x => x))
  end.

Check ltac:(mrun (assumption_to_goal' (forall x : nat, x > 0 -> M (x = x)))).

(* Definition assumption_to_goal (A : Type) : tactic := *)
(*   \tactic g => *)
(*   ''(existT _ T G) <- assumption_to_goal' A; *)
(*   t <- M.evar T; *)
(*   T.exact (G t) g;; *)
(*   M.ret [m: (tt, Goal t)] *)
(* . *)

Definition mtac_to_tactic {T : Type} (t : T) : tactic :=
  \tactic g =>
  gty <- M.goal_type g;
  (mfix rec T : T -> M (mlist (unit * goal)) :=
    mtmmatch T as T return T -> M (mlist (unit * goal)) with
    | (M gty : Type) =c> fun t => p <- t; T.exact p g
    | [? P Q] P -> Q =c> fun H : P -> Q =>
        ''(existT _ T G) <- assumption_to_goal' P;
        t <- M.evar T;
        let Gt := rone_step (G t) in
        let HGt := rone_step (H Gt) in
        gl <- rec _ HGt;
        M.print_term "??";;
        M.ret (mcons (tt, Goal t) gl)
    | T =n> fun _ => M.failwith "The given mtac function does not solve goals of this shape."
    end
  )
  T t
.

(* Goal (1 = 1). *)
(* MProof. *)
(* mtac_to_tactic (fun (H : M False) => t <- H; M.ret (match t with end)). *)
(* Abort. *)


(* Goal (1 = 1). *)
(* MProof. *)
(* mtac_to_tactic (fun (H : forall x : nat, False) => M.ret (match H 1 with end)). *)
(* Abort. *)