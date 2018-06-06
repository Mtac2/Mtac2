From Mtac2 Require Import Base List.
Import M.notations.

Definition ConstrNotFound : Exception. constructor. Qed.
Definition ConstrsUnmentioned (m : mlist dyn) : Exception. constructor. Qed.

Definition find_in_constrs {C} (c : C)  : mlist dyn -> M (mlist dyn) :=
  mfix1 f (cs : _) : M _ :=
    match cs with
    | mnil => M.ret mnil
    | mcons c' cs =>
      let C := reduce (RedVmCompute) C in
      u <- M.unify c' (@Dyn C c) UniMatchNoRed;
      match u with
      | mSome _ =>
        M.ret cs
      | mNone =>
        l <- f cs;
        M.ret (c' :m: l)
      end
    end.


Definition check_exhaustiveness {A B y}
           (ps_in : mlist (branch M A B y))
           (ops : moption (mlist (branch M A B y))) :
  M (mlist (branch M A B y)) :=
  ''(mpair _ constrs) <- M.constrs A;
  (
    mfix2 f (ps : _) (constrs : _) : M _ :=
      match ps, constrs with
      | mnil, mnil =>
        match ops with
        | mNone => M.ret ps_in
        | mSome ps' => let ps := dreduce (@mapp) (mapp ps_in ps') in
                       M.ret ps
        end
      | mcons p ps, _ =>
        match p with
        | branch_app_static U C _ =>
          constrs <- find_in_constrs C constrs;
          f ps constrs
        | _ => f ps constrs
        end
      | _, _ => M.raise (ConstrsUnmentioned constrs)
      end
  ) ps_in constrs
.

Notation "'exhaustively_with' | p1 | .. | pn 'end'" :=
  (let ps' := mcons p1%branch .. (mcons pn%branch mnil%branch) .. in
           ltac:(mrun (check_exhaustiveness ps' (mNone)))
  )
    (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.