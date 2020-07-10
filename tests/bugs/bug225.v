From Mtac2 Require Import Base Datatypes.
Import M.notations.
From Coq Require Import String.

Definition reduce_nu :=
  ltac:(
    mrun
      (
        M.nu
          Generate
          (mNone)
          (fun k =>
             mtry k with
             | StuckTerm => M.ret tt
             | _ as _catchall => M.failwith "expected StuckTerm"
             end
          )
      )
  ).
