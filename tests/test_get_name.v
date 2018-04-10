Require Import Mtac2.Mtac2.

Goal True.
MProof.
  (s <- M.get_binder_name (fun name:nat=>name);
  match String.string_dec s "name" with
  | Specif.left _ => M.ret I
  | _ => M.raise exception
  end)%MC.
Qed.

Goal forall x:nat, True.
MProof.
  M.ret (fun name=>_).
  Unshelve.
  (s <- M.get_binder_name name;
  match String.string_dec s "name" with
  | Specif.left _ => M.ret I
  | _ => M.raise exception
  end)%MC.
Qed.

Goal True.
MProof.
  M.nu (TheName "name") mNone (fun x:nat=>
  s <- M.get_binder_name x;
  match String.string_dec s "name" with
  | Specif.left _ => M.ret I
  | _ => M.raise exception
  end)%MC.
Qed.

Goal True.
MProof.
  (r <- M.nu (TheName "name") mNone (fun x:nat => M.abs_fun x x);
  s <- M.get_binder_name r;
  match String.string_dec s "name" with
  | Specif.left _ => M.ret I
  | _ => M.raise exception
  end)%MC.
Qed.
