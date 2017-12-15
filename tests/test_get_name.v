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
  M.nu "name" mNone (fun x:nat=>
  s <- M.get_binder_name x;
  match String.string_dec s "name" with
  | Specif.left _ => M.ret I
  | _ => M.raise exception
  end)%MC.
Qed.

Goal True.
MProof.
  (r <- M.nu "name" mNone (fun x:nat => M.abs_fun x x);
  s <- M.get_binder_name r;
  match String.string_dec s "name" with
  | Specif.left _ => M.ret I
  | _ => M.raise exception
  end)%MC.
Qed.

Example fresh_name_works_with_same_name (x:nat) : True.
MProof.
  (s <- M.fresh_binder_name (fun y:nat=>y);
  match String.string_dec s "y" with
  | Specif.left _ => M.ret I
  | _ => M.raise exception
  end)%MC.
Qed.

Example existing_name_works_with_diff_name (x:nat) : True.
MProof.
  (s <- M.fresh_binder_name (fun x:nat=>x);
  match String.string_dec s "x_" with
  | Specif.left _ => M.ret I
  | _ => M.raise exception
  end)%MC.
Qed.
