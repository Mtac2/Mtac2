Require Import MetaCoq.MetaCoq.

Goal True.
MProof.
  s <- get_binder_name (fun name:nat=>name);
  match String.string_dec s "name" with
  | Specif.left _ => ret I
  | _ => raise exception
  end.
Qed.

Goal forall x:nat, True.
MProof.
  ret (fun name=>_).
  s <- get_binder_name name;
  match String.string_dec s "name" with
  | Specif.left _ => ret I
  | _ => raise exception
  end.
Qed.

Goal True.
MProof.
  tnu "name" None (fun x:nat=>
  s <- get_binder_name x;
  match String.string_dec s "name" with
  | Specif.left _ => ret I
  | _ => raise exception
  end).
Qed.

Goal True.
MProof.
  r <- tnu "name" None (fun x:nat=>abs x x);
  s <- get_binder_name r;
  match String.string_dec s "name" with
  | Specif.left _ => ret I
  | _ => raise exception
  end.
Qed.

Example fresh_name_works_with_same_name (x:nat) : True.
MProof.
  s <- fresh_binder_name (fun y:nat=>y);
  match String.string_dec s "y" with
  | Specif.left _ => ret I
  | _ => raise exception
  end.
Qed.

Example existing_name_works_with_diff_name (x:nat) : True.
MProof.
  s <- fresh_binder_name (fun x:nat=>x);
  match String.string_dec s "x_" with
  | Specif.left _ => ret I
  | _ => raise exception
  end.
Qed.
