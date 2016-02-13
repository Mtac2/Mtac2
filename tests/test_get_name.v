Require Import MetaCoq.MetaCoq.
Import MetaCoqNotations.
Require Import MetaCoq.LtacEmu.
Import LtacEmuNotations.

Goal True.
MProof.
  s <- get_name (fun name:nat=>name);
  match String.string_dec s "name" with
  | Specif.left _ => ret I
  | _ => raise exception
  end.
Qed.

Goal forall x:nat, True.
MProof.
  refine (fun name=>_).
  s <- get_name name;
  match String.string_dec s "name" with
  | Specif.left _ => ret I
  | _ => raise exception
  end.
Qed.

Goal True.
MProof.
  tnu "name" (fun x:nat=>
  s <- get_name x;
  match String.string_dec s "name" with
  | Specif.left _ => ret I
  | _ => raise exception
  end).
Qed.

Goal True.
MProof.
  r <- tnu "name" (fun x:nat=>abs x x);
  s <- get_name r;
  match String.string_dec s "name" with
  | Specif.left _ => ret I
  | _ => raise exception
  end.
Qed.