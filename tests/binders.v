Require Import Mtac2.Datatypes Mtac2.Mtac2.

Example nu_new_name_works : forall x:nat, 0 <= x.
MProof.
  M.nu (TheName "x") mNone (fun y=> M.abs_fun y (le_0_n y)).
Qed.

Example nu_existing_name_fails (x: nat) : forall y:nat, 0 <= y.
MProof.
Mtac Do Set_Debug_Exceptions.
  (mtry M.nu (TheName "x") mNone (fun y=>M.abs_fun y (le_0_n y)) with NameExistsInContext (TheName "x")=>M.ret _ end)%MC.
Abort.

Example nu_returning_x_fails (x: nat) : forall y:nat, 0 <= y.
MProof.
  (mtry M.nu (TheName "z") mNone (fun y=>M.ret y) with VarAppearsInValue => M.ret _ end)%MC.
Abort.

Example fresh_nu : True.
MProof.
  (\nu_f for (fun hopefully_unused : True => True) as (x : nat),
    n <- M.get_binder_name x;
    M.coerce (B:=n = "hopefully_unused") (@eq_refl _ n);;
    M.ret I
  )%MC.
Qed.

Example mirror_nu : True.
MProof.
  (* The type of [x] and  [y] is determined by the function given to [\nu_m] *)
  (\nu_m for (fun (hopefully_unused0 : True) (hopefully_unused1 : hopefully_unused0 = I) => True) as x y,
    n0 <- M.get_binder_name x;
    M.coerce (B:=n0 = "hopefully_unused0") (@eq_refl _ n0);;
    n1 <- M.get_binder_name y;
    M.coerce (B:=n1 = "hopefully_unused1") (@eq_refl _ n1);;
    M.ret I
  )%MC.
Qed.

Example mirror_nu_with_func : True.
MProof.
  (* The type of [x] and  [y] is determined by the function given to [\nu_m] *)
  (\nu_M for (fun (hopefully_unused0 : True) (hopefully_unused1 : hopefully_unused0 = I) => True) as x y ; f,
    M.unify_or_fail UniMatchNoRed f True;;
    n0 <- M.get_binder_name x;
    M.coerce (B:=n0 = "hopefully_unused0") (@eq_refl _ n0);;
    n1 <- M.get_binder_name y;
    M.coerce (B:=n1 = "hopefully_unused1") (@eq_refl _ n1);;
    M.ret I
  )%MC.
Qed.