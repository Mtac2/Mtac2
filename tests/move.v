From MetaCoq Require Import MetaCoq.
Require Import Strings.String.


Inductive intro_base :=
| ipsimpl : intro_base
| ipdone : intro_base
| ipsimpldone : intro_base
| ipmaybevar : intro_base
| ipvar : string -> intro_base
| ipfold : string -> intro_base
| ipcase : list (list intro_base) -> intro_base.

Definition intro_pattern := list intro_base.

Section Parser.

Notation "a >>= b" := (match a with None => None | Some a' => b a' end) (at level 100).

Definition remove_hd_maybevar r :=
  match r with
  | (ipmaybevar :: r') => r'
  | _ => r
  end.

Fixpoint to_ip' (s : string) (hd : intro_pattern) {struct s} :=
  let hd' := remove_hd_maybevar hd in
  match s with
  | EmptyString => Some hd'
  | String "/" s1 =>
    match s1 with
    | EmptyString => None
    | String "=" s2 => to_ip' s2 (ipsimpl :: hd')
    | String "/" s2 =>
      match s2 with
      | String "=" s3 =>
        to_ip' s3 (ipsimpldone :: hd')
      | _ =>
        to_ip' s2 (ipdone :: hd')
      end
    | _ =>
      to_ip' s1 (ipfold "" :: hd')
    end
  | String " " s1 =>
    match hd with
    | ipfold "" :: _ => None
    | ipvar _ :: _ => to_ip' s1 (ipmaybevar :: hd)
    | ipfold _ :: _ => to_ip' s1 (ipmaybevar :: hd)
    | _ => to_ip' s1 hd
    end
  | String a s1 =>
    match hd with
    | ipfold b :: c => to_ip' s1 (ipfold (append b (String a "")) :: c)
    | ipvar b :: c => to_ip' s1 (ipvar (append b (String a "")) :: c)
    | ipmaybevar :: b => to_ip' s1 (ipvar (String a "") :: b)
    | _ => to_ip' s1 (ipvar (String a "") :: hd')
    end
  end.

Definition to_ip x :=
  to_ip' x [] >>= (fun r=> Some (rev r)).

Example test1 : to_ip "x" = Some [ipvar "x"].
Proof. reflexivity. Qed.

Example test2 : to_ip "x y" = Some [ipvar "x"; ipvar "y"].
Proof. reflexivity. Qed.

Example test3 : to_ip "xy" = Some [ipvar "xy"].
Proof. reflexivity. Qed.

Example test4 : to_ip "/xy" = Some [ipfold "xy"].
Proof. reflexivity. Qed.

Example test5 : to_ip "w /xy" = Some [ipvar "w"; ipfold "xy"].
Proof. reflexivity. Qed.

Example test6 : to_ip "//" = Some [ipdone].
Proof. reflexivity. Qed.

Example test7 : to_ip "// " = Some [ipdone].
Proof. reflexivity. Qed.

Example test8 : to_ip "//=" = Some [ipsimpldone].
Proof. reflexivity. Qed.

Example test9 : to_ip "// b" = Some [ipdone; ipvar "b"].
Proof. reflexivity. Qed.

Example test10 : to_ip "a // b" = Some [ipvar "a"; ipdone; ipvar "b"].
Proof. reflexivity. Qed.

Example test_ultimate : to_ip "/abc x // IH /=" =
  Some [ipfold "abc"; ipvar "x"; ipdone; ipvar "IH"; ipsimpl].
Proof. reflexivity. Qed.

End Parser.

Ltac done := intros; tauto || trivial || assumption || reflexivity.

Definition done := ltac "Top.done" [].

Definition build_tac :=
  List.map (fun ip=>
              match ip with
              | ipsimpl => simpl
              | ipsimpldone => simpl &> done
              | ipdone => done
              | ipvar x => intro_simpl x
              | ipfold x =>
                n <- get_reference x;
                let (_, e) := n : dyn in
                unfold e
              | _ => fun _ => failwith "unsupported"
              end).

Definition tac1_tac1 t u : tactic := fun g=>
  l <- t g;
  let u_is_idtac :=
      mtry unify_or_fail u idtac
      with _ => failwith "All goals solved" end in
  match l with
  | [] => u_is_idtac;; ret []
  | [g'] => mif is_open g' then
              open_and_apply u g'
            else u_is_idtac;; ret []
  | _ => failwith "More than one goal!"
  end.

Definition move s :=
  let oips := rcbv (to_ip s) in
  match oips with
  | Some ips =>
    List.fold_right tac1_tac1 idtac (build_tac ips)
  | None => fun _ => failwith "unsupported"
  end.

Goal forall P:Prop, id P -> P.
MProof.
  move "P". move "xP //".
Qed.

Goal forall P:Prop, id P -> P.
MProof.
  move "P /id /= //".
Qed.