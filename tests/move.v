Require Import MetaCoq.
Require Import Strings.String.


Inductive intro_pattern : Type :=
| ipnil : intro_pattern
| ipcons : intro_base -> intro_pattern -> intro_pattern
with intro_base :=
| ipsimpl : intro_base
| ipdone : intro_base
| ipsimpldone : intro_base
| ipmaybevar : intro_base
| ipvar : string -> intro_base
| ipfold : string -> intro_base
| ipcase : list intro_pattern -> intro_base.


Section Parser.

Notation "a >>= b" := (match a with None => None | Some a' => b a' end) (at level 100).

Fixpoint token (s : string) :=
  match s with
  | EmptyString => ("", s)
  | String "/" _ => ("", s)
  | String "[" _ => ("", s)
  | String "]" _ => ("", s)
  | String " " s' => ("", s')
  | String a s' =>
    let (b, c) := token s' in
    (String a b, c)
  end.

Definition remove_hd_maybevar r :=
  match r with
  | ipcons ipmaybevar r' => r'
  | _ => r
  end.

Fixpoint to_ip' (s : string) (hd : intro_pattern) {struct s} :=
  let hd' := remove_hd_maybevar hd in
  match s with
  | EmptyString => Some hd'
  | String "/" s1 =>
    match s1 with
    | EmptyString => None
    | String "=" s2 => to_ip' s2 (ipcons ipsimpl hd')
    | String "/" s2 =>
      match s2 with
      | String "=" s3 =>
        to_ip' s3 (ipcons ipsimpldone hd')
      | _ =>
        to_ip' s2 (ipcons ipdone hd')
      end
    | _ =>
      to_ip' s1 (ipcons (ipfold "") hd')
    end
  | String " " s1 =>
    match hd with
    | ipcons (ipfold "") _ => None
    | ipcons (ipvar _) _ => to_ip' s1 (ipcons ipmaybevar hd)
    | ipcons (ipfold _) _ => to_ip' s1 (ipcons ipmaybevar hd)
    | _ => to_ip' s1 hd
    end
  | String a s1 =>
    match hd with
    | ipcons (ipfold b) c => to_ip' s1 (ipcons (ipfold (append b (String a ""))) c)
    | ipcons (ipvar b) c => to_ip' s1 (ipcons (ipvar (append b (String a ""))) c)
    | ipcons ipmaybevar b => to_ip' s1 (ipcons (ipvar (String a "")) b)
    | _ => to_ip' s1 (ipcons (ipvar (String a "")) hd')
    end
  end.

Fixpoint ipapp a b :=
  match a with
  | ipnil => b
  | ipcons x y => ipcons x (ipapp y b)
  end.

Fixpoint iprev i :=
  match i with
  | ipcons a b => ipapp (iprev b) (ipcons a ipnil)
  | _ => i
  end.

Definition to_ip x :=
  to_ip' x ipnil >>= (fun r=> Some (iprev r)).

Example test1 : to_ip "x" = Some (ipcons (ipvar "x") ipnil).
Proof. reflexivity. Qed.

Example test2 : to_ip "x y" = Some (ipcons (ipvar "x") (ipcons (ipvar "y") ipnil)).
Proof. reflexivity. Qed.

Example test3 : to_ip "xy" = Some (ipcons (ipvar "xy") ipnil).
Proof. reflexivity. Qed.

Example test4 : to_ip "/xy" = Some (ipcons (ipfold "xy") ipnil).
Proof. reflexivity. Qed.

Example test5 : to_ip "w /xy" = Some (ipcons (ipvar "w") (ipcons (ipfold "xy") ipnil)).
Proof. reflexivity. Qed.

Example test6 : to_ip "//" = Some (ipcons ipdone ipnil).
Proof. reflexivity. Qed.

Example test7 : to_ip "// " = Some (ipcons ipdone ipnil).
Proof. reflexivity. Qed.

Example test8 : to_ip "//=" = Some (ipcons ipsimpldone ipnil).
Proof. reflexivity. Qed.

Example test9 : to_ip "// b" = Some (ipcons ipdone (ipcons (ipvar "b") ipnil)).
Proof. reflexivity. Qed.

Example test10 : to_ip "a // b" = Some (ipcons (ipvar "a") (ipcons ipdone (ipcons (ipvar "b") ipnil))).
Proof. reflexivity. Qed.

Example test_ultimate : to_ip "/abc x // IH /=" =
  Some (ipcons (ipfold "abc") (ipcons (ipvar "x") (ipcons ipdone (ipcons (ipvar "IH") (ipcons ipsimpl ipnil))))).
Proof. reflexivity. Qed.
