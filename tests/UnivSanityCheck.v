From Mtac2 Require Import Mtac2.

Print Universes "univ.txt".
Import M.
Require Import Coq.Numbers.BinNums.
Require Import Strings.String.

Definition find_cmd := "egrep ""Coq.*Mtac2.*"" univ.txt".
Definition count_cmd := find_cmd ++ " | wc -l  | tr -d ' '".
Definition assert_cmd := "[ $(" ++ count_cmd ++ ") = ""3"" ]".

Goal eval (os_cmd assert_cmd) = Z0.
  reflexivity.
Qed.