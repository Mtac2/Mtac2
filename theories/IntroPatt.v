From Mtac2 Require Import List Base Tactics ImportedTactics.
Import Mtac2.List.ListNotations.
Import M.notations.
Import T.notations.

Inductive IPB := .

Inductive IP :=
| IntroNoOp : IP
| IntroB (binder : IPB -> unit) : IP
| IntroC (cases : mlist LIP)
| IntroR : RewriteDirection -> IP
| IntroDone
| IntroSimpl : IP
with LIP :=
| lnil : LIP
| lcons : IP -> LIP -> LIP.

Definition LIP_app : LIP -> LIP -> LIP :=
  fix f l1 :=
    match l1 with
    | lnil => fun l2 => l2
    | lcons ip l1 => fun l2 => lcons ip (f l1 l2)
    end.
Bind Scope IP_scope with IP.
Delimit Scope IP_scope with IP.

Definition LIP_rcons := fix f l1 := match l1 with | lnil => fun ip => ip | lcons ip1 l1 => fun ip => lcons ip1 (f l1 ip) end.
Coercion LIP_rcons : LIP >-> Funclass.
Coercion LIP_app : LIP >-> Funclass.
Notation "\ x .. z " := (lcons (IntroB (fun x => tt)) .. (lcons (IntroB (fun z => tt)) lnil) ..) (at level 20, x binder, z binder) : IP_scope.
Notation "\ x .. z C" := (lcons (IntroB (fun x => tt)) .. (lcons (IntroB (fun z => tt)) C) ..) (at level 20, x binder, z binder) : IP_scope.
Notation "'//'" := (lcons IntroDone lnil) : IP_scope.
Notation "'/='" := (lcons IntroSimpl lnil) : IP_scope.
Notation "~~" := (lcons IntroNoOp lnil) : IP_scope.
Notation "r>" := (lcons (IntroR RightRewrite) lnil) : IP_scope.
Notation "<l" := (lcons (IntroR LeftRewrite) lnil) : IP_scope.

Notation "[| ]" := (lcons (IntroC nil) lnil) : IP_scope.
Notation "[| x | .. | y ]" := (lcons (IntroC (mcons x .. (mcons y mnil) .. )) lnil) : IP_scope.

Close Scope IP.

Definition LIP_mfold_left {A} f :=
fix loop (l : LIP) (a : A) {struct l} : M A :=
  match l with
  | lnil => M.ret a
  | lcons b bs => f a b >>= loop bs
  end%MC.

Definition NotDone : Exception. exact exception. Qed.
Definition done : tactic :=
  intros ;; (tauto || T.assumption || T.reflexivity) || (T.raise NotDone).

Fixpoint mmap_plist (f: LIP -> tactic) (l: mlist LIP) : mlist tactic :=
  match l with
  | [m:] => [m:]
  | a :m: l' => f a :m: mmap_plist f l'
  end.

Definition to_tactic (ip : IP) (do_intro : LIP -> tactic) : tactic :=
  match ip return tactic with
  | IntroNoOp => T.idtac
  | IntroB binder =>
    var <- M.get_binder_name binder;
    T.intro_simpl var
  | IntroC [m:] => T.destructn 0
  | IntroC ips =>
    T.destructn 0 &> mmap_plist do_intro ips
  | IntroR d =>
    T.introsn 1;;
    l <- M.hyps;
    h <- M.hd l;
    let (_, var, _) := h : Hyp in
    trewrite d [m:Dyn var];;
    T.clear var
  | IntroDone => done
  | IntroSimpl => simpl
  end.

Definition do_intro :  LIP -> tactic :=
  mfix2 do_intro (lip : LIP) (g : goal) : M (mlist (unit * goal)) :=
  (match lip return tactic with
  | lnil => T.idtac
  | lcons ip lnil => to_tactic ip do_intro
  | lcons ip lip => to_tactic ip do_intro ;; do_intro lip
  end%tactic) g.

Notation "'pintro' s" := (do_intro s%IP) (at level 100).
Notation "'pintros' l1 .. ln" := (do_intro (LIP_app l1%IP .. (LIP_app ln%IP lnil) ..)) (at level 0).

Notation "[i: l1 | .. | ln ]" := (mcons (pintros l1) ( .. (mcons (pintros ln) mnil) ..)) (at level 0).

Close Scope IP.
