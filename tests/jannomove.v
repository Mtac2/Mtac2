From MetaCoq Require Import MetaCoq Datatypes.
Import MetaCoq.List.ListNotations.

Inductive IPB := .

Inductive IP :=
| NoOp : IP
| B (binder : IPB -> unit) : IP
| C (cases : list LIP)
| R : RewriteDirection -> IP
| Done
| Simpl : IP
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
Notation "\ x .. z " := (lcons (B (fun x => tt)) .. (lcons (B (fun z => tt)) lnil) ..) (at level 20, x binder, z binder) : IP_scope.
Notation "\ x .. z C" := (lcons (B (fun x => tt)) .. (lcons (B (fun z => tt)) C) ..) (at level 20, x binder, z binder) : IP_scope.
Notation "'//'" := (lcons Done lnil) : IP_scope.
Notation "'/='" := (lcons Simpl lnil) : IP_scope.
Notation "' l1 .. ln" := (LIP_app l1 .. (LIP_app ln lnil) ..) (at level 0) : IP_scope.
Notation "~~" := (lcons NoOp lnil) : IP_scope.
Notation "r>" := (lcons (R RightRewrite) lnil) : IP_scope.
Notation "<l" := (lcons (R LeftRewrite) lnil) : IP_scope.

Notation "[| ]" := (lcons (C nil) lnil) : IP_scope.
Notation "[| x | .. | y ]" := (lcons (C ( cons x .. (cons y nil) .. )) lnil) : IP_scope.

Close Scope IP.

Definition LIP_mfold_left {A} f :=
fix loop (l : LIP) (a : A) {struct l} : M A :=
  match l with
  | lnil => M.ret a
  | lcons b bs => f a b >>= loop bs
  end%MC.

Definition NotDone : Exception. exact exception. Qed.
Definition done : tactic :=
  intros ;; (tauto or T.assumption or T.reflexivity) or (T.raise NotDone).

Fixpoint mmap_plist (f: LIP -> tactic) (l: list LIP) : list tactic :=
  match l with
  | nil => [m:]
  | cons a l' => f a :: mmap_plist f l'
  end.

Definition to_tactic (ip : IP) (do_intro : LIP -> tactic) : tactic :=
  match ip return tactic with
  | NoOp => T.idtac
  | B binder =>
    var <- M.get_binder_name binder;
    T.intro_simpl var
  | C ips =>
    T.destructn 0 &> mmap_plist do_intro ips
  | R d =>
    T.introsn 1;;
    l <- M.hyps;
    h <- M.hd l;
    let (_, var, _) := h : Hyp in
    trewrite d [m:Dyn var];;
    T.clear var
  | Done => done
  | Simpl => simpl
  end.

Definition do_intro :  LIP -> tactic :=
  mfix2 do_intro (lip : LIP) (g : goal) : M (list (unit * goal)) :=
  (match lip return tactic with
  | lnil => T.idtac
  | lcons ip lnil => to_tactic ip do_intro
  | lcons ip lip => to_tactic ip do_intro ;; do_intro lip
  end%tactic) g.

Notation "'do_intro' s" := (do_intro s%IP) (at level 100).

Close Scope IP.

Goal True -> True -> True.
MProof.
  do_intro '\x y //.
Qed.

Goal nat -> True -> True.
MProof.
  do_intro '[| ~~ | \x ] \t //.
Qed.

Goal forall x y z : nat, x = y -> x + z = y + z.
MProof.
  do_intro '\x y z r> //.
Qed.

Goal forall x y z : nat, x = y -> x + z = y + z.
MProof.
  do_intro '\x y z <l //.
Qed.

Goal forall x y z : nat, x + z = y + z.
MProof.
  Fail do_intro '\x y z //.
Abort.

Goal forall x z : nat, (forall y, y+0 = y) -> x + z = z + x.
MProof.
  do_intro '[| ~~ | \x'] [| ~~ | \z'] /=.
  - do_intro '//.
  - do_intro 'r> //.
  - do_intro 'r> //.
Abort.
