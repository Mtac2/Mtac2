Require Import MetaCoq.MetaCoq.

Inductive IPB := .

Inductive IP :=
| NoOp : IP
| B (binder : IPB -> unit) : IP
| C (cases : list LIP)
| R : RewriteDirection -> IP
| Done : IP
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
  | lnil => ret a
  | lcons b bs => f a b >> loop bs
  end.


Ltac done := intros; tauto || trivial || assumption || reflexivity.

Definition NotDone : Exception. exact exception. Qed.
Definition done := ltac "Top.done" [ ]%list or (fail NotDone).

Fixpoint do_intro lip : tactic :=
  match lip with
  | lnil => idtac
  | lcons ip lip =>
    match ip with
    | NoOp => idtac
    | B binder => fun g =>
      var <- get_binder_name binder;
      A <- evar Type;
      Tactics.intro_base var (fun a : A => do_intro lip) g
    | C ips =>
      destructn 0 &> (map do_intro ips) &> do_intro lip
    | R d =>
      introsn 1 &> (l <- hypotheses;
                    h <- hd_exception l;
                    let (_, var, _) := h : Hyp in
                    trewrite d [Dyn var] &> clear var)
                &> do_intro lip
    | Done =>
      fun g =>
        gs <- done g;
        gs' <- mmap (do_intro lip) gs;
        let gs'' := reduce (RedOnlyComplete [Dyn (@concat); Dyn (@app)]) (concat gs') in
        ret gs''
    end
  end.

Notation "'do_intro' s" := (do_intro s%IP) (at level 0).

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
