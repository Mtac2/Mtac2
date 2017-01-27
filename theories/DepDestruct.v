From MetaCoq
     Require Export Mtac2 ListUtils Tactics ImportedTactics.
Import MtacNotations.
Import TacticsNotations.

Require Import Strings.String.
Require Import Lists.List.
Import ListNotations.

(** This is the [abs] from [MetaCoq] but first reducing the variable
    [x] (in case it is [id x] or some convertible term to a variable)
    *)
Definition abs {A} {P} (x:A) (t:P x) :=
  let y := reduce RedHNF x in abs_fun y t.

Notation redMatch := (reduce (RedWhd [RedMatch])).

(** [match_eq E P A] takes an equality of [T = S] and an element [A]
    of type [T], and returns [A] casted to [P S], but without any match
    (it reduces it). *)
Notation match_eq E P A :=
  (redMatch match E in _ = R return P R with eq_refl => A end).

(** A polymorphic function that returns the type of an element. *)
Definition type_of {A : Type} (x : A) : Type := A.


(** Types that can hold either a [Prop] or a [Type] *)
Section Sorts.

Inductive Sort : Type := SProp | SType.

(** Creates a fresh type according to [s] *)
Definition stype_of (s : Sort) : Type :=
  match s with SType => Type | SProp => Prop end.

(** When working with a sort [s], we cannot simply say "we have an
    element of [stype_of s]". For that, we make [selem_of T], where
    [T] is a [stype_of s]. *)
Definition selem_of {s : Sort} (x : stype_of s) : Type :=
  match s return stype_of s -> Type with
  | SType => fun x => x
  | SProp => fun x => x
  end x.

Fail Example CannotMakeAnElementOfaSort s (P : stype_of s) (x : P) := x.

Example WeCanWithElemOf s (P : stype_of s) (x : selem_of P) := x.


Definition ForAll
            {sort : Sort} {A : Type} :
  (A -> stype_of sort) -> stype_of sort :=
  match
    sort as sort'
    return ((A -> stype_of sort') -> stype_of sort')
  with
  | SProp => fun F => forall a : A, F a
  | SType => fun F => forall a : A, F a
  end.

Definition Fun {sort} {A : Type} :
  forall {F : A -> stype_of sort}, (forall a, selem_of (F a)) -> selem_of (ForAll F) :=
  match sort as sort' return
        forall {F : A -> stype_of sort'}, (forall a, selem_of (F a)) -> selem_of (ForAll F)
  with
  | SProp => fun _ f => f
  | SType => fun _ f => f
  end.

Definition App {sort} {A : Type} : forall {F : A -> _},  selem_of (ForAll (sort := sort) F) -> forall a, selem_of (F a) :=
  match sort as sort' return forall F, selem_of (ForAll (sort := sort') F) -> forall a, selem_of (F a) with
  | SProp => fun F f a => f a
  | SType => fun F f a => f a
  end.
End Sorts.

(** [ITele s] described a sorted type [forall x, ..., y, P] with
    [P] a [stype_of s]. *)
Inductive ITele (sort : Sort) : Type :=
| iBase : stype_of sort -> ITele sort
| iTele : forall {T : Type}, (T -> ITele sort) -> ITele sort.

Delimit Scope ITele_scope with IT.
Bind Scope ITele_scope with ITele.
Arguments iBase {_} _.
Arguments iTele {_ _%type} _.

(** [ATele it] describes a applied version of the type described in
    [it]. For instance, if [it] represents the type [T] equals to
    [forall x, ..., y, P], [ATele it] represents [T c1 ... cn]. *)
Inductive ATele {sort} : ITele sort -> Type :=
| aBase : forall {T: stype_of sort}, ATele (iBase T)
| aTele : forall {T : Type} {f : T -> ITele sort} (a:T), ATele (f a) -> ATele (iTele f).

Delimit Scope ATele_scope with AT.
Bind Scope ATele_scope with ATele.
Arguments ATele {_} _%IT.
Arguments aBase {_ _}.
Arguments aTele {_ _%type _} _%AT _.

(** Returns the type resulting from the [ATele] [args] *)
Fixpoint ITele_App {isort} {it : ITele isort} (args : ATele it) : stype_of isort :=
  match args with
  | @aBase _ T => T
  | @aTele _ _ f v args =>
    ITele_App args
  end.

(** Represents a constructor of an inductive type. *)
Inductive CTele {sort} (it : ITele sort) : Type :=
| cBase : forall {a : ATele it} (c : selem_of (ITele_App a)), CTele it
| cProd : forall {T : Type}, (T -> CTele it) -> CTele it.
Delimit Scope CTele_scope with CT.
Bind Scope CTele_scope with CTele.
Arguments CTele {_} _%IT.
Arguments cBase {_ _%AT} _ _.
Arguments cProd {_ _%type _} _.

(** Represents the result type of a branch. *)
Inductive RTele {isort} rsort : ITele isort -> Type :=
| rBase : forall {T : stype_of isort}, (selem_of T -> stype_of rsort) -> RTele rsort (iBase T)
| rTele : forall {T:Type} {f}, (forall (t : T), RTele rsort (f t)) -> RTele rsort (iTele f).
Delimit Scope RTele_scope with RT.
Bind Scope RTele_scope with RTele.
Arguments RTele {_} _ _%IT.
Arguments rBase {_ _ _} _.
Arguments rTele {_ _ _%type _} _.

Fixpoint RTele_App {isort rsort} {it : ITele isort} (rt : RTele rsort it) : forall (a : ATele it), selem_of (ITele_App a) -> stype_of rsort :=
  match rt in RTele _ it' return forall a' : ATele it', selem_of (ITele_App a') -> stype_of rsort
  with
  | @rBase _ _ T t =>
    fun (a : ATele (iBase T)) =>
      match a as a' in ATele it' return
            match it' with
            | iBase T' => (selem_of T' -> stype_of rsort) -> selem_of (ITele_App a') -> stype_of rsort
            | iTele f => True
            end
      with
      | aBase => fun f => f
      | aTele _ _ => I
      end t
  | rTele r =>
    let rec t := RTele_App (r t) in
    fun (a : ATele (iTele _)) =>
      match a as a' in ATele it' return
            match it' with
            | iBase _ => True
            | @iTele _ T' f => (forall (t:T') (a:ATele (f t)), selem_of (ITele_App a) -> _) -> selem_of (ITele_App a') -> stype_of rsort
            end
      with
      | aBase => I
      | aTele v a => fun rec => rec v a
      end rec
  end.

(* rt_T_weird1 and rt_T_weird2 will be equal to
    rt_T_type1 and rt_T_type2.
    Again, Coq does not realize that. So we leave them in for now.
  *)
Fixpoint RTele_Type {isort} {it : ITele isort} {rsort} (rt : RTele rsort it) : Type :=
match rt with
| @rBase _ _ s r =>
  (forall (t : selem_of s), stype_of rsort)
| rTele rt => forall t, RTele_Type (rt t)
end.

(* No idea why we still need rt_F_max_weird. *)
Fixpoint RTele_Fun {isort} {it : ITele isort} {rsort} (rt : RTele rsort it) : RTele_Type rt :=
  match rt with
  | rBase r => r
  | rTele rt => fun t => (RTele_Fun (rt t))
  end.

Notation reduce_novars := (reduce (RedStrong [RedBeta;RedMatch;RedFix;RedDeltaC;RedZeta])).

(* We need to handle Prop (maybe) *)
Fixpoint abstract_goal {isort} {rsort} {it : ITele isort} (args : ATele it) (G : stype_of rsort) :
  selem_of (ITele_App args) -> M (RTele rsort it) :=
  match args with
  | @aBase _ T => fun t =>
    let t := reduce_novars t in
    b <- is_var t;
    if b then
      let Gty := reduce RedNF (type_of G) in
      let T' := reduce RedNF (type_of t) in
      r <- @abs T' (fun _=>Gty) t G;
      let r := reduce RedNF (rBase r) in
      ret r
    else
      failwith "Argument t should be a variable"
  | @aTele _ _ f v args => fun t=>
      r <- abstract_goal args G t;
      let v := reduce_novars v in
      b <- is_var v;
      if b then
        let Gty := reduce RedNF (fun v'=>RTele rsort (f v')) in
        let T' := reduce RedNF (type_of v) in
        r <- @abs T' Gty v r;
        let r := reduce RedNF (rTele r) in
        ret r
      else
        failwith "All indices need to be variables"
  end.

Fixpoint get_type_of_branch {isort} {rsort} {it : ITele isort} (rt : RTele rsort it) (ct : CTele it) : stype_of rsort :=
  match ct with
  | cBase a t => RTele_App rt a t
  | cProd f => ForAll (fun t => get_type_of_branch rt (f t))
  end.

(* Get exactly `max` many arguments *)
Definition NotEnoughArguments : Exception. exact exception. Qed.
Fixpoint args_of_max (max : nat) : dyn -> M (list dyn) :=
    match max with
    | 0 => fun _ => ret nil
    | S max => fun d=>
      mmatch d with
      | [? T Q (t : T) (f : T -> Q)] Dyn (f t) => r <- args_of_max max (Dyn f); ret (app r (Dyn t :: nil))
                                                                           | _ =>
        T <- evar Type;
        P <- evar (T -> Type);
        f <- evar (forall x:T, P x);
        t <- evar T;
        let el := rhnf (d.(elem)) in
        b <- munify_cumul el (f t) UniCoq;
        if b then
          r <- args_of_max max (Dyn f); ret (app r (Dyn t :: nil))
        else
          print "Failed args_of_max while matching:";;
          print_term d;;
          raise NotEnoughArguments
      end
    end.

(** Given a inductive described in [it] and a list of elements [al],
    it returns the [ATele] describing the applied version of [it] with [al]. *)
Program Fixpoint get_ATele {isort} (it : ITele isort) (al : list dyn) {struct al} : M (ATele it) :=
    match it as it', al return M (ATele it') with
    | iBase T, nil => ret (@aBase _ T)
    | iTele f, t_dyn :: al =>
      (* We coerce the type of the element in [t_dyn] to match that expected by f *)
      t <- coerce (elem t_dyn);
      r <- (get_ATele (f t) al);
      ret (aTele t r)
    | _, _ => raise NoPatternMatches
    end.

Definition get_CTele_raw : forall {isort} (it : ITele isort) (nindx : nat) {A : stype_of isort}, selem_of A -> M (CTele it) :=
  fun isort it nindx =>
    mfix2 rec (A : stype_of isort) (a : selem_of A) : M (CTele it) :=
      B <- evar Type;
      F <- evar (B -> stype_of isort);
      oH <- munify A (ForAll F) UniCoq;
      match oH with
      | Some H =>
        let f := match_eq H selem_of a in
        n <- fresh_name "b";
        nu n None (fun b : B =>
          r <- rec (F b) (App f b);
          f' <- abs b r;
          ret (cProd f'))
      | None =>
        let Ty := stype_of isort in
        H <- unify_or_fail B Ty;
        let idB : B -> Ty := match_eq H (fun T=>B->T) (fun x=>x) in
        cumul_or_fail F idB;;
        let A_red := reduce RedHNF A in (* why the reduction here? *)
        args <- args_of_max nindx (Dyn A_red);
        atele <- get_ATele it args;
        a' <- @coerce _ (selem_of (ITele_App (isort := isort) atele)) a ;
        ret (cBase atele a')
end.

Definition get_CTele :=
  fun {isort} =>
    match isort as sort return forall {it : ITele sort} nindx {A : stype_of sort}, selem_of A -> M (CTele it) with
    | SProp => get_CTele_raw (isort := SProp)
    | SType => get_CTele_raw (isort := SType)
    end.

(** Given a goal, it returns its sorted version *)
Definition sort_goal {T : Type} (A : T) : M (sigT stype_of) :=
  mmatch T with
  | Prop => [H] let A_Prop := match_eq H id A in
                ret (existT _ SProp A_Prop)
  | Type => [H] let A_Type := match_eq H id A in
                ret (existT _ SType A_Type)
  end.

Definition get_ITele : forall {T : Type} (ind : T), M (nat * (sigT ITele)) :=
  mfix2 f (T : _) (ind : _) : M (nat * sigT ITele)%type :=
    mmatch T with
    | [? (A : Type) (F : A -> Type)] forall a, F a => [H]
      let indFun := match_eq H (fun x=>x) ind in
      name <- fresh_binder_name T;
      nu name None (fun a : A =>
        r <- f (F a) (indFun a);
        let (n, sit) := r in
        let (sort, it) := sit in
        f <- abs a it;
        ret (S n, existT _ sort (iTele f)))
    | Prop => [H]
      let indProp := match_eq H (fun x=>x) ind in
      ret (0, existT _ SProp (iBase (sort := SProp) indProp))
    | Type => [H]
      let indType := match_eq H (fun x=>x) ind in
      ret (0, existT _ (SType) (iBase (sort := SType) indType))
    | Set => [H]
      let indType := match_eq H (fun x=>x) ind in
      ret (0, existT _ (SType) (iBase (sort := SType) indType))
    | _ => failwith "Impossible ITele"
    end.

Definition get_ind {A : Type} (n : A) :
  M (nat * sigT (fun s => (ITele s)) * list dyn) :=
  r <- constrs A;
  let (indP, constrs) := r in
  sortit <- get_ITele (elem indP) : M (nat * sigT ITele);
  let nindx : nat := fst sortit in
  let (isort, it) := snd sortit in
  ret (nindx, existT _ _ it, constrs).

(* Compute ind type ATele *)
Definition get_ind_atele {isort} (it : ITele isort) (nindx : nat) (A : Type) :=
  indlist <- args_of_max nindx (Dyn A) : M (list dyn);
  atele <- get_ATele it indlist : M (ATele it);
  ret atele.

Definition new_destruct {A : Type} (n : A) : tactic :=
  fun (g : goal) =>
    ind <- get_ind n;
      let (nsortit, constrs) := ind in
      let (nindx, sortit) := nsortit in
      let (isort, it) := sortit in
      atele <- get_ind_atele it nindx A;
                 (* Compute CTeles *)
        cts <- mmap (fun c_dyn : dyn =>
                       let (dtype, delem) := c_dyn in
                       ty <- evar (stype_of isort);
                       b <- munify_cumul ty dtype UniCoq;
                       if b then
                         el <- evar (selem_of ty);
                         munify_cumul el delem UniCoq;;
                         get_CTele it nindx ty el
                       else
                         failwith "Couldn't unify the type of the inductive with the type of the constructor"
                    ) constrs;
                     (* Compute return type RTele *)
        gt <- goal_type g;
        rsG <- sort_goal gt;
        let (rsort, sG) := rsG in
        n' <- coerce n;
        rt <- abstract_goal atele sG n';
          let sg := reduce RedSimpl (map (
                        fun ct =>
                           (selem_of (get_type_of_branch rt ct))
                                       ) cts) in
          goals <- mmap (fun ty=> r <- evar ty; ret (Goal r)) sg;
          branches <- mmap goal_to_dyn goals;
          let tsg := reduce RedHNF (type_of sg) in
          let rrf := reduce RedSimpl (RTele_Fun rt) in
          let rrt := reduce RedSimpl (RTele_Type rt) in
          let type := reduce RedHNF (type_of n') in
          caseterm <- makecase {|
                       case_ind := type;
                       case_val := n';
                       case_return := Dyn rrf;
                       case_branches := branches
                     |};
          let gterm := dyn_to_goal caseterm in
          unify_or_fail gterm g;;
          ret goals.