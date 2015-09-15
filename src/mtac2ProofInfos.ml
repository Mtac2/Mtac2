(**
   This module concerns the state of the proof tree
*)

(**  *)
type split_tree=
    Skip_patt of Names.Id.Set.t * split_tree
  | Split_patt of Names.Id.Set.t * Names.inductive * (bool array * (Names.Id.Set.t * split_tree) option) array
  | Close_patt of split_tree
  | End_patt of (Names.Id.t * (int * int))

(**  *)
type elim_kind =
    EK_dep of split_tree
  | EK_nodep
  | EK_unknown

type recpath = int option*Declarations.wf_paths

type per_info =
  {per_casee:Term.constr;
   per_ctype:Term.types;
   per_ind:Names.inductive;
   per_pred:Term.constr;
   per_args:Term.constr list;
   per_params:Term.constr list;
   per_nparams:int;
   per_wf:recpath}

type elim_type =
    ET_Case_analysis
  | ET_Induction

type stack_info =
    Per of elim_type * per_info * elim_kind * Names.Id.t list
  | Suppose_case
  | Claim
  | Focus_claim

type pm_info =
  { pm_stack : stack_info list}

(** Create a new field in datatype used to store additional information in evar maps*)
let info = Evd.Store.field ()

(** Get back the infos of a given goal *)
let get_info sigma gl=
  match Evd.Store.get (Goal.V82.extra sigma gl) info with
  | None ->  invalid_arg "get_info"
  | Some pm -> pm

let get_stack pts =
  let { Evd.it = goals ; sigma = sigma } = Proof.V82.subgoals pts in
  let info = get_info sigma (List.hd goals) in
  info.pm_stack

let proof_focus = Proof.new_focus_kind ()
let proof_cond = Proof.no_cond proof_focus

(** focus on the proof *)
let focus p =
  let inf = get_stack p in
  Printf.printf "____focus\n%!";
  Proof_global.simple_with_current_proof
    (fun _ -> Proof.focus proof_cond inf 1)

(** unfocus *)
let maximal_unfocus () =
  Proof_global.simple_with_current_proof
    (fun _ -> Proof.maximal_unfocus proof_focus)
