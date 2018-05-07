open Environ
open Evd
open EConstr

module ExistentialSet : Set.S with type elt = Term.existential_key

type elem_stack = (evar_map * CClosure.fconstr * CClosure.stack)
type elem = (evar_map * constr)

type data_stack =
  | Val of elem_stack
  | Err of elem_stack

type data =
  | Val of elem
  | Err of elem

val make_evar : evar_map -> env -> constr -> evar_map * constr (* used in metaCoqInterp *)

val run : (env * evar_map) -> constr -> data

module Goal : sig
  val mkTheGoal : types -> constr -> Evd.evar_map -> Environ.env -> (Evd.evar_map * constr)
  val evar_of_goal : Evd.evar_map -> Environ.env -> constr -> Evar.t option
end

(** DEBUG **)

type delta_stack_name =
  | Constant of Names.Constant.t
  | String of string

type delta_stack_entry = { name: delta_stack_name; entry_time: float; }
type delta_stack = delta_stack_entry list list

type ctxt = {env: Environ.env; renv: CClosure.fconstr; sigma: Evd.evar_map; nus: int; stack: CClosure.stack; delta_stack: delta_stack}

type vm = Code of CClosure.fconstr | Ret of CClosure.fconstr | Fail of CClosure.fconstr
        | Bind of CClosure.fconstr | Try of (Evd.evar_map * CClosure.stack * delta_stack * CClosure.fconstr)
        | Nu of (Names.Id.t * Environ.env * CClosure.fconstr)
        | Rem of (Environ.env * CClosure.fconstr * bool)

(* val run_fix : ctxt -> vm list -> CClosure.fconstr -> CClosure.fconstr array -> CClosure.fconstr -> CClosure.fconstr -> CClosure.fconstr array *)

val run' : ctxt -> vm list -> data_stack

val multi_subst : evar_map -> (int * constr) list -> constr -> constr

module Hypotheses : sig
  val from_coq_list : (Environ.env * Evd.evar_map) ->
    constr -> (constr * constr option * constr) list
end
