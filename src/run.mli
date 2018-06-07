open Environ
open Evd
open EConstr

module ExistentialSet : Set.S with type elt = Term.existential_key

type elem_stack = (evar_map * CClosure_copy.fconstr * CClosure_copy.stack)
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

type ctxt = {
  env: Environ.env;
  renv: CClosure_copy.fconstr;
  sigma: Evd.evar_map;
  nus: int;
  stack: CClosure_copy.stack;
  infos: CClosure_copy.fconstr CClosure_copy.infos;
}

type vm = Code of CClosure_copy.fconstr | Ret of CClosure_copy.fconstr | Fail of CClosure_copy.fconstr
        | Bind of CClosure_copy.fconstr | Try of (Evd.evar_map * CClosure_copy.stack * CClosure_copy.fconstr)
        | Nu of (Names.Id.t * Environ.env * CClosure_copy.fconstr)
        | Rem of (Environ.env * CClosure_copy.fconstr * bool)

(* val run_fix : ctxt -> vm list -> CClosure_copy.fconstr -> CClosure_copy.fconstr array -> CClosure_copy.fconstr -> CClosure_copy.fconstr -> CClosure_copy.fconstr array *)

val run' : ctxt -> vm list -> data_stack

val multi_subst : evar_map -> (int * constr) list -> constr -> constr

module Hypotheses : sig
  val from_coq_list : (Environ.env * Evd.evar_map) ->
    constr -> (constr * constr option * constr) list
end
