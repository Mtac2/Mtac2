open Environ
open Evd
open EConstr

module ExistentialSet : Set.S with type elt = Term.existential_key

type elem = (evar_map * constr)

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

type ctxt = {env: Environ.env; renv: constr; sigma: Evd.evar_map; nus: int; fixpoints: (EConstr.t, EConstr.t) Context.Named.pt}

type vm = Code of constr | Ret of constr | Fail of constr
        | Bind of constr | Try of (Evd.evar_map * constr)
        | Nu of (Names.Id.t * Environ.env * constr)
        | Fix

val run' : ctxt -> vm list -> data

val multi_subst : evar_map -> (int * constr) list -> constr -> constr

module Hypotheses : sig
  val from_coq_list : (Environ.env * Evd.evar_map) ->
    constr -> (constr * constr option * constr) list
end
