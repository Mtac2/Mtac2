open Term
open Evd
open Environ

module ExistentialSet : Set.S with type elt = existential_key

type elem = (evar_map * ExistentialSet.t * constr)

type data =
  | Val of elem
  | Tac of (evar_map * ExistentialSet.t * unit Proofview.tactic * (elem -> data))
  | Err of elem

val run : (env * evar_map) -> constr -> data

module MetaCoqNames : sig
  val mkT_lazy : evar_map -> env -> (evar_map * constr)
end

val run' :
  Environ.env * Constr.constr * Evd.evar_map * (int * int) list ref list * ExistentialSet.t ->
  Term.constr -> data
