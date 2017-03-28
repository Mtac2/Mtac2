open Term
open Evd
open Environ

module ExistentialSet : Set.S with type elt = existential_key

type elem = (evar_map * constr)

type data =
  | Val of elem
  | Err of elem

val make_evar : evar_map -> env -> constr -> evar_map * constr (* used in metaCoqInterp *)

val run : (env * evar_map) -> constr -> data

module MetaCoqNames : sig
  val mkT_lazy : constr Lazy.t
end

module Goal : sig
  val mkTheGoal : types -> constr -> Evd.evar_map -> Environ.env -> (Evd.evar_map * constr)
  val evar_of_goal : Evd.evar_map -> Environ.env -> constr -> Evar.t option
end

(** DEBUG **)
val run' :
  Environ.env * constr * Evd.evar_map * int ->
  constr -> data

val multi_subst : (int * constr) list -> constr -> constr

module Hypotheses : sig
  val from_coq_list : (Environ.env * Evd.evar_map) ->
    Constr.constr ->
    (Term.constr * Constr.constr option * Constr.constr) list
end
