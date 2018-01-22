open Evd
open Environ
open Term
open Names

module type RedFlagsSig = sig
  type reds
  type red_kind
  val fBETA : red_kind
  val fDELTA : red_kind
  val fETA : red_kind
  val fMATCH : red_kind
  val fFIX : red_kind
  val fCOFIX : red_kind
  val fZETA : red_kind
  val fCONST : constant -> red_kind
  val fVAR : Id.t -> red_kind
  val no_red : reds
  val red_add : reds -> red_kind -> reds
  val red_sub : reds -> red_kind -> reds
  val red_add_transparent : reds -> transparent_state -> reds
  val mkflags : red_kind list -> reds
  val red_set : reds -> red_kind -> bool
  val red_projection : reds -> projection -> bool
end

module RedFlags : RedFlagsSig

(** {6 Generic Optimized Reduction Function using Closures } *)

type contextual_reduction_function = env -> evar_map -> constr -> constr
type reduction_function = contextual_reduction_function

val clos_norm_flags : RedFlags.reds -> reduction_function
val clos_whd_flags : RedFlags.reds -> reduction_function
