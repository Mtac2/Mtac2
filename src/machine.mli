(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Constr
open EConstr
open Evd
(* open Environ *)

(** Reduction Functions. *)

(* exception Elimconst *)

(* (\** Machinery to customize the behavior of the reduction *\) *)
(* module ReductionBehaviour : sig *)
(*   type flag = [ `ReductionDontExposeCase | `ReductionNeverUnfold ] *)

(*   (\** [set is_local ref (recargs, nargs, flags)] *\) *)
(*   val set : *)
(*     bool -> Globnames.global_reference -> (int list * int * flag list) -> unit *)
(*   val get : *)
(*     Globnames.global_reference -> (int list * int * flag list) option *)
(*   val print : Globnames.global_reference -> Pp.std_ppcmds *)
(* end *)

(* (\** Option telling if reduction should use the refolding machinery of cbn *)
(*     (off by default) *\) *)
(* val get_refolding_in_reduction : unit -> bool *)
(* val set_refolding_in_reduction : bool -> unit *)

(* (\** {6 Support for reduction effects } *\) *)

(* type effect_name = string *)

(* (\* [declare_reduction_effect name f] declares [f] under key [name]; *)
(*    [name] must be a unique in "world". *\) *)
(* val declare_reduction_effect : effect_name -> *)
(*   (Environ.env -> Evd.evar_map -> Constr.constr -> unit) -> unit *)

(* (\* [set_reduction_effect cst name] declares effect [name] to be called when [cst] is found *\) *)
(* val set_reduction_effect : Globnames.global_reference -> effect_name -> unit *)

(* (\* [effect_hook env sigma key term] apply effect associated to [key] on [term] *\) *)
(* val reduction_effect_hook : Environ.env -> Evd.evar_map -> Constr.constr -> *)
(*   Constr.constr Lazy.t -> unit *)

(** {6 Machinery about a stack of unfolded constant }

    cst applied to params must convertible to term of the state applied to args
*)
module Cst_stack : sig
  type t
  val empty : t
  val add_param : constr -> t -> t
  val add_args : constr array -> t -> t
  val add_cst : constr -> t -> t
  val best_cst : t -> (constr * constr list) option
  val best_replace : Evd.evar_map -> constr -> t -> constr -> constr
  val reference : Evd.evar_map -> t -> Constant.t option
  val pr : t -> Pp.t
end

module Stack : sig
  type 'a app_node

  val pr_app_node : ('a -> Pp.t) -> 'a app_node -> Pp.t

  type cst_member =
    | Cst_const of pconstant
    | Cst_proj of Projection.t

  type 'a member =
    | App of 'a app_node
    | Case of case_info * 'a * 'a array * Cst_stack.t
    | Proj of int * int * Projection.t * Cst_stack.t
    | Fix of ('a, 'a) pfixpoint * 'a t * Cst_stack.t
    | Cst of cst_member * int (** current foccussed arg *) * int list (** remaining args *)
             * 'a t * Cst_stack.t
    | Shift of int
    | Update of 'a
  and 'a t = 'a member list

  val pr : ('a -> Pp.t) -> 'a t -> Pp.t

  val empty : 'a t
  val is_empty : 'a t -> bool
  val append_app : 'a array -> 'a t -> 'a t
  val decomp : 'a t -> ('a * 'a t) option

  val decomp_node_last : 'a app_node -> 'a t -> ('a * 'a t)

  val compare_shape : 'a t -> 'a t -> bool

  exception IncompatibleFold2
  (** [fold2 f x sk1 sk2] folds [f] on any pair of term in [(sk1,sk2)].
      @return the result and the lifts to apply on the terms
      @raise IncompatibleFold2 when [sk1] and [sk2] have incompatible shapes *)
  val fold2 : ('a -> constr -> constr -> 'a) -> 'a ->
    constr t -> constr t -> 'a * int * int
  val map : ('a -> 'a) -> 'a t -> 'a t
  val append_app_list : 'a list -> 'a t -> 'a t

  (** if [strip_app s] = [(a,b)], then [s = a @ b] and [b] does not
      start by App or Shift *)
  val strip_app : 'a t -> 'a t * 'a t
  (** @return (the nth first elements, the (n+1)th element, the remaining stack)  *)
  val strip_n_app : int -> 'a t -> ('a t * 'a * 'a t) option

  val not_purely_applicative : 'a t -> bool
  val list_of_app_stack : constr t -> constr list option

  val assign : 'a t -> int -> 'a -> 'a t
  val args_size : 'a t -> int
  val tail : int -> 'a t -> 'a t
  val nth : 'a t -> int -> 'a

  val best_state : evar_map -> constr * constr t -> Cst_stack.t -> constr * constr t
  val zip : ?refold:bool -> evar_map -> constr * constr t -> constr
end

(************************************************************************)

type state = constr * constr Stack.t

val whd_state_gen :
  CClosure.RedFlags.reds -> Environ.env -> (EConstr.t, EConstr.t) Context.Named.pt  -> Evd.evar_map -> state -> state * Cst_stack.t

val iterate_whd_gen : bool -> CClosure.RedFlags.reds ->
  Environ.env -> Evd.evar_map -> constr -> constr
