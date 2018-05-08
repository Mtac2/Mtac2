val metaCoq_module_name : string
(* val mtac_constant_of_string : string -> Names.Constant.t *)
val mkBuilder: string -> Constrs.ConstrBuilder.t
val mkUBuilder: string -> Constrs.UConstrBuilder.t
val mkConstr : string -> EConstr.t
val mkUConstr : string -> Evd.evar_map -> Environ.env -> Evd.evar_map * EConstr.t
val mkT_lazy : Constrs.UConstrBuilder.t
val mkCase: EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t ->
  Evd.evar_map -> Environ.env -> Evd.evar_map * EConstr.t
val mkelem: EConstr.t -> Evd.evar_map -> Environ.env -> Evd.evar_map * EConstr.t
val mkdyn: Evd.evar_map -> Environ.env -> Evd.evar_map * EConstr.constr
val mkDyn: EConstr.t -> EConstr.t -> Evd.evar_map -> Environ.env -> Evd.evar_map * EConstr.t
val get_elem: Evd.evar_map -> EConstr.t -> EConstr.t
