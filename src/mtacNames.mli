val metaCoq_module_name : string
val mkConstr : string -> EConstr.constr Lazy.t
val mkUGlobal: string -> Names.GlobRef.t
val mkUConstr: string ->
  Evd.evar_map -> Environ.env -> Evd.evar_map * EConstr.constr
val mkBuilder: string -> Constrs.ConstrBuilder.t
val mkUBuilder: string -> Constrs.UConstrBuilder.t
val mkT_lazy : Evd.evar_map -> Environ.env -> Evd.evar_map * EConstr.constr
val isConstr : Evd.evar_map -> string -> EConstr.constr -> bool
val isUConstr: Evd.evar_map -> Environ.env -> string -> EConstr.t -> bool
val constant_of_string: string -> Names.Constant.t
val isConstant : Evd.evar_map -> Environ.env -> Names.Constant.t -> EConstr.t -> bool
val isFConstant : Environ.env -> Names.Constant.t -> CClosure.fconstr -> bool
val mkCase: EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t ->
  Evd.evar_map -> Environ.env -> Evd.evar_map * EConstr.t
val mkelem: EConstr.t -> Evd.evar_map -> Environ.env -> Evd.evar_map * EConstr.t
val mkdyn: Evd.evar_map -> Environ.env -> Evd.evar_map * EConstr.constr
val mkDyn: EConstr.t -> EConstr.t -> Evd.evar_map -> Environ.env -> Evd.evar_map * EConstr.t
val get_elem: Evd.evar_map -> EConstr.t -> EConstr.t
