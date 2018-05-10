open EConstr
open Termops

open Constrs

let metaCoq_module_name = "Mtac2.intf"

(* let mtac_constant_of_string name = constant_of_string (metaCoq_module_name ^ "." ^ name) *)

let mkBuilder e = ConstrBuilder.from_string (metaCoq_module_name ^ "." ^ e)
let mkUBuilder e = UConstrBuilder.from_string (metaCoq_module_name ^ "." ^ e)
let mkT_lazy = mkUBuilder "M.M.t"

let mkConstr e =
  let builder = ConstrBuilder.from_string (metaCoq_module_name ^ "." ^ e) in
  ConstrBuilder.to_coq builder
let mkUConstr e =
  let builder = (UConstrBuilder.from_string (metaCoq_module_name ^ "." ^ e)) in
  UConstrBuilder.to_coq builder

let mkCase_builder = mkUBuilder "Case.mkCase"
let mkCase ind v ret branch sigma env =
  UConstrBuilder.build_app mkCase_builder sigma env [|ind;v;ret;branch|]

let mkelem_builder = mkUBuilder "Dyn.elem"
let mkelem d sigma env =
  UConstrBuilder.build_app mkelem_builder sigma env [|d|]

let mkdyn_builder = mkUBuilder "Dyn.dyn"
let mkdyn sigma env = UConstrBuilder.to_coq mkdyn_builder sigma env

let mkDyn_builder = mkUBuilder "Dyn.Dyn"
let mkDyn ty el sigma env =
  UConstrBuilder.build_app mkDyn_builder sigma env [|ty;el|]

(* dyn is expected to be Dyn ty el *)
let get_elem sigma dyn = (snd (destApp sigma dyn)).(1)
