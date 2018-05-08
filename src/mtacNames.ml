open EConstr
open Termops

open Constrs

let metaCoq_module_name = "Mtac2.intf"

(* let mtac_constant_of_string name = constant_of_string (metaCoq_module_name ^ "." ^ name) *)

let mkBuilder e = ConstrBuilder.from_string (metaCoq_module_name ^ "." ^ e)
let mkUBuilder e = UConstrBuilder.from_string (metaCoq_module_name ^ "." ^ e)
let mkT_lazy = mkUBuilder "M.M.t"

let mkConstr e = ConstrBuilder.to_coq (ConstrBuilder.from_string (metaCoq_module_name ^ "." ^ e))
let mkUConstr e sigma env = UConstrBuilder.to_coq (UConstrBuilder.from_string (metaCoq_module_name ^ "." ^ e)) sigma env

let mkCase ind v ret branch sigma env =
  let c = UConstrBuilder.from_string "Case.mkCase" in
  UConstrBuilder.build_app c sigma env [|ind;v;ret;branch|]

let mkelem d sigma env =
  let c = UConstrBuilder.from_string "Dyn.elem" in
  UConstrBuilder.build_app c sigma env [|d|]

let mkdyn sigma env = UConstrBuilder.to_coq (UConstrBuilder.from_string "Dyn.dyn") sigma env

let mkDyn ty el sigma env =
  let c = UConstrBuilder.from_string "Dyn.Dyn" in
  UConstrBuilder.build_app c sigma env [|ty;el|]

(* dyn is expected to be Dyn ty el *)
let get_elem sigma dyn = (snd (destApp sigma dyn)).(1)
