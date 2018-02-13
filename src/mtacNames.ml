open EConstr
open Termops

open Constrs

let metaCoq_module_name = "Mtac2.intf"
let mkConstr e = Constr.mkConstr (metaCoq_module_name ^ "." ^ e)
let mkUConstr e = Constr.mkUConstr (metaCoq_module_name ^ "." ^ e)
let mkBuilder e = ConstrBuilder.from_string (metaCoq_module_name ^ "." ^ e)
let mkUBuilder e = UConstrBuilder.from_string (metaCoq_module_name ^ "." ^ e)
let mkT_lazy = mkUConstr "M.M.t"
let mkUConstr e = Constr.mkUConstr (metaCoq_module_name ^ "." ^ e)

let isConstr sigma e =
  let c = Lazy.force (mkConstr e) in
  eq_constr sigma c

let isUConstr sigma env e =
  let sigma, c = mkUConstr e sigma env in
  eq_constr_nounivs sigma c

let mkCase ind v ret branch sigma env =
  let sigma, c = mkUConstr "Case.mkCase" sigma env in
  sigma, mkApp(c, [|ind;v;ret;branch|])

let mkelem d sigma env =
  let sigma, c = mkUConstr "Dyn.elem" sigma env in
  sigma, mkApp(c, [|d|])

let mkdyn = mkUConstr "Dyn.dyn"

let mkDyn ty el sigma env =
  let sigma, c = mkUConstr "Dyn.Dyn" sigma env in
  sigma, mkApp(c, [|ty;el|])

(* dyn is expected to be Dyn ty el *)
let get_elem sigma dyn = (snd (destApp sigma dyn)).(1)
