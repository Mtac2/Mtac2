open Constr
open EConstr
open Termops

open Constrs

let metaCoq_module_name = "Mtac2.intf"
let mkConstr e = Constrs.mkConstr (metaCoq_module_name ^ "." ^ e)
let mkUGlobal e = Constrs.mkUGlobal (metaCoq_module_name ^ "." ^ e)
let mkUConstr e = Constrs.mkUConstr (metaCoq_module_name ^ "." ^ e)
let mkBuilder e = ConstrBuilder.from_string (metaCoq_module_name ^ "." ^ e)
let mkUBuilder e = UConstrBuilder.from_string (metaCoq_module_name ^ "." ^ e)
let mkT_lazy = mkUConstr "M.M.t"
let mkUConstr e = Constrs.mkUConstr (metaCoq_module_name ^ "." ^ e)

let isConstr sigma e =
  let c = Lazy.force (mkConstr e) in
  eq_constr sigma c

let isUConstr sigma env e =
  let sigma, c = mkUConstr e sigma env in
  eq_constr_nounivs sigma c

let constant_of_string e =
  let full_name = metaCoq_module_name ^ "." ^ e in
  let p = Libnames.path_of_string full_name in
  (* let q = Libnames.qualid_of_path p in *)
  match Nametab.global_of_path p with
  | Globnames.ConstRef (c) -> c
  | _ -> raise Not_found

let isConstant sigma const c =
  match EConstr.kind sigma c with
  | Const (n, _) -> Names.Constant.equal n const
  | _ -> false

let isFConstant const fc =
  match CClosure.fterm_of fc with
  | CClosure.FFlex (Names.ConstKey (n, _)) ->
      Names.Constant.equal n const
  | _ -> false

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
