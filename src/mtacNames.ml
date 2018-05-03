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

let constant_of_string e =
  let p = Libnames.path_of_string (metaCoq_module_name ^ "." ^ e) in
  let q = Libnames.qualid_of_path p in
  Nametab.locate_constant q

let isConstant sigma e c =
  match EConstr.destConst sigma c with
  | (n, _) ->
      (* let open Pp in
       * Feedback.msg_info (Names.Constant.debug_print n ++ Pp.str e); *)
      Names.Constant.equal n (constant_of_string e)
  | exception Term.DestKO -> false

let isFConstant e fc =
  match CClosure.fterm_of fc with
  | CClosure.FFlex (Names.ConstKey (n, _)) ->
      (* let open Pp in
       * Feedback.msg_info (Names.Constant.debug_print n ++ Pp.str e); *)
      Names.Constant.equal n (constant_of_string e)
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
