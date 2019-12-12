open MtacNames
open EConstr

type arg = CClosure.fconstr

type arg_any = arg
type arg_type = arg
type arg_fun = arg
type arg_string = arg
type arg_N = arg
type arg_bool = arg
type arg_mlist = arg
type arg_case = arg

type arg_fix1_ty = arg_type
type arg_fix1_val = arg_any

type arg_fix2_ty = arg_type * arg_type
type arg_fix2_val = arg_any * arg_any

type arg_fix3_ty = arg_type * arg_type * arg_type
type arg_fix3_val = arg_any * arg_any * arg_any

type arg_fix4_ty = arg_type * arg_type * arg_type * arg_type
type arg_fix4_val = arg_any * arg_any * arg_any * arg_any

type arg_fix5_ty = arg_type * arg_type * arg_type * arg_type * arg_type
type arg_fix5_val = arg_any * arg_any * arg_any * arg_any * arg_any

type 'a mconstr_head =
  | Mret : (arg_type * arg_any) mconstr_head
  | Mbind : (arg_type * arg_type * arg_any * arg_fun) mconstr_head
  | Mmtry' : (arg_type * arg_any * arg_fun) mconstr_head
  | Mraise' : (arg_type * arg_any) mconstr_head
  | Mfix1 : (arg_fix1_ty * arg_type * arg_fun * arg_fix1_val) mconstr_head
  | Mfix2 : (arg_fix2_ty * arg_type * arg_fun * arg_fix2_val) mconstr_head
  | Mfix3 : (arg_fix3_ty * arg_type * arg_fun * arg_fix3_val) mconstr_head
  | Mfix4 : (arg_fix4_ty * arg_type * arg_fun * arg_fix4_val) mconstr_head
  | Mfix5 : (arg_fix5_ty * arg_type * arg_fun * arg_fix5_val) mconstr_head
  | Mis_var : (arg_type * arg_any) mconstr_head
  | Mnu : (arg_type * arg_type * arg_string * arg_any * arg_fun) mconstr_head
  | Mnu_let : (arg_type * arg_type * arg_type * arg_string * arg_any * arg_fun) mconstr_head
  | Mabs_fun : (arg_type * arg_fun * arg_any * arg_any) mconstr_head
  | Mabs_let : (arg_type * arg_fun * arg_any * arg_any * arg_any) mconstr_head
  | Mabs_prod_prop : (arg_type * arg_any * arg_type) mconstr_head
  | Mabs_prod_type : (arg_type * arg_any * arg_type) mconstr_head
  | Mabs_fix : (arg_type * arg_any * arg_any * arg_N) mconstr_head
  | Mget_binder_name : (arg_type * arg_any) mconstr_head
  | Mremove : (arg_type * arg_type * arg_any * arg_any) mconstr_head
  | Mgen_evar : (arg_type * arg_any) mconstr_head
  | Mis_evar : (arg_type * arg_any) mconstr_head
  | Mhash : (arg_type * arg_any * arg_N) mconstr_head
  | Msolve_typeclasses
  | Mprint : (arg_string) mconstr_head
  | Mpretty_print : (arg_type * arg_any) mconstr_head
  | Mhyps
  | Mdestcase : (arg_type * arg_any) mconstr_head
  | Mconstrs : (arg_type * arg_any) mconstr_head
  | Mmakecase : (arg_case) mconstr_head
  | Munify : (arg_type * arg_type * arg_any * arg_any * arg_any * arg_fun * arg_fun) mconstr_head
  | Munify_univ : (arg_type * arg_type * arg_any) mconstr_head
  | Mget_reference : (arg_string) mconstr_head
  | Mget_var : (arg_string) mconstr_head
  | Mcall_ltac : (arg_any * arg_any * arg_string * arg_mlist) mconstr_head
  | Mlist_ltac
  | Mread_line
  | Mdecompose : (arg_type * arg_any) mconstr_head
  | Msolve_typeclass : (arg_type) mconstr_head
  | Mdeclare : (arg_any * arg_string * arg_bool * arg_type * arg_any) mconstr_head
  | Mdeclare_implicits : (arg_type * arg_any * arg_mlist) mconstr_head
  | Mos_cmd : (arg_string) mconstr_head
  | Mget_debug_exceptions
  | Mset_debug_exceptions : (arg_bool) mconstr_head
  | Mget_trace
  | Mset_trace : (arg_bool) mconstr_head
  | Mdecompose_app' : (arg_type * arg_fun * arg_any * arg_any * arg_any * arg_any * arg_any * arg_any) mconstr_head
  | Mdecompose_forallT : (arg_fun * arg_type * arg_any * arg_any) mconstr_head
  | Mdecompose_forallP : (arg_fun * arg_type * arg_any * arg_any) mconstr_head
  | Mdecompose_app'' : (arg_fun * arg_fun * arg_any * arg_any) mconstr_head
  | Mnew_timer : (arg_type * arg_any) mconstr_head
  | Mstart_timer : (arg_type * arg_any * arg_bool) mconstr_head
  | Mstop_timer : (arg_type * arg_any) mconstr_head
  | Mreset_timer : (arg_type * arg_any) mconstr_head
  | Mprint_timer : (arg_type * arg_any) mconstr_head
  | Mkind_of_term : (arg_type * arg_any) mconstr_head
  | Mreplace : (arg_type * arg_type * arg_type * arg_any * arg_any * arg_any) mconstr_head
  | Mdeclare_mind : (arg_any * arg_any * arg_any) mconstr_head
and mhead = | MHead : 'a mconstr_head -> mhead
and mconstr = | MConstr : 'a mconstr_head * 'a -> mconstr

let num_args_of_mconstr (type a) (mh : a mconstr_head) =
  match mh with
  | Mret -> 2
  | Mbind -> 4
  | Mmtry' -> 3
  | Mraise' -> 2
  | Mfix1 -> 2 + 2*1
  | Mfix2 -> 2 + 2*2
  | Mfix3 -> 2 + 2*3
  | Mfix4 -> 2 + 2*4
  | Mfix5 -> 2 + 2*5
  | Mis_var -> 2
  | Mnu -> 5
  | Mnu_let -> 6
  | Mabs_fun -> 4
  | Mabs_let -> 5
  | Mabs_prod_prop -> 3
  | Mabs_prod_type -> 3
  | Mabs_fix -> 4
  | Mget_binder_name -> 2
  | Mremove -> 4
  | Mgen_evar -> 2
  | Mis_evar -> 2
  | Mhash -> 3
  | Msolve_typeclasses -> 0
  | Mprint -> 1
  | Mpretty_print -> 2
  | Mhyps -> 0
  | Mdestcase -> 2
  | Mconstrs -> 2
  | Mmakecase -> 1
  | Munify -> 7
  | Munify_univ -> 3
  | Mget_reference -> 1
  | Mget_var -> 1
  | Mcall_ltac -> 4
  | Mlist_ltac -> 0
  | Mread_line -> 0
  | Mdecompose -> 2
  | Msolve_typeclass -> 1
  | Mdeclare -> 5
  | Mdeclare_implicits -> 3
  | Mos_cmd -> 1
  | Mget_debug_exceptions -> 0
  | Mset_debug_exceptions -> 1
  | Mget_trace -> 0
  | Mset_trace -> 1
  | Mdecompose_app' -> 8
  | Mdecompose_forallT -> 4
  | Mdecompose_forallP -> 4
  | Mdecompose_app'' -> 4
  | Mnew_timer -> 2
  | Mstart_timer -> 3
  | Mstop_timer -> 2
  | Mreset_timer -> 2
  | Mprint_timer -> 2
  | Mkind_of_term -> 2
  | Mreplace -> 6
  | Mdeclare_mind -> 3


let _mkconstr s = lazy (let (_, c) = mkUConstr ("M.M." ^ s) Evd.empty (Global.env ()) in c)
let _isconstr c h = eq_constr_nounivs Evd.empty (Lazy.force c) h
let isconstant n h = Names.Constant.equal (Lazy.force n) h

let constant_of_string s = lazy (constant_of_string ("M.M." ^ s))

let name_ret = constant_of_string "ret"
(* let mkret = mkconstr name_ret *)
let isret = isconstant name_ret

let name_bind = constant_of_string "bind"
(* let mkbind = mkconstr name_bind *)
let isbind = isconstant name_bind

let name_try' = constant_of_string "mtry'"
(* let mktry' = mkconstr name_try' *)
let istry' = isconstant name_try'

let name_raise = constant_of_string "raise'"
(* let mkraise = mkconstr name_raise *)
let israise = isconstant name_raise

let name_fix1 = constant_of_string "fix1"
(* let mkfix1 = mkconstr name_fix1 *)
let isfix1 = isconstant name_fix1

let name_fix2 = constant_of_string "fix2"
(* let mkfix2 = mkconstr name_fix2 *)
let isfix2 = isconstant name_fix2

let name_fix3 = constant_of_string "fix3"
(* let mkfix3 = mkconstr name_fix3 *)
let isfix3 = isconstant name_fix3

let name_fix4 = constant_of_string "fix4"
(* let mkfix4 = mkconstr name_fix4 *)
let isfix4 = isconstant name_fix4

let name_fix5 = constant_of_string "fix5"
(* let mkfix5 = mkconstr name_fix5 *)
let isfix5 = isconstant name_fix5

let name_is_var = constant_of_string "is_var"
(* let mkis_var = mkconstr name_is_var *)
let isis_var = isconstant name_is_var

let name_nu = constant_of_string "nu"
(* let mknu = mkconstr name_nu *)
let isnu = isconstant name_nu

let name_nu_let = constant_of_string "nu_let"
let isnu_let = isconstant name_nu_let

let name_abs_fun = constant_of_string "abs_fun"
(* let mkabs_fun = mkconstr name_abs_fun *)
let isabs_fun = isconstant name_abs_fun

let name_abs_let = constant_of_string "abs_let"
(* let mkabs_let = mkconstr name_abs_let *)
let isabs_let = isconstant name_abs_let

let name_abs_prod_prop = constant_of_string "abs_prod_prop"
(* let mkabs_prod_prop = mkconstr name_abs_prod_prop *)
let isabs_prod_prop = isconstant name_abs_prod_prop

let name_abs_prod_type = constant_of_string "abs_prod_type"
(* let mkabs_prod_type = mkconstr name_abs_prod_type *)
let isabs_prod_type = isconstant name_abs_prod_type

let name_abs_fix = constant_of_string "abs_fix"
(* let mkabs_fix = mkconstr name_abs_fix *)
let isabs_fix = isconstant name_abs_fix

let name_get_binder_name = constant_of_string "get_binder_name"
(* let mkget_binder_name = mkconstr name_get_binder_name *)
let isget_binder_name = isconstant name_get_binder_name

let name_remove = constant_of_string "remove"
(* let mkremove = mkconstr name_remove *)
let isremove = isconstant name_remove

let name_gen_evar = constant_of_string "gen_evar"
(* let mkgen_evar = mkconstr name_gen_evar *)
let isgen_evar = isconstant name_gen_evar

let name_is_evar = constant_of_string "is_evar"
(* let mkis_evar = mkconstr name_is_evar *)
let isis_evar = isconstant name_is_evar

let name_hash = constant_of_string "hash"
(* let mkhash = mkconstr name_hash *)
let ishash = isconstant name_hash

let name_solve_typeclasses = constant_of_string "solve_typeclasses"
(* let mksolve_typeclasses = mkconstr name_solve_typeclasses *)
let issolve_typeclasses = isconstant name_solve_typeclasses

let name_print = constant_of_string "print"
(* let mkprint = mkconstr name_print *)
let isprint = isconstant name_print

let name_pretty_print = constant_of_string "pretty_print"
(* let mkpretty_print = mkconstr name_pretty_print *)
let ispretty_print = isconstant name_pretty_print

let name_hyps = constant_of_string "hyps"
(* let mkhyps = mkconstr name_hyps *)
let ishyps = isconstant name_hyps

let name_destcase = constant_of_string "destcase"
(* let mkdestcase = mkconstr name_destcase *)
let isdestcase = isconstant name_destcase

let name_constrs = constant_of_string "constrs"
(* let mkconstrs = mkconstr name_constrs *)
let isconstrs = isconstant name_constrs

let name_makecase = constant_of_string "makecase"
(* let mkmakecase = mkconstr name_makecase *)
let ismakecase = isconstant name_makecase

let name_unify = constant_of_string "unify_cnt"
(* let mkunify = mkconstr name_unify *)
let isunify = isconstant name_unify

let name_unify_univ = constant_of_string "unify_univ"
(* let mkunify_univ = mkconstr name_unify_univ *)
let isunify_univ = isconstant name_unify_univ

let name_get_reference = constant_of_string "get_reference"
(* let mkget_reference = mkconstr name_get_reference *)
let isget_reference = isconstant name_get_reference

let name_get_var = constant_of_string "get_var"
(* let mkget_var = mkconstr name_get_var *)
let isget_var = isconstant name_get_var

let name_call_ltac = constant_of_string "call_ltac"
(* let mkcall_ltac = mkconstr name_call_ltac *)
let iscall_ltac = isconstant name_call_ltac

let name_list_ltac = constant_of_string "list_ltac"
(* let mklist_ltac = mkconstr name_list_ltac *)
let islist_ltac = isconstant name_list_ltac

let name_read_line = constant_of_string "read_line"
(* let mkread_line = mkconstr name_read_line *)
let isread_line = isconstant name_read_line

(* let name_break = constant_of_string "break"
 * (\* let mkbreak = mkconstr name_break *\)
 * let isbreak = isconstant name_break *)

let name_decompose = constant_of_string "decompose"
(* let mkdecompose = mkconstr name_decompose *)
let isdecompose = isconstant name_decompose

let name_solve_typeclass = constant_of_string "solve_typeclass"
(* let mksolve_typeclass = mkconstr name_solve_typeclass *)
let issolve_typeclass = isconstant name_solve_typeclass

let name_declare = constant_of_string "declare"
(* let mkdeclare = mkconstr name_declare *)
let isdeclare = isconstant name_declare

let name_declare_implicits = constant_of_string "declare_implicits"
(* let mkdeclare_implicits = mkconstr name_declare_implicits *)
let isdeclare_implicits = isconstant name_declare_implicits

let name_os_cmd = constant_of_string "os_cmd"
(* let mkos_cmd = mkconstr name_os_cmd *)
let isos_cmd = isconstant name_os_cmd

let name_get_debug_ex = constant_of_string "get_debug_exceptions"
(* let mkget_debug_ex = mkconstr name_get_debug_ex *)
let isget_debug_ex = isconstant name_get_debug_ex

let name_set_debug_ex = constant_of_string "set_debug_exceptions"
(* let mkset_debug_ex = mkconstr name_set_debug_ex *)
let isset_debug_ex = isconstant name_set_debug_ex

let name_get_trace = constant_of_string "get_trace"
(* let mkget_trace = mkconstr name_get_trace *)
let isget_trace = isconstant name_get_trace

let name_set_trace = constant_of_string "set_trace"
(* let mkset_trace = mkconstr name_set_trace *)
let isset_trace = isconstant name_set_trace

let name_decompose_app = constant_of_string "is_head"
(* let mkdecompose_app = mkconstr name_decompose_app *)
let isdecompose_app = isconstant name_decompose_app

let name_decompose_forallT = constant_of_string "decompose_forallT"
(* let mkdecompose_forallT = mkconstr name_decompose_forallT *)
let isdecompose_forallT = isconstant name_decompose_forallT

let name_decompose_forallP = constant_of_string "decompose_forallP"
(* let mkdecompose_forallP = mkconstr name_decompose_forallP *)
let isdecompose_forallP = isconstant name_decompose_forallP

let name_decompose_app'' = constant_of_string "decompose_app''"
(* let mkdecompose_app'' = mkconstr name_decompose_app'' *)
let isdecompose_app'' = isconstant name_decompose_app''

let name_new_timer = constant_of_string "new_timer"
(* let mknew_timer = mkconstr name_new_timer *)
let isnew_timer = isconstant name_new_timer

let name_start_timer = constant_of_string "start_timer"
(* let mkstart_timer = mkconstr name_start_timer *)
let isstart_timer = isconstant name_start_timer

let name_stop_timer = constant_of_string "stop_timer"
(* let mkstop_timer = mkconstr name_stop_timer *)
let isstop_timer = isconstant name_stop_timer

let name_reset_timer = constant_of_string "reset_timer"
(* let mkreset_timer = mkconstr name_reset_timer *)
let isreset_timer = isconstant name_reset_timer

let name_print_timer = constant_of_string "print_timer"
(* let mkprint_timer = mkconstr name_print_timer *)
let isprint_timer = isconstant name_print_timer

let name_kind_of_term = constant_of_string "kind_of_term"
(* let mkkind_of_term = mkconstr name_kind_of_term *)
let iskind_of_term = isconstant name_kind_of_term

let name_replace = constant_of_string "replace"
let isreplace = isconstant name_replace

let name_declare_mind = constant_of_string "declare_mind"
let isdeclare_mind = isconstant name_declare_mind


let mconstr_head_of h =
  match h with
  | _ when isret h ->
      MHead Mret
  | _ when isbind h ->
      MHead Mbind
  | _ when istry' h ->
      MHead Mmtry'
  | _ when israise h ->
      MHead Mraise'
  | _ when isfix1 h ->
      MHead Mfix1
  | _ when isfix2 h ->
      MHead Mfix2
  | _ when isfix3 h ->
      MHead Mfix3
  | _ when isfix4 h ->
      MHead Mfix4
  | _ when isfix5 h ->
      MHead Mfix5
  | _ when isis_var h ->
      MHead Mis_var
  | _ when isnu h ->
      MHead Mnu
  | _ when isnu_let h ->
      MHead Mnu_let
  | _ when isabs_fun h ->
      MHead Mabs_fun
  | _ when isabs_let h ->
      MHead Mabs_let
  | _ when isabs_prod_type h ->
      MHead Mabs_prod_type
  | _ when isabs_prod_prop h ->
      MHead Mabs_prod_prop
  | _ when isabs_fix h ->
      MHead Mabs_fix
  | _ when isget_binder_name h ->
      MHead Mget_binder_name
  | _ when isremove h ->
      MHead Mremove
  | _ when isgen_evar h ->
      MHead Mgen_evar
  | _ when isis_evar h ->
      MHead Mis_evar
  | _ when ishash h ->
      MHead Mhash
  | _ when issolve_typeclasses h ->
      MHead Msolve_typeclasses
  | _ when isprint h ->
      MHead Mprint
  | _ when ispretty_print h ->
      MHead Mpretty_print
  | _ when ishyps h ->
      MHead Mhyps
  | _ when isdestcase h ->
      MHead Mdestcase
  | _ when isconstrs h ->
      MHead Mconstrs
  | _ when ismakecase h ->
      MHead Mmakecase
  | _ when isunify h ->
      MHead Munify
  | _ when isunify_univ h ->
      MHead Munify_univ
  | _ when isget_reference h ->
      MHead Mget_reference
  | _ when isget_var h ->
      MHead Mget_var
  | _ when iscall_ltac h ->
      MHead Mcall_ltac
  | _ when islist_ltac h ->
      MHead Mlist_ltac
  | _ when isread_line h ->
      MHead Mread_line
  | _ when isdecompose h ->
      MHead Mdecompose
  | _ when issolve_typeclass h ->
      MHead Msolve_typeclass
  | _ when isdeclare h ->
      MHead Mdeclare
  | _ when isdeclare_implicits h ->
      MHead Mdeclare_implicits
  | _ when isos_cmd h ->
      MHead Mos_cmd
  | _ when isget_debug_ex h ->
      MHead Mget_debug_exceptions
  | _ when isset_debug_ex h ->
      MHead Mset_debug_exceptions
  | _ when isget_trace h ->
      MHead Mget_trace
  | _ when isset_trace h ->
      MHead Mset_trace
  | _ when isdecompose_app h ->
      MHead Mdecompose_app'
  | _ when isdecompose_forallT h ->
      MHead Mdecompose_forallT
  | _ when isdecompose_forallP h ->
      MHead Mdecompose_forallP
  | _ when isdecompose_app'' h ->
      MHead Mdecompose_app''
  | _ when isnew_timer h ->
      MHead Mnew_timer
  | _ when isstart_timer h ->
      MHead Mstart_timer
  | _ when isstop_timer h ->
      MHead Mstop_timer
  | _ when isreset_timer h ->
      MHead Mreset_timer
  | _ when isprint_timer h ->
      MHead Mprint_timer
  | _ when iskind_of_term h ->
      MHead Mkind_of_term
  | _ when isreplace h ->
      MHead Mreplace
  | _ when isdeclare_mind h ->
      MHead Mdeclare_mind
  | _ -> raise Not_found

let mconstr_head_opt h =
  match mconstr_head_of h with
  | mh -> Some(mh)
  | exception Not_found -> None

let mconstr_of (type a) args (h : a mconstr_head) =
  match h with
  | Mret -> MConstr (Mret,(args 0, args 1))
  | Mbind -> MConstr (Mbind, (args 0, args 1, args 2, args 3))
  | Mmtry' -> MConstr (Mmtry', (args 0, args 1, args 2))
  | Mraise' -> MConstr (Mraise', (args 0, args 1))
  | Mfix1 ->
      let n = 1 in
      let m = n+2 in
      let types = (args 0) in
      let ret = (args n) in
      let bod = (args (n+1)) in
      let vals = (args (m+0)) in
      MConstr (Mfix1, (types, ret, bod, vals))
  | Mfix2 ->
      let n = 2 in
      let m = n+2 in
      let types = (args 0, args 1) in
      let ret = (args n) in
      let bod = (args (n+1)) in
      let vals = (args (m+0), args (m+1)) in
      MConstr (Mfix2, (types, ret, bod, vals))
  | Mfix3 ->
      let n = 3 in
      let m = n+2 in
      let types = (args 0, args 1, args 2) in
      let ret = (args n) in
      let bod = (args (n+1)) in
      let vals = (args (m+0), args (m+1), args (m+2)) in
      MConstr (Mfix3, (types, ret, bod, vals))
  | Mfix4 ->
      let n = 4 in
      let m = n+2 in
      let types = (args 0, args 1, args 2, args 3) in
      let ret = (args n) in
      let bod = (args (n+1)) in
      let vals = (args (m+0), args (m+1), args (m+2), args (m+3)) in
      MConstr (Mfix4, (types, ret, bod, vals))
  | Mfix5 ->
      let n = 5 in
      let m = n+2 in
      let types = (args 0, args 1, args 2, args 3, args 4) in
      let ret = (args n) in
      let bod = (args (n+1)) in
      let vals = (args (m+0), args (m+1), args (m+2), args (m+3), args (m+4)) in
      MConstr (Mfix5, (types, ret, bod, vals))
  | Mis_var ->
      MConstr (Mis_var, (args 0, args 1))
  | Mnu ->
      MConstr (Mnu, (args 0, args 1, args 2, args 3, args 4))
  | Mnu_let ->
      MConstr (Mnu_let, (args 0, args 1, args 2, args 3, args 4, args 5))
  | Mabs_fun ->
      MConstr (Mabs_fun, (args 0, args 1, args 2, args 3))
  | Mabs_let ->
      MConstr (Mabs_let, (args 0, args 1, args 2, args 3, args 4))
  | Mabs_prod_type ->
      MConstr (Mabs_prod_type, (args 0, args 1, args 2))
  | Mabs_prod_prop ->
      MConstr (Mabs_prod_prop, (args 0, args 1, args 2))
  | Mabs_fix ->
      MConstr (Mabs_fix, (args 0, args 1, args 2, args 3))
  | Mget_binder_name ->
      MConstr (Mget_binder_name, (args 0, args 1))
  | Mremove ->
      MConstr (Mremove, (args 0, args 1, args 2, args 3))
  | Mgen_evar ->
      MConstr (Mgen_evar, (args 0, args 1))
  | Mis_evar ->
      MConstr (Mis_evar, (args 0, args 1))
  | Mhash ->
      MConstr (Mhash, (args 0, args 1, args 2))
  | Msolve_typeclasses ->
      MConstr (Msolve_typeclasses, ())
  | Mprint ->
      MConstr (Mprint, (args 0))
  | Mpretty_print ->
      MConstr (Mpretty_print, (args 0, args 1))
  | Mhyps ->
      MConstr (Mhyps, ())
  | Mdestcase ->
      MConstr (Mdestcase, (args 0, args 1))
  | Mconstrs ->
      MConstr (Mconstrs, (args 0, args 1))
  | Mmakecase ->
      MConstr (Mmakecase, (args 0))
  | Munify ->
      MConstr (Munify, (args 0, args 1, args 2, args 3, args 4, args 5, args 6))
  | Munify_univ ->
      MConstr (Munify_univ, (args 0, args 1, args 2))
  | Mget_reference ->
      MConstr (Mget_reference, (args 0))
  | Mget_var ->
      MConstr (Mget_var, (args 0))
  | Mcall_ltac ->
      MConstr (Mcall_ltac, (args 0, args 1, args 2, args 3))
  | Mlist_ltac ->
      MConstr (Mlist_ltac, ())
  | Mread_line ->
      MConstr (Mread_line, ())
  | Mdecompose ->
      MConstr (Mdecompose, (args 0, args 1))
  | Msolve_typeclass ->
      MConstr (Msolve_typeclass, (args 0))
  | Mdeclare ->
      MConstr (Mdeclare, (args 0, args 1, args 2, args 3, args 4))
  | Mdeclare_implicits ->
      MConstr (Mdeclare_implicits, (args 0, args 1, args 2))
  | Mos_cmd ->
      MConstr (Mos_cmd, (args 0))
  | Mget_debug_exceptions ->
      MConstr (Mget_debug_exceptions, ())
  | Mset_debug_exceptions ->
      MConstr (Mset_debug_exceptions, (args 0))
  | Mget_trace ->
      MConstr (Mget_trace, ())
  | Mset_trace ->
      MConstr (Mset_trace, (args 0))
  | Mdecompose_app' ->
      MConstr (Mdecompose_app', (args 0, args 1, args 2, args 3, args 4, args 5, args 6, args 7))
  | Mdecompose_forallT ->
      MConstr (Mdecompose_forallT, (args 0, args 1, args 2, args 3))
  | Mdecompose_forallP ->
      MConstr (Mdecompose_forallP, (args 0, args 1, args 2, args 3))
  | Mdecompose_app'' ->
      MConstr (Mdecompose_app'', (args 0, args 1, args 2, args 3))
  | Mnew_timer ->
      MConstr (Mnew_timer, (args 0, args 1))
  | Mstart_timer ->
      MConstr (Mstart_timer, (args 0, args 1, args 2))
  | Mstop_timer ->
      MConstr (Mstop_timer, (args 0, args 1))
  | Mreset_timer ->
      MConstr (Mreset_timer, (args 0, args 1))
  | Mprint_timer ->
      MConstr (Mprint_timer, (args 0, args 1))
  | Mkind_of_term ->
      MConstr (Mkind_of_term, (args 0, args 1))
  | Mreplace ->
      MConstr (Mreplace, (args 0, args 1, args 2, args 3, args 4, args 5))
  | Mdeclare_mind ->
      MConstr (Mdeclare_mind, (args 0, args 1, args 2))
