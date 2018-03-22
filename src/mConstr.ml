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
  | Munify : (arg_type * arg_any * arg_any * arg_any) mconstr_head
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
  | Mdecompose_app' : (arg_type * arg_fun * arg_any * arg_any * arg_any * arg_any * arg_any) mconstr_head
  | Mnew_timer : (arg_type * arg_any) mconstr_head
  | Mstart_timer : (arg_type * arg_any * arg_bool) mconstr_head
  | Mstop_timer : (arg_type * arg_any) mconstr_head
  | Mreset_timer : (arg_type * arg_any) mconstr_head
  | Mprint_timer : (arg_type * arg_any) mconstr_head
  | Mkind_of_term : (arg_type * arg_any) mconstr_head
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
  | Munify -> 4
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
  | Mdecompose_app' -> 7
  | Mnew_timer -> 2
  | Mstart_timer -> 3
  | Mstop_timer -> 2
  | Mreset_timer -> 2
  | Mprint_timer -> 2
  | Mkind_of_term -> 2


let mkconstr s = lazy (let (_, c) = mkUConstr ("M.M." ^ s) Evd.empty (Global.env ()) in c)
let isconstr c h = eq_constr_nounivs Evd.empty (Lazy.force c) h

let mkret = mkconstr "ret"
let isret  = isconstr mkret

let mkbind = mkconstr "bind"
let isbind  = isconstr mkbind

let mktry' = mkconstr "mtry'"
let istry'  = isconstr mktry'

let mkraise = mkconstr "raise'"
let israise  = isconstr mkraise

let mkfix1 = mkconstr "fix1"
let isfix1  = isconstr mkfix1

let mkfix2 = mkconstr "fix2"
let isfix2  = isconstr mkfix2

let mkfix3 = mkconstr "fix3"
let isfix3  = isconstr mkfix3

let mkfix4 = mkconstr "fix4"
let isfix4  = isconstr mkfix4

let mkfix5 = mkconstr "fix5"
let isfix5  = isconstr mkfix5

let mkis_var = mkconstr "is_var"
let isis_var  = isconstr mkis_var

let mknu = mkconstr "nu"
let isnu  = isconstr mknu

let mkabs_fun = mkconstr "abs_fun"
let isabs_fun  = isconstr mkabs_fun

let mkabs_let = mkconstr "abs_let"
let isabs_let  = isconstr mkabs_let

let mkabs_prod_prop = mkconstr "abs_prod_prop"
let isabs_prod_prop  = isconstr mkabs_prod_prop

let mkabs_prod_type = mkconstr "abs_prod_type"
let isabs_prod_type  = isconstr mkabs_prod_type

let mkabs_fix = mkconstr "abs_fix"
let isabs_fix  = isconstr mkabs_fix

let mkget_binder_name = mkconstr "get_binder_name"
let isget_binder_name  = isconstr mkget_binder_name

let mkremove = mkconstr "remove"
let isremove  = isconstr mkremove

let mkgen_evar = mkconstr "gen_evar"
let isgen_evar  = isconstr mkgen_evar

let mkis_evar = mkconstr "is_evar"
let isis_evar  = isconstr mkis_evar

let mkhash = mkconstr "hash"
let ishash  = isconstr mkhash

let mksolve_typeclasses = mkconstr "solve_typeclasses"
let issolve_typeclasses  = isconstr mksolve_typeclasses

let mkprint = mkconstr "print"
let isprint  = isconstr mkprint

let mkpretty_print = mkconstr "pretty_print"
let ispretty_print  = isconstr mkpretty_print

let mkhyps = mkconstr "hyps"
let ishyps  = isconstr mkhyps

let mkdestcase = mkconstr "destcase"
let isdestcase  = isconstr mkdestcase

let mkconstrs = mkconstr "constrs"
let isconstrs  = isconstr mkconstrs

let mkmakecase = mkconstr "makecase"
let ismakecase  = isconstr mkmakecase

let mkunify = mkconstr "unify"
let isunify  = isconstr mkunify

let mkunify_univ = mkconstr "unify_univ"
let isunify_univ  = isconstr mkunify_univ

let mkget_reference = mkconstr "get_reference"
let isget_reference  = isconstr mkget_reference

let mkget_var = mkconstr "get_var"
let isget_var  = isconstr mkget_var

let mkcall_ltac = mkconstr "call_ltac"
let iscall_ltac  = isconstr mkcall_ltac

let mklist_ltac = mkconstr "list_ltac"
let islist_ltac  = isconstr mklist_ltac

let mkread_line = mkconstr "read_line"
let isread_line  = isconstr mkread_line

let mkbreak = mkconstr "break"
let isbreak  = isconstr mkbreak

let mkdecompose = mkconstr "decompose"
let isdecompose  = isconstr mkdecompose

let mksolve_typeclass = mkconstr "solve_typeclass"
let issolve_typeclass  = isconstr mksolve_typeclass

let mkdeclare = mkconstr "declare"
let isdeclare  = isconstr mkdeclare

let mkdeclare_implicits = mkconstr "declare_implicits"
let isdeclare_implicits  = isconstr mkdeclare_implicits

let mkos_cmd = mkconstr "os_cmd"
let isos_cmd  = isconstr mkos_cmd

let mkget_debug_ex = mkconstr "get_debug_exceptions"
let isget_debug_ex  = isconstr mkget_debug_ex

let mkset_debug_ex = mkconstr "set_debug_exceptions"
let isset_debug_ex  = isconstr mkset_debug_ex

let mkget_trace = mkconstr "get_trace"
let isget_trace  = isconstr mkget_trace

let mkset_trace = mkconstr "set_trace"
let isset_trace  = isconstr mkset_trace

let mkdecompose_app = mkconstr "decompose_app'"
let isdecompose_app = isconstr mkdecompose_app

let mknew_timer = mkconstr "new_timer"
let isnew_timer = isconstr mknew_timer

let mkstart_timer = mkconstr "start_timer"
let isstart_timer = isconstr mkstart_timer

let mkstop_timer = mkconstr "stop_timer"
let isstop_timer = isconstr mkstop_timer

let mkreset_timer = mkconstr "reset_timer"
let isreset_timer = isconstr mkreset_timer

let mkprint_timer = mkconstr "print_timer"
let isprint_timer = isconstr mkprint_timer

let mkkind_of_term = mkconstr "kind_of_term"
let iskind_of_term = isconstr mkkind_of_term

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
  | _ when isgen_evar h->
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
  | _ when isnew_timer h ->
      MHead Mnew_timer
  | _ when isstart_timer h ->
      MHead Mnew_timer
  | _ when isstop_timer h ->
      MHead Mnew_timer
  | _ when isreset_timer h ->
      MHead Mnew_timer
  | _ when isprint_timer h ->
      MHead Mnew_timer
  | _ when iskind_of_term h ->
      MHead Mkind_of_term
  | _ -> raise Not_found


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
      MConstr (Munify, (args 0, args 1, args 2, args 3))
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
      MConstr (Mdecompose_app', (args 0, args 1, args 2, args 3, args 4, args 5, args 6))
  | Mnew_timer ->
      MConstr (Mnew_timer, (args 0, args 1))
  | Mnew_timer ->
      MConstr (Mnew_timer, (args 0, args 1))
  | Mnew_timer ->
      MConstr (Mnew_timer, (args 0, args 1))
  | Mnew_timer ->
      MConstr (Mnew_timer, (args 0, args 1))
  | Mnew_timer ->
      MConstr (Mnew_timer, (args 0, args 1))
  | Mkind_of_term ->
      MConstr (Mkind_of_term, (args 0, args 1))
  | _ -> raise Not_found
