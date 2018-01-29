open MtacNames
open EConstr

let mkconstr s = lazy (let (_, c) = mkUConstr ("M." ^ s) Evd.empty (Global.env ()) in c)
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
