open Constr
open EConstr
open Reductionops

let reduce_value = Tacred.compute

let decompose_appvect sigma c =
  match kind sigma c with
  | App (f,cl) -> (f, cl)
  | _ -> (c,[||])

let global_of_string name =
  let p = Libnames.path_of_string name in
  (* let q = Libnames.qualid_of_path p in *)
  match Nametab.global_of_path p with
  | c -> c
  | exception Not_found ->
      Feedback.msg_debug (Pp.str (Libnames.string_of_path p)); raise Not_found

let isConstant sigma globref c =
  let open Globnames in
  match globref, EConstr.kind sigma c with
  | ConstRef const, Term.Const (n, _) -> Names.Constant.equal n const
  | IndRef ind1, Term.Ind (ind2, _) ->
      Names.eq_ind ind1 ind2
  | ConstructRef constr1, Term.Construct (constr2, _) ->
      Names.eq_constructor constr1 constr2
  | VarRef var1, Term.Var var2 ->
      Names.Id.equal var1 var2
  | _ -> false

let isFConstant globref fc =
  let open Globnames in
  match globref, CClosure.fterm_of fc with
  | ConstRef const, CClosure.FFlex (Names.ConstKey (n, _)) ->
      Names.Constant.equal n const
  | IndRef ind, CClosure.FInd pind ->
      Names.eq_ind ind (Univ.out_punivs pind)
  | ConstructRef constr, CClosure.FConstruct pconstr ->
      Names.eq_constructor constr (Univ.out_punivs pconstr)
  | VarRef var1, CClosure.FFlex (Names.VarKey var2) ->
      Names.Id.equal var1 var2
  | _ -> false

let globref_to_string globref =
  let open Globnames in
  match globref with
  | ConstRef const -> Names.Constant.to_string const
  | IndRef ind -> Pp.string_of_ppcmds (Printer.pr_inductive (Global.env ()) ind)
  | ConstructRef constr ->
      Pp.string_of_ppcmds (Printer.pr_constructor (Global.env ()) constr)
  | VarRef var -> Names.Id.to_string var


module Constr = struct
  exception Constr_not_found of string
  exception Constr_poly of string

  let mkConstr globref = lazy (
    try
      of_constr @@
      Universes.constr_of_global globref
    with Not_found -> raise (Constr_not_found (globref_to_string globref))
       | Invalid_argument _ -> raise (Constr_poly (globref_to_string globref))
  )

  let mkUConstr globref sigma env =
    try fresh_global env sigma globref
    with Not_found -> raise (Constr_not_found (globref_to_string globref))

  let isConstr sigma = fun r c -> eq_constr sigma (Lazy.force r) c
  let isConstant = isConstant
  let isFConstant = isFConstant

  let isUConstr r sigma env = fun c ->
    eq_constr_nounivs sigma (snd (mkUConstr r sigma env)) c

end

module ConstrBuilder = struct
  type t = Globnames.global_reference Lazy.t

  let from_string (s:string) : t = lazy (global_of_string s)

  let build s = Lazy.force (Constr.mkConstr (Lazy.force s))
  let build_app s args = mkApp (Lazy.force (Constr.mkConstr (Lazy.force s)), args)

  let equal sigma s = Constr.isConstant sigma (Lazy.force s)
  let fequal s = Constr.isFConstant (Lazy.force s)

  let to_coq s =
    let open Globnames in
    match (Lazy.force s) with
    | ConstRef c -> EConstr.mkConst c
    | VarRef var -> EConstr.mkVar var
    | IndRef ind -> EConstr.mkInd ind
    | ConstructRef constr -> EConstr.mkConstruct constr


  let from_coq s (_, sigma) cterm =
    let (head, args) = decompose_appvect sigma cterm in
    if equal sigma s head then Some args else None
end

module UConstrBuilder = struct
  type t = Globnames.global_reference Lazy.t

  let from_string (s:string) : t = lazy (global_of_string s)

  let build_app s sigma env args =
    let (sigma, c) = Constr.mkUConstr (Lazy.force s) sigma env in
    (sigma, mkApp (c, args))

  let to_coq s = Constr.mkUConstr (Lazy.force s)

  let equal sigma s = Constr.isConstant sigma (Lazy.force s)
  let fequal s = Constr.isFConstant (Lazy.force s)

  let from_coq s (env, sigma) cterm =
    let (head, args) = decompose_appvect sigma cterm in
    if equal sigma s head then Some args else None
end

module CoqOption = struct
  open UConstrBuilder

  (* let optionBuilder = from_string "Mtac2.Datatypes.moption" *)
  let noneBuilder = from_string "Mtac2.Datatypes.mNone"
  let someBuilder = from_string "Mtac2.Datatypes.mSome"

  (* let mkType sigma env ty = build_app optionBuilder sigma env [|ty|] *)
  let mkNone sigma env ty = build_app noneBuilder sigma env [|ty|]
  let mkSome sigma env ty t = build_app someBuilder sigma env [|ty; t|]

  exception NotAnOption

  let from_coq sigma env cterm =
    match from_coq noneBuilder (env, sigma) cterm with
    | None ->
        begin match from_coq someBuilder (env, sigma) cterm with
        | None -> raise NotAnOption
        | Some args -> Some args.(1)
        end
    | Some _ -> None

  let to_coq sigma env ty oterm =
    match oterm with
    | None -> mkNone sigma env ty
    | Some t -> mkSome sigma env ty t
end

module type ListParams = sig
  val nilname : string
  val consname : string
  val typename : string
end

module type LIST = sig
  val mkNil : Evd.evar_map -> Environ.env -> types -> Evd.evar_map * constr
  val mkCons : Evd.evar_map -> Environ.env -> types -> constr -> constr -> Evd.evar_map * constr
  val mkType : Evd.evar_map -> Environ.env -> types -> Evd.evar_map * types

  exception NotAList of constr

  val from_coq : Evd.evar_map -> Environ.env -> constr -> constr list

  (** Allows skipping an element in the conversion *)
  exception Skip
  val from_coq_conv : Evd.evar_map -> Environ.env -> (Evd.evar_map -> constr -> Evd.evar_map * 'a) -> constr -> Evd.evar_map * 'a list

  val to_coq : Evd.evar_map -> Environ.env -> types -> (Evd.evar_map -> 'a -> Evd.evar_map * constr) -> 'a list -> Evd.evar_map * constr
  val pto_coq : Environ.env -> types -> ('a -> Evd.evar_map -> Evd.evar_map * constr) -> 'a list -> Evd.evar_map -> Evd.evar_map * constr
end

module GenericList (LP : ListParams) = struct
  open UConstrBuilder

  let listBuilder = from_string LP.typename
  let nilBuilder  = from_string LP.nilname
  let consBuilder = from_string LP.consname

  let mkType sigma env ty = build_app listBuilder sigma env [|ty|]
  let mkNil sigma env ty = build_app nilBuilder sigma env [|ty|]
  let mkCons sigma env t x xs = build_app consBuilder sigma env [| t ; x ; xs |]

  exception Skip
  exception NotAList of constr
  (** given a list of terms and a convertion function fconv
      it creates a list of elements using the converstion function.
      if fconv raises Skip, that element is not included.
      if the list is ill-formed, an exception NotAList is raised. *)
  let from_coq_conv sigma env (fconv : Evd.evar_map -> constr -> Evd.evar_map * 'a) cterm =
    let rec fcc sigma cterm =
      match from_coq consBuilder (env, sigma) cterm with
      | None ->
          begin match from_coq nilBuilder (env, sigma) cterm with
          | None -> raise (NotAList cterm)
          | Some _ -> sigma, []
          end
      | Some args ->
          let (sigma, tail) = fcc sigma args.(2) in
          try
            let (sigma, h) = fconv sigma args.(1) in
            (sigma, h :: tail)
          with Skip ->
            (sigma, tail)
    in
    fcc sigma cterm

  let from_coq sigma env t =
    (* it is safe to throw away sigma here because we are not changing it *)
    snd (from_coq_conv sigma env (fun sigma (x:constr)->(sigma, x)) t)

  let to_coq sigma env ty f l =
    List.fold_right (fun e (sigma, l) -> let (sigma, t) = f sigma e in
                      mkCons sigma env ty t l)
      l
      (mkNil sigma env ty)

  let pto_coq env ty f l sigma =
    List.fold_right (fun e (sigma, l) ->
      let sigma, c = f e sigma in
      mkCons sigma env ty c l) l (mkNil sigma env ty)
end

module CoqList = GenericList (struct
    let nilname = "Mtac2.Datatypes.mnil"
    let consname = "Mtac2.Datatypes.mcons"
    let typename = "Mtac2.Datatypes.mlist"
  end)

module CoqEq = struct
  open UConstrBuilder

  let eqBuilder = from_string "Mtac2.Logic.meq"
  let eqReflBuilder = from_string "Mtac2.Logic.meq_refl"

  let mkType env sigma a x y = build_app eqBuilder env sigma [|a;x;y|]
  let mkEqRefl env sigma a x = build_app eqReflBuilder env sigma [|a;x|]
end

module CoqSig = struct
  let from_coq (env, sigma) constr =
    (* NOTE: Hightly unsafe *)
    let (_, args) = decompose_appvect sigma (whd_all env sigma constr) in
    args.(1)
end

module CoqPositive = struct
  open ConstrBuilder
  let xI = from_string "Coq.Numbers.BinNums.xI"
  let xO = from_string "Coq.Numbers.BinNums.xO"
  let xH = from_string "Coq.Numbers.BinNums.xH"

  let isH sigma = equal sigma xH
  let isI sigma = equal sigma xI
  let isO sigma = equal sigma xO

  let from_coq (env, evd) c =
    let rec fc i c =
      if isH evd c then
        1
      else
        let (s, n) = destApp evd c in
        begin
          if isI evd s then
            (fc (i+1) (n.(0)))*2 + 1
          else if isO evd s then
            (fc (i+1) (n.(0)))*2
          else
            CErrors.user_err Pp.(str "Not a positive")
        end
    in
    let c' = reduce_value env evd c in
    fc 0 c'

  let rec to_coq n =
    if n = 1 then
      ConstrBuilder.to_coq xH
    else if n mod 2 = 0 then
      build_app xO [|to_coq (n / 2)|]
    else
      build_app xI [|to_coq ((n-1)/2)|]
end

module CoqN = struct
  open ConstrBuilder
  let h0 = from_string "Coq.Numbers.BinNums.N0"
  let hP = from_string "Coq.Numbers.BinNums.Npos"

  let is0 sigma = equal sigma h0
  let isP sigma = equal sigma hP

  exception NotAnN

  let from_coq (env, evd) c =
    let fc c =
      if is0 evd c then
        0
      else
        let (s, n) = destApp evd c in
        begin
          if isP evd s then
            CoqPositive.from_coq (env, evd) (n.(0))
          else
            raise NotAnN
        end
    in
    let c' = reduce_value env evd c in
    fc c'

  let to_coq n =
    if n = 0 then
      ConstrBuilder.to_coq h0
    else
      build_app hP [|CoqPositive.to_coq n|]
end

module CoqZ = struct
  open ConstrBuilder
  let z0 = from_string "Coq.Numbers.BinNums.Z0"
  let zpos = from_string "Coq.Numbers.BinNums.Zpos"
  let zneg = from_string "Coq.Numbers.BinNums.Zneg"

  let to_coq n =
    if n = 0 then
      ConstrBuilder.to_coq z0
    else if n > 0 then
      build_app zpos [|CoqPositive.to_coq n|]
    else
      build_app zneg [|CoqPositive.to_coq n|]
end

module CoqBool = struct
  open ConstrBuilder

  let boolBuilder = from_string "Coq.Init.Datatypes.bool"
  let trueBuilder = from_string "Coq.Init.Datatypes.true"
  let falseBuilder = from_string "Coq.Init.Datatypes.false"

  let mkType () = build boolBuilder
  let mkTrue () = build trueBuilder
  let mkFalse () = build falseBuilder

  exception NotABool

  let to_coq b = if b then mkTrue () else mkFalse ()
  let from_coq sigma c =
    if equal sigma trueBuilder c then true
    else if equal sigma falseBuilder c then false
    else raise NotABool
end

module CoqAscii = struct
  open ConstrBuilder

  let asciiBuilder = from_string "Coq.Strings.Ascii.Ascii"

  let from_coq (_, sigma) c =
    let (h, args) = decompose_appvect sigma c in
    let rec from_bits n =
      if n >= Array.length args then 0
      else (if CoqBool.from_coq sigma args.(n) then 1 else 0) lsl n + from_bits (n+1)
    in
    let n = from_bits 0 in
    String.make 1 (Char.chr n)

  let to_coq c =
    let c = int_of_char c in
    let a = Array.init 8 (fun i->(c lsr i) mod 2 = 1) in
    let a = Array.map CoqBool.to_coq a in
    build_app asciiBuilder a
end

module CoqString = struct
  open ConstrBuilder

  let emptyBuilder = from_string "Coq.Strings.String.EmptyString"
  let stringBuilder = from_string "Coq.Strings.String.String"

  exception NotAString

  let from_coq (env, sigma as ctx) s =
    let rec fc s =
      let (h, args) = decompose_appvect sigma s in
      if equal sigma emptyBuilder h then ""
      else if equal sigma stringBuilder h then
        CoqAscii.from_coq ctx args.(0) ^ fc args.(1)
      else
        raise NotAString
    in
    fc (reduce_value env sigma s)

  let rec to_coq s =
    if String.length s = 0 then
      build emptyBuilder
    else
      build_app stringBuilder [|
        CoqAscii.to_coq s.[0];
        to_coq (String.sub s 1 (String.length s -1))|]
end

module CoqUnit = struct
  open ConstrBuilder

  let unitBuilder = from_string "Coq.Init.Datatypes.unit"
  let ttBuilder = from_string "Coq.Init.Datatypes.tt"

  let mkType () = build unitBuilder
  let mkTT () = build ttBuilder
end

module MCTactics = struct
  let gTactic = UConstrBuilder.from_string "Mtac2.Tactics.gtactic"

  let mkGTactic env sigma = UConstrBuilder.to_coq gTactic sigma env
end

module CoqPair = struct
  open UConstrBuilder

  let pairBuilder = from_string "Mtac2.Datatypes.mpair"

  let mkPair sigma env tya tyb a b = build_app pairBuilder sigma env [|tya;tyb;a;b|]

  exception NotAPair

  let from_coq ctx cterm =
    match from_coq pairBuilder ctx cterm with
    | None -> raise NotAPair
    | Some args -> (args.(2), args.(3))
end

module CoqPTele = struct
  open UConstrBuilder

  let pBaseBuilder = from_string "Mtac2.MTele.pBase"
  let pTeleBuilder = from_string "Mtac2.MTele.pTele"

  (* let mkType env sigma tele = build_app pTeleBuilder sigma env [|tele|] *)
  let mkPBase env sigma tele = build_app pBaseBuilder sigma env [|tele|]
  let mkPTele env sigma ty telefun tyval ptele = build_app pTeleBuilder sigma env [|ty; telefun; tyval; ptele|]

  exception NotAPTele

  let from_coq sigma env cterm =
    match from_coq pTeleBuilder (env, sigma) cterm with
    | None ->
        begin match from_coq pBaseBuilder (env, sigma) cterm with
        | None -> raise NotAPTele
        | Some _ -> None
        end
    | Some args -> Some (args.(2), args.(3))
end
