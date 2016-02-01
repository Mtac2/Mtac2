open Constr
open Term
open Reductionops

let reduce_value = Tacred.compute

module Constr = struct
  exception Constr_not_found of string
  exception Constr_poly of string

  let mkConstr name = lazy (
    try Universes.constr_of_global
          (Nametab.global_of_path (Libnames.path_of_string name))
    with Not_found -> raise (Constr_not_found name)
       | Invalid_argument _ -> raise (Constr_poly name)
  )

  let mkUConstr name sigma env =
    try Evd.fresh_global env sigma
          (Nametab.global_of_path (Libnames.path_of_string name))
    with Not_found -> raise (Constr_not_found name)

  let isConstr = fun r c -> eq_constr (Lazy.force r) c

  let isUConstr r sigma env = fun c ->
    eq_constr_nounivs (snd (mkUConstr r sigma env)) c

  let eq_ind i1 i2 = Names.eq_ind (fst i1) (fst i2)

end

module ConstrBuilder = struct

  type t = string

  let from_string (s:string) : t = s

  let build_app s args = mkApp (Lazy.force (Constr.mkConstr s), args)

  let equal s = Constr.isConstr (Constr.mkConstr s)

  exception WrongConstr of t * constr

  let from_coq s (env, sigma as ctx) cterm =
    let (head, args) = whd_betadeltaiota_stack env sigma cterm in
    let args = Array.of_list args in
    if equal s head then
      args
    else
      raise (WrongConstr (s, head))
end

module UConstrBuilder = struct

  type t = string

  let from_string (s:string) : t = s

  let build_app s sigma env args =
    let (sigma, c) = Constr.mkUConstr s sigma env in
    (sigma, mkApp (c, args))

  let equal = Constr.isUConstr

  exception WrongConstr of t * constr

  let from_coq s (env, sigma as ctx) cterm =
    let (head, args) = whd_betadeltaiota_stack env sigma cterm in
    let args = Array.of_list args in
    if equal s sigma env head then
      args
    else
      raise (WrongConstr (s, head))
end

module CoqOption = struct
  let noneBuilder = ConstrBuilder.from_string "Coq.Init.Datatypes.None"

  let mkNone ty = ConstrBuilder.build_app noneBuilder [|ty|]

  let someBuilder = ConstrBuilder.from_string "Coq.Init.Datatypes.Some"

  let mkSome ty t = ConstrBuilder.build_app someBuilder [|ty; t|]

  let from_coq (env, sigma as ctx) cterm fsome =
    try
      let _ = ConstrBuilder.from_coq noneBuilder ctx cterm in
      None
    with ConstrBuilder.WrongConstr _ ->
      let arr = ConstrBuilder.from_coq someBuilder ctx cterm in
      Some (fsome arr.(0))

end

module CoqList = struct
  let mkNil  = Constr.mkConstr "Coq.Init.Datatypes.nil"
  let mkCons = Constr.mkConstr "Coq.Init.Datatypes.cons"

  let makeNil ty = Term.mkApp (Lazy.force mkNil, [| ty |])
  let makeCons t x xs = Term.mkApp (Lazy.force mkCons, [| t ; x ; xs |])

  let mkListType ty =
    mkApp (Lazy.force (Constr.mkConstr "Coq.Init.Datatypes.cons"),
           [|ty|])

  let isNil  = Constr.isConstr mkNil
  let isCons = Constr.isConstr mkCons

  let rec from_coq_conv (env, sigma as ctx) (fconv : Term.constr -> 'a) cterm =
    let (constr, args) = whd_betadeltaiota_stack env sigma cterm in
    if isNil constr then [] else
    if not (isCons constr) then invalid_arg "not a list" else
      let elt = List.nth args 1 in
      let ctail = List.nth args 2 in
      fconv elt :: from_coq_conv ctx fconv ctail

  let from_coq (env, sigma) =
    from_coq_conv (env, sigma) (fun x->x)

end

module CoqEq = struct
  let mkEq = Constr.mkConstr "Coq.Init.Logic.eq"
  let mkEqRefl = Constr.mkConstr "Coq.Init.Logic.eq_refl"

  let mkAppEq a x y = mkApp(Lazy.force mkEq, [|a;x;y|])
  let mkAppEqRefl a x = mkApp(Lazy.force mkEqRefl, [|a;x|])
end

module CoqSigT = struct
  let mkExistT  = Constr.mkConstr "Coq.Init.Specif.existT"

  let mkAppExistT a p x px =
    mkApp (Lazy.force mkExistT, [|a; p; x; px|])
end


module CoqSig = struct
  let rec from_coq (env, sigma) constr =
    (* NOTE: Hightly unsafe *)
    let (_, args) = whd_betadeltaiota_stack env sigma constr in
    List.nth args 1
end

module CoqNat = struct
  let mkZero = Constr.mkConstr "Coq.Init.Datatypes.O"
  let mkSucc = Constr.mkConstr "Coq.Init.Datatypes.S"

  let isZero = Constr.isConstr mkZero
  let isSucc = Constr.isConstr mkSucc

  let rec to_coq = function
    | 0 -> Lazy.force mkZero
    | n -> Term.mkApp (Lazy.force mkSucc, [| to_coq (pred n) |])

  let from_coq (env, evd) c =
    let rec fc c =
      if isZero c then
        0
      else
        let (s, n) = destApp c in
        begin
          if isSucc s then
            1 + (fc (n.(0)))
          else
            Errors.error "Not a nat"
        end
    in
    let c' = reduce_value env evd c in
    fc c'

end

module CoqPositive = struct
  let xI = Constr.mkConstr "Coq.Numbers.BinNums.xI"
  let xO = Constr.mkConstr "Coq.Numbers.BinNums.xO"
  let xH = Constr.mkConstr "Coq.Numbers.BinNums.xH"

  let isH = Constr.isConstr xH
  let isI = Constr.isConstr xI
  let isO = Constr.isConstr xO

  let from_coq (env, evd) c =
    let rec fc i c =
      if isH c then
        1
      else
        let (s, n) = destApp c in
        begin
          if isI s then
            (fc (i+1) (n.(0)))*2 + 1
          else if isO s then
            (fc (i+1) (n.(0)))*2
          else
            Errors.error "Not a positive"
        end
    in
    let c' = reduce_value env evd c in
    fc 0 c'

  let rec to_coq n =
    if n = 1 then
      Lazy.force xH
    else if n mod 2 = 0 then
      mkApp(Lazy.force xO, [|to_coq (n / 2)|])
    else
      mkApp(Lazy.force xI, [|to_coq ((n-1)/2)|])

end

module CoqN = struct
  let tN = Constr.mkConstr "Coq.Numbers.BinNums.N"
  let h0 = Constr.mkConstr "Coq.Numbers.BinNums.N0"
  let hP = Constr.mkConstr "Coq.Numbers.BinNums.Npos"

  let is0 = Constr.isConstr h0
  let isP = Constr.isConstr hP

  let from_coq (env, evd) c =
    let rec fc c =
      if is0 c then
        0
      else
        let (s, n) = destApp c in
        begin
          if isP s then
            CoqPositive.from_coq (env, evd) (n.(0))
          else
            Errors.error "Not a positive"
        end
    in
    let c' = reduce_value env evd c in
    fc c'

  let to_coq n =
    if n = 0 then
      Lazy.force h0
    else
      mkApp(Lazy.force hP, [|CoqPositive.to_coq n|])
end

module CoqBool = struct

  let mkTrue = Constr.mkConstr "Coq.Init.Datatypes.true"
  let mkFalse = Constr.mkConstr "Coq.Init.Datatypes.false"

  let isTrue = Constr.isConstr mkTrue

end

module CoqAscii = struct

  let from_coq (env, sigma) c =
    let (h, args) = whd_betadeltaiota_stack env sigma c in
    let rec from_bits n bits =
      match bits with
      | [] -> 0
      | (b :: bs) -> (if CoqBool.isTrue b then 1 else 0) lsl n + from_bits (n+1) bs
    in
    let n = from_bits 0 args in
    (* Char.escaped (Char.chr n) *) (* Why was it excaped in the first place ? *)
    String.make 1 (Char.chr n)

end

module CoqString = struct

  let mkEmpty = Constr.mkConstr "Coq.Strings.String.EmptyString"
  let mkString = Constr.mkConstr "Coq.Strings.String.String"

  let isEmpty = Constr.isConstr mkEmpty
  let isString = Constr.isConstr mkString

  let rec from_coq (env, sigma) s =
    let (h, args) = whd_betadeltaiota_stack env sigma s in
    if isEmpty h then
      ""
    else if isString h then
      let c, s' = List.nth args 0, List.nth args 1 in
      CoqAscii.from_coq (env, sigma) c ^ from_coq (env, sigma) s'
    else
      Errors.error "Not a string"
end

module CoqUnit = struct
  let mkTT = Constr.mkConstr "Coq.Init.Datatypes.tt"
end
