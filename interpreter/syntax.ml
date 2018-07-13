(* ML interpreter / type reconstruction *)
type id = string

type binOp = Plus | Minus | Mult | Lt | Eq | Cons

type binLogicOp = And | Or

type tyvar = int

type ty =
    TyInt
  | TyBool
  | TyVar of tyvar
  | TyFun of ty * ty
  | TyList of ty

type attached_tyvar = string

type attached_ty =
    Tyint
  | Tybool
  | Tyvar of attached_tyvar
  | Tyfun of attached_ty * attached_ty
  | Tylist of attached_ty
  | Ranty of attached_ty
  | TransformedTyvar of tyvar

type typedId = id * attached_ty list

type exp =
  | Var of id (* Var "x" --> x *)
  | ILit of int (* ILit 3 --> 3 *)
  | BLit of bool (* BLit true --> true *)
  | BinOp of binOp * typedExp * typedExp
  (* BinOp(Plus, ILit 4, Var "x") --> 4 + x *)
  | BinLogicOp of binLogicOp * typedExp * typedExp
  (* BinLogicOp(And, BLit true, BLit false) --> true && false *)
  | IfExp of typedExp * typedExp * typedExp
  (* IfExp(BinOp(Lt, Var "x", ILit 4), 
           ILit 3, 
           Var "x") --> 
     if x<4 then 3 else x *)
  | LetExp of (typedId * typedExp) list * typedExp
  (* LetExp([("x", ILit 5); ("y", ILit 3)], 
            BinOp(Plus, Var "x", Var "y") -->
     let x = 5 and y = 3 in x + y *)
  | FunExp of typedId * typedExp
  (* FunExp("x", BinOp(Plus, Var "x", ILit 1)) --> fun x -> x + 1 *)
  | DFunExp of typedId * typedExp
  (* DFunExp("x", BinOp(Plus, Var "x", ILit 1)) --> dfun x -> x + 1 *)
  | AppExp of typedExp * typedExp
  (* AppExp(Var "f", ILit 3) --> f 3 *)
  | LetRecExp of (typedId * typedExp) list * typedExp
  | ListExp of listExp
  (* ListExp(Cons(ILit 1, (Cons(ILit 2, Emp)))) --> [1;2] *)
  | MatchExp of typedExp list * (typedExp list * typedExp) list
  (* MatchExp([ILit 1; ILit 2],
              [([ILit 0; ILit 1], ILit 0); ([ILit 1; ILit 2], ILit 1)]) -->
     match 1, 2 with
       0, 1 -> 0
     | 1, 2 -> 1 *)
  | Wildcard (* Wildcard --> _ *)
and listExp = Emp | Cons of typedExp * listExp
and typedExp = exp * attached_ty list


type program = 
    Exp of typedExp
  | Decls of ((typedId * typedExp) list) list
  | RecDecls of ((typedId * typedExp) list) list


type tysc = TyScheme of tyvar list * ty


let tysc_of_ty ty = TyScheme ([], ty)

let alphabet_of_0to25 i = 
  if i >= 0 && i <= 25 then Char.escaped (char_of_int (i + 97))
  else "error"

let string_of_num num =
  let mod26 = num mod 26 in
  let quo26 = num / 26 in
  let alphabet = alphabet_of_0to25 mod26 in
  let suffix = if quo26 = 0 then "" else string_of_int quo26 in
  "'" ^ alphabet ^ suffix

let make_tyvar_string_list ty =
  let counter = ref 0 in
  let rec body_func ty ts_list =
    let num = !counter in
    match ty with
      TyInt
    | TyBool -> ts_list
    | TyVar tyvar ->
        if List.mem_assoc tyvar ts_list then ts_list
        else (counter := num + 1; (tyvar, string_of_num num) :: ts_list)
    | TyFun (domty, ranty) ->
        let domty_ts_list = body_func domty ts_list in
        let ranty_ts_list = body_func ranty domty_ts_list in
        domty_ts_list @ ranty_ts_list
    | TyList ty' -> body_func ty' ts_list
  in
    body_func ty []
         

let rec string_of_ty ty =
  let tyvar_string_list = make_tyvar_string_list ty in
  let rec body_func ty =
    match ty with
      TyInt -> "int"
    | TyBool -> "bool"
    | TyVar tyvar -> List.assoc tyvar tyvar_string_list
    | TyFun (TyFun (_, _) as domty, ranty) -> "(" ^ (body_func domty) ^ ")" ^
                                              " -> " ^ (body_func ranty)
    | TyFun (domty, ranty) -> (body_func domty) ^ " -> " ^ (body_func ranty)
    | TyList ty -> 
       (match ty with
          TyFun (_, _) -> "(" ^ (body_func ty) ^ ")" ^ " list"
        | _ -> (body_func ty) ^ " list")
  in
    body_func ty


let rec ty_of_attached_ty attached_ty stv_to_itv_list =
  let rec body_func = function
      Tyint -> TyInt
    | Tybool -> TyBool
    | Tyvar tyvar -> TyVar (List.assoc tyvar stv_to_itv_list)
    | Tyfun (domty, ranty) -> TyFun ((body_func domty), (body_func ranty))
    | Tylist ty -> TyList (body_func ty)
  in
    body_func attached_ty


(* pretty printing *)
let pp_ty ty = print_string (string_of_ty ty)


let string_of_tysc (TyScheme (tyvarlist, ty)) =
  let tyvar_string_list = make_tyvar_string_list ty in
  let string_of_tyvar tyvar = List.assoc tyvar tyvar_string_list in
  "[" ^ (List.fold_right (fun x y -> x ^ ", " ^ y) (List.map (string_of_tyvar) tyvarlist) "") ^ "|" ^ (string_of_ty ty) ^ "]" 
    

let pp_tysc tysc = print_string (string_of_tysc tysc)


let fresh_tyvar =
  let counter = ref 0 in
  let body () =
    let v = !counter in
      counter := v + 1; v
  in body    
  

let rec freevar_ty ty = 
  match ty with
    TyInt
  | TyBool -> MySet.empty
  | TyVar tyvar -> MySet.singleton tyvar
  | TyFun (domty, ranty) -> MySet.union (freevar_ty domty) (freevar_ty ranty)
  | TyList ty -> freevar_ty ty

let freevar_tysc tysc =
  match tysc with
    TyScheme (tyvar_list, ty) ->
      let freevar_in_ty = freevar_ty ty in
      let boundty = MySet.from_list tyvar_list in
      MySet.diff freevar_in_ty boundty
