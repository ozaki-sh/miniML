(* ML interpreter / type reconstruction *)
exception Error of string

let err s = raise (Error s)

type id = string

type binOp = Plus | Minus | Mult | Lt | Mt | Eq | Cons | Hat | Expo

type binLogicOp = And | Or

type tyvar = int

type name = string

type ty =
    TyInt
  | TyBool
  | TyString
  | TyVar of tyvar
  | TyStringVar of string
  | TyFun of ty * ty
  | TyList of ty
  | TyTuple of tytuple
  | TyUser of id * ty list
  | TyVariant of id * ty list
  | TyRecord of id * ty list
  | TyNone of name
  | TySet of tyvar * ty MySet.t
and tytuple = TyEmpT | TyConsT of ty * tytuple

(* 型注釈付きのidを表す型 *)
type typedId = id * ty list

type exp =
  | Var of id (* Var "x" --> x *)
  | ILit of int (* ILit 3 --> 3 *)
  | BLit of bool (* BLit true --> true *)
  | SLit of string (* SLit "abc" --> "abc" *)
  | Constr of name * typedExp option (* Constr "A" (Some (ILit 1)) --> A 1 *)
  | Record of recordExp
  | RecordWith of typedExp * recordExp
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
  (* ListExp(Cons(ILit 1, (Cons (ILit 2, Emp)))) --> [1;2] *)
  | MatchExp of typedExp * (typedExp * typedExp) list
  (* MatchExp(ILit 1,
              [(ILit 0, ILit 0); (ILit 1, ILit 1)]) -->
     match 1 with
       0 -> 0
     | 1 -> 1 *)
  | TupleExp of tupleExp (* TupeExp (ConsT (ILit 3, ConsT (BLit true, EmpT))) --> (3, true) *)
  | RecordPattern of recordExp
  | Wildcard (* Wildcard --> _ *)
and listExp = Emp | Cons of typedExp * listExp
and tupleExp = EmpT | ConsT of typedExp * tupleExp
and recordExp = EmpR | ConsR of (name * typedExp) * recordExp
(* 型注釈付きの式を表す型 *)
and typedExp = exp * ty list

type tydecl =
    Constructor of name * ty
  | Field of name * ty

type program =
    Exp of typedExp
  | Decls of ((typedId * typedExp) list) list
  | RecDecls of ((typedId * typedExp) list) list
  | TypeDecls of ((id * string list * tydecl list) list) list


type tysc = TyScheme of tyvar list * ty


let tysc_of_ty ty = TyScheme ([], ty)


let remove_index indexed_id =
  let i = String.index indexed_id '#' in
  String.sub indexed_id (i + 1) (String.length indexed_id - (i + 1))


(* 0-25をa-zに変換する *)
let alphabet_of_0to25 i =
  if i >= 0 && i <= 25 then Char.escaped (char_of_int (i + 97))
  else "error" (* この文は実行されないはず(呼び出し側が気をつける) *)

(* intを'a,...,'z,'a1,...のstringにする *)
let string_of_num num =
  let mod26 = num mod 26 in
  let quo26 = num / 26 in
  let alphabet = alphabet_of_0to25 mod26 in
  let suffix = if quo26 = 0 then "" else string_of_int quo26 in
  "'" ^ alphabet ^ suffix

(* 型中の型変数と'a,'bなどの対応表を作る *)
let make_tyvar_string_list ty =
  let counter = ref 0 in (* pp_tyが呼ばれるたびにこのカウンターは0に戻る、すなわち型変数は'aから始まる *)
  let rec case_tytuple tytup ts_list =
    match tytup with
      TyEmpT -> ts_list
    | TyConsT (ty, tytup') ->
       let ts_list' = body_func ty ts_list in
       case_tytuple tytup' ts_list'
  and case_ty_list l ts_list =
    match l with
      [] -> ts_list
    | head :: rest ->
       let ts_list' = body_func head ts_list in
       case_ty_list rest ts_list'
  and body_func ty ts_list =
    let num = !counter in
    match ty with
      TyInt
    | TyBool
    | TyString -> ts_list
    | TyVar tyvar ->
       if List.mem_assoc tyvar ts_list then ts_list
       else (counter := num + 1; (tyvar, string_of_num num) :: ts_list)
    | TyStringVar tyvar -> ts_list (* これは型宣言の時しか呼ばれない *)
    | TyFun (domty, ranty) ->
       let domty_ts_list = body_func domty ts_list in
       let ranty_ts_list = body_func ranty domty_ts_list in
       ranty_ts_list
    | TyList ty' -> body_func ty' ts_list
    | TyTuple tytup  -> case_tytuple tytup ts_list
    | TyUser (_, l) -> case_ty_list l ts_list
    | TyVariant (_, l) -> case_ty_list l ts_list
    | TyRecord (_, l) -> case_ty_list l ts_list
    | _ -> err ("For debug: at make_tyvar_string_list")
  in
  body_func ty []

let rec string_of_ty ty =
  let tyvar_string_list = make_tyvar_string_list ty in (* これを持ちまわるのが面倒だったのでbody_funcを作った *)
  let rec  string_of_tytuple tytup =
    let rec inner_loop tytup =
      match tytup with
        TyEmpT -> ""
      | TyConsT (ty, tytup') ->
         (match ty with
            TyFun _
          | TyTuple _ -> "(" ^ (body_func ty) ^ ") * " ^ (inner_loop tytup')
          | _ -> (body_func ty) ^ " * " ^ (inner_loop tytup'))
    in
    let str = inner_loop tytup in
    let str_length = String.length str in
    String.sub str 0 (str_length - 3)
  and body_func ty =
    match ty with
      TyInt -> "int"
    | TyBool -> "bool"
    | TyString -> "string"
    | TyVar tyvar -> List.assoc tyvar tyvar_string_list
    | TyStringVar tyvar -> tyvar (* これは型宣言の時しか呼ばれない *)
    | TyFun (domty, ranty) ->
       (match domty with
          TyFun _
        | TyTuple _ -> "(" ^ (body_func domty) ^ ") -> " ^ (body_func ranty)
        | _ -> (body_func domty) ^ " -> " ^ (body_func ranty))
    | TyList ty ->
       (match ty with
          TyFun _
        | TyTuple _  -> "(" ^ (body_func ty) ^ ")" ^ " list"
        | _ -> (body_func ty) ^ " list")
    | TyTuple tytup -> string_of_tytuple tytup
    | TyUser (x, l) ->
       if List.length l = 0 then x
       else string_of_param l ^ " " ^ x
    | TyVariant (x, l) ->
       if List.length l = 0 then remove_index x
       else string_of_param l ^ " " ^ remove_index x
    | TyRecord (x, l) ->
       if List.length l = 0 then remove_index x
       else string_of_param l ^ " " ^ remove_index x
    | _ -> err ("For debug: at string_of_ty")
  in
  body_func ty

and string_of_param param =
  let rec inner_loop = function
      [] -> ")"
    | head :: rest ->
       ", " ^ string_of_ty head ^ inner_loop rest
  in
  if List.length param = 1 then
    string_of_ty (List.hd param)
  else
    let str = inner_loop param in
    "(" ^ String.sub str 2 (String.length str - 2)

(* pretty printing *)
let pp_ty ty = print_string (string_of_ty ty)



let fresh_tyvar =
  let counter = ref 0 in
  let body () =
    let v = !counter in
    counter := v + 1; v
  in body



let rec freevar_ty ty =
  let rec freevar_tytuple tytup =
    match tytup with
      TyEmpT -> MySet.empty
    | TyConsT (ty, tytup') -> MySet.union (freevar_ty ty) (freevar_tytuple tytup')
  and freevar_ty_list ty_list =
    match ty_list with
      [] -> MySet.empty
    | head :: rest -> MySet.union (freevar_ty head) (freevar_ty_list rest)
  in
  match ty with
    TyInt
  | TyBool
  | TyString -> MySet.empty
  | TyVar tyvar -> MySet.singleton tyvar
  | TyFun (domty, ranty) -> MySet.union (freevar_ty domty) (freevar_ty ranty)
  | TyList ty -> freevar_ty ty
  | TyTuple tytup -> freevar_tytuple tytup
  | TyVariant (_, l) -> freevar_ty_list l
  | TyRecord (_, l) -> freevar_ty_list l
  | TyNone _ -> MySet.empty
  | TySet _ -> MySet.empty
  | _ -> err ("For debug: at freevar_ty")

let freevar_tysc tysc =
  match tysc with
    TyScheme (tyvar_list, ty) ->
      let freevar_in_ty = freevar_ty ty in
      let boundty = MySet.from_list tyvar_list in
      MySet.diff freevar_in_ty boundty


let string_of_def d =
  match d with
    Constructor (id, ty) ->
     (match ty with
        TyNone _ -> id
      | _ -> id ^ " of " ^ (string_of_ty ty))
  | Field (id, ty) ->
     id ^ " : " ^ (string_of_ty ty)

let string_of_defs ds =
  let strdefs = List.map string_of_def ds in
  match List.hd ds with
    Constructor _ ->
     let str = List.fold_right (fun x y -> x ^ " | " ^ y) strdefs "" in
     String.sub str 0 (String.length str - 3)
  | Field _ ->
     let str = List.fold_right (fun x y -> x ^ "; " ^ y) strdefs "" in
     "{ " ^ str ^ "}"
let pp_defs ds = print_string (string_of_defs ds)



let string_of_param_decl param =
  let rec inner_loop = function
      [] -> ")"
    | head :: rest ->
       ", " ^ head ^ inner_loop rest
  in
  if List.length param = 0 then
    ""
  else if List.length param = 1 then
    List.hd param
  else
    let str = inner_loop param in
    "(" ^ String.sub str 2 (String.length str - 2)
