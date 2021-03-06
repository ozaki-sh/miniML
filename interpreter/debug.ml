open Syntax

let rec string_of_binOp = function
    Plus -> "Plus"
  | Minus -> "Minus"
  | Mult -> "Mult"
  | Lt -> "Lt"
  | Mt -> "Mt"
  | Eq -> "Eq"
  | Cons -> "Cons"
  | Hat -> "Hat"
  | Expo -> "Expo"

and string_of_binLogicOp = function
    And -> "And"
  | Or -> "Or"

and string_of_bind = function
    [] -> ""
  | ((id, _), (exp, _)) :: rest ->
     "(" ^ id ^ ", (" ^ (string_of_exp exp) ^ ")); " ^ (string_of_bind rest)

and string_of_listExp = function
    Emp -> "Emp"
  | Cons ((exp, _), l) -> "Cons ((" ^ (string_of_exp exp) ^ "), (" ^ (string_of_listExp l) ^ "))"

and string_of_pattern_and_body_list = function
    [] -> ""
  | ((pattern, _), (body, _)) :: rest ->
     "((" ^ (string_of_exp pattern) ^ "), (" ^ (string_of_exp body) ^ ")); "
    ^ (string_of_pattern_and_body_list rest)

and string_of_tupleExp = function
    EmpT -> "EmpT"
  | ConsT ((exp, _), l) -> "ConsT ((" ^ (string_of_exp exp) ^ "), (" ^ (string_of_tupleExp l) ^ "))"

and string_of_recordExp = function
    EmpR -> "EmpR"
  | ConsR ((name, (exp, _)), l) -> "ConsR ((" ^ name ^ ", " ^ (string_of_exp exp) ^ "), (" ^ (string_of_recordExp l) ^ "))"

and string_of_exp = function
    Var x -> "Var " ^ x
  | ILit i -> "ILit " ^ (string_of_int i)
  | BLit b -> "BLit " ^ (string_of_bool b)
  | SLit s -> "SLit " ^ s
  | Constr (id, expop) ->
     (match expop with
        None -> "Constr (" ^ id ^ ", None)"
      | Some (exp, _) -> "Constr (" ^ id ^ ", " ^ (string_of_exp exp) ^ ")")
  | Record rexp -> "Record " ^ (string_of_recordExp rexp)
  | RecordWith ((exp, _), rexp) -> "RecordWith (" ^ (string_of_exp exp) ^ ", " ^ (string_of_recordExp rexp)
  | BinOp (op, (exp1, _), (exp2, _)) ->
     "BinOp " ^ (string_of_binOp op) ^
       " (" ^ (string_of_exp exp1) ^ "), (" ^ (string_of_exp exp2) ^ ")"
  | BinLogicOp (op, (exp1, _), (exp2, _)) ->
     "BinLogicOp " ^ (string_of_binLogicOp op) ^
       " (" ^ (string_of_exp exp1) ^ "), (" ^ (string_of_exp exp2) ^ ")"
  | IfExp ((exp1, _), (exp2, _), (exp3, _)) ->
     "IfExp (" ^ (string_of_exp exp1) ^ "), ("
     ^ (string_of_exp exp2) ^ "), (" ^ (string_of_exp exp3) ^ ")"
  | LetExp (l, (exp2,_ )) ->
     "LetExp [" ^ (string_of_bind l) ^ "], (" ^ (string_of_exp exp2) ^ ")"
  | FunExp ((id, _), (exp, _)) ->
     "FunExp " ^ id ^ ", (" ^ (string_of_exp exp) ^ ")"
  | DFunExp ((id, _), (exp, _)) ->
     "DFunExp " ^ id ^ ", (" ^ (string_of_exp exp) ^ ")"
  | AppExp ((exp1, _), (exp2, _)) ->
     "AppExp (" ^ (string_of_exp exp1) ^ "), (" ^ (string_of_exp exp2) ^ ")"
  | LetRecExp (l, (exp2, _)) ->
     "LetRecExp [" ^ (string_of_bind l) ^ "], (" ^ (string_of_exp exp2) ^ ")"
  | ListExp lexp ->
     "ListExp " ^ (string_of_listExp lexp)
  | MatchExp ((exp, _), pattern_and_body_list) ->
     "MatchExp (" ^ (string_of_exp exp) ^ "), ["
     ^ (string_of_pattern_and_body_list pattern_and_body_list)
  | TupleExp texp ->
     "TupleExp " ^ (string_of_tupleExp texp)
  | RecordPattern rexp -> "RecordPattern " ^ (string_of_recordExp rexp)
  | AssignExp ((exp1, _), name, (exp2, _)) -> "AssignExp (" ^ (string_of_exp exp1) ^ ", " ^ name ^ ", " ^ (string_of_exp exp2) ^ ")"
  | Unit -> "Unit"
  | Wildcard -> "Wildcard"

let rec string_of_tytuple = function
    TyEmpT -> ""
  | TyConsT (ty, tytup) -> string_of_tyrow ty ^ ", " ^ string_of_tytuple tytup

and string_of_ty_list l =
  let rec inner_loop = function
    [] -> "]"
  | head :: rest ->
     "; " ^ string_of_tyrow head ^ inner_loop rest
  in
  if List.length l = 0 then
    "[]"
  else if List.length l = 1 then
    "[" ^ string_of_tyrow (List.hd l) ^ "]"
  else
    let str = inner_loop l in
    "[" ^ String.sub str 2 (String.length str - 2)

and string_of_tyrow = function
    TyInt -> "TyInt"
  | TyBool -> "TyBool"
  | TyString -> "TyString"
  | TyVar tyvar -> "TyVar " ^ (string_of_int tyvar)
  | TyStringVar tyvar -> "TyStringVar " ^ tyvar
  | WeakTyVar tyvar -> "WeakTyVar " ^ string_of_int tyvar
  | TyFun (domty, ranty) -> "TyFun (" ^ (string_of_tyrow domty) ^ ", " ^ (string_of_tyrow ranty) ^ ")"
  | TyList ty -> "TyList " ^ (string_of_tyrow ty)
  | TyTuple tytup -> "TyTuple (" ^ string_of_tytuple tytup ^ ")"
  | TyUser (name, l) -> "TyUser (" ^ name ^ ", " ^ string_of_ty_list l ^ ")"
  | TyVariant (name, l) -> "TyVariant (" ^ name ^ ", " ^ string_of_ty_list l ^ ")"
  | TyRecord (name, l) -> "TyRecord (" ^ name ^ ", " ^ string_of_ty_list l ^ ")"
  | TyNone _ -> "TyNone"
  | TyUnit -> "TyUnit"
  | TySet (tyvar, l, nest_level) ->
     let str = match nest_level with
         MostOuter -> "MostOuter"
       | Other -> "Other" in
     "TySet (" ^ (string_of_int tyvar) ^ ", " ^ (List.fold_left (fun x y -> x ^ "; " ^ y) "" ((List.map (fun x -> string_of_tyrow x) (MySet.to_list l)))) ^ ", " ^ str ^ ")"

let rec string_of_tydecl = function
    Constructor (name, ty) -> name ^ " of " ^ string_of_tyrow ty
  | Field (name, ty, mutability) ->
     let mut = match mutability with Mutable -> "mutable " | Immutable -> "" in
     mut ^ name ^ " : " ^ string_of_tyrow ty

let rec string_of_param = function
    [] -> "]"
  | head :: rest ->
     head ^ "; " ^ string_of_param rest

let string_of_decl = function
    Exp (exp, _) -> string_of_exp exp
  | Decls l ->
     List.fold_left
       (fun x y ->
         x ^ (List.fold_left
                (fun s t -> s ^ t ^ "\n")
                ""
                (List.map (fun ((id, _), (exp, _)) -> id ^ " ::= " ^ string_of_exp exp) y)) ^ "\n")
       ""
       l
  | RecDecls l ->
     List.fold_left
       (fun x y ->
         x ^ (List.fold_left
                (fun s t -> s ^ t ^ "\n")
                ""
                (List.map (fun ((id, _), (exp, _)) -> id ^ " ::= " ^ string_of_exp exp) y)) ^ "\n")
       ""
       l
  | TypeDecls l ->
     List.fold_left
       (fun x y ->
         x ^ (List.fold_left
                (fun s t -> s ^ t ^ "\n")
                ""
                (List.map (fun (id, param, tydecl) -> id ^ " <-def-> " ^ "[" ^ string_of_param param ^ "] " ^  string_of_defs tydecl) y)) ^ "\n")
       ""
       l


let rec string_of_subst s =
  List.fold_right
    (fun x y -> x ^ "; " ^ y)
    (List.map (fun (tyvar, ty) -> "(" ^ (string_of_int tyvar) ^ ", " ^ (string_of_tyrow ty) ^ ")") s)
    ""

let rec string_of_eqs eqs =
  List.fold_right
    (fun x y -> x ^ "; " ^ y)
    (List.map (fun (ty1, ty2) -> "(" ^ (string_of_tyrow ty1) ^ ", " ^ (string_of_tyrow ty2) ^ ")") eqs)
    ""


