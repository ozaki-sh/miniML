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

and string_of_exp = function
    Var x -> "Var " ^ x
  | ILit i -> "ILit " ^ (string_of_int i)
  | BLit b -> "BLit " ^ (string_of_bool b)
  | SLit s -> "SLit " ^ s
  | Constr (id, expop) ->
     (match expop with
        None -> "Constr (" ^ id ^ ", None)"
      | Some (exp, _) -> "Constr (" ^ id ^ ", " ^ (string_of_exp exp) ^ ")")
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
  | Wildcard -> "Wildcard"

let rec string_of_tyrow = function
    TyInt -> "TyInt"
  | TyBool -> "TyBool"
  | TyString -> "TyString"
  | TyVar tyvar -> "TyVar " ^ (string_of_int tyvar)
  | TyStringVar tyvar -> "TyStringVar " ^ tyvar
  | TyFun (domty, ranty) -> "TyFun (" ^ (string_of_tyrow domty) ^ ", " ^ (string_of_tyrow ranty) ^ ")"
  | TyList ty -> "TyList " ^ (string_of_tyrow ty)
  | TyTuple tytup -> "TyTuple "
  | TyUser id -> "TyUser " ^ id
  | TyVariant id -> "TyVariant " ^ id
  | TySet (tyvar, l) -> "TySet (" ^ (string_of_int tyvar) ^ ", " ^ List.fold_left (fun x y -> x ^ "; " ^ y) "" ((List.map (fun x -> string_of_tyrow x) (MySet.to_list l)))

let rec string_of_tydecl = function
    Constructor (name, None) -> name
  | Constructor (name, Some ty) -> name ^ " of " ^ string_of_ty ty
  | Field (name, ty) -> name ^ " : " ^ string_of_ty ty

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
                (List.map (fun (id, tydecl) -> id ^ " <-def-> " ^ string_of_defs tydecl) y)) ^ "\n")
       ""
       l


let rec string_of_subst s =
  List.fold_left
    (fun x y -> x ^ "; " ^ y)
    ""
    (List.map (fun (tyvar, ty) -> "(" ^ (string_of_int tyvar) ^ ", " ^ (string_of_tyrow ty) ^ ")") s)
