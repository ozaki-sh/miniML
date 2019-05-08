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

let string_of_decl = function
    Exp (exp, _) -> string_of_exp exp
  | _ -> ""
