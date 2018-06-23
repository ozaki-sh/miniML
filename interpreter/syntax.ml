(* ML interpreter / type reconstruction *)
type id = string

type binOp = Plus | Minus | Mult | Lt | Eq | Cons

type binLogicOp = And | Or

type binListOp = Cons

type exp =
  | Var of id (* Var "x" --> x *)
  | ILit of int (* ILit 3 --> 3 *)
  | BLit of bool (* BLit true --> true *)
  | BinOp of binOp * exp * exp
  (* BinOp(Plus, ILit 4, Var "x") --> 4 + x *)
  | BinLogicOp of binLogicOp * exp * exp
  | BinListOp of binListOp * exp * exp
  | IfExp of exp * exp * exp
  (* IfExp(BinOp(Lt, Var "x", ILit 4), 
           ILit 3, 
           Var "x") --> 
     if x<4 then 3 else x *)
  | LetExp of (id * exp) list * exp
  (* LetExp("x", 
            ILit 5, 
            BinOp(Plus, Var "x", ILit 3) -->
     let x = 5 in x + 3 *)
  | FunExp of id * exp
  | DFunExp of id * exp
  | AppExp of exp * exp
  | LetRecExp of (id * id * exp) list * exp
  | ListExp of listExp
  | MatchExp of exp list * (exp list * exp) list
  | PatternExp of exp
  | Wildcard
and listExp = Emp | Cons of exp * listExp

type program = 
    Exp of exp
  | Decls of ((id * exp) list) list
  | RecDecls of ((id * id * exp) list) list
