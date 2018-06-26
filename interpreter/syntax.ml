(* ML interpreter / type reconstruction *)
type id = string

type binOp = Plus | Minus | Mult | Lt | Eq | Cons

type binLogicOp = And | Or

type exp =
  | Var of id (* Var "x" --> x *)
  | ILit of int (* ILit 3 --> 3 *)
  | BLit of bool (* BLit true --> true *)
  | BinOp of binOp * exp * exp
  (* BinOp(Plus, ILit 4, Var "x") --> 4 + x *)
  | BinLogicOp of binLogicOp * exp * exp
  (* BinLogicOp(And, BLit true, BLit false) --> true && false *)
  | IfExp of exp * exp * exp
  (* IfExp(BinOp(Lt, Var "x", ILit 4), 
           ILit 3, 
           Var "x") --> 
     if x<4 then 3 else x *)
  | LetExp of (id * exp) list * exp
  (* LetExp([("x", ILit 5); ("y", ILit 3)], 
            BinOp(Plus, Var "x", Var "y") -->
     let x = 5 and y = 3 in x + y *)
  | FunExp of id * exp
  (* FunExp("x", BinOp(Plus, Var "x", ILit 1)) --> fun x -> x + 1 *)
  | DFunExp of id * exp
  (* DFunExp("x", BinOp(Plus, Var "x", ILit 1)) --> dfun x -> x + 1 *)
  | AppExp of exp * exp
  (* AppExp(Var "f", ILit 3) --> f 3 *)
  | LetRecExp of (id * id * exp) list * exp
  | ListExp of listExp
  (* ListExp(Cons(ILit 1, (Cons(ILit 2, Emp)))) --> [1;2] *)
  | MatchExp of exp list * (exp list * exp) list
  (* MatchExp([ILit 1; ILit 2],
              [([ILit 0; ILit 1], ILit 0); ([ILit 1; ILit 2], ILit 1)]) -->
     match 1, 2 with
       0, 1 -> 0
     | 1, 2 -> 1 *)
  | Wildcard (* Wildcard --> _ *)
and listExp = Emp | Cons of exp * listExp

type program = 
    Exp of exp
  | Decls of ((id * exp) list) list
  | RecDecls of ((id * id * exp) list) list
