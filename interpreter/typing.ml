open Syntax

exception Error of string

let err s = raise (Error s)

(* Type Environment *)
type tyenv = ty Environment.t

let ty_prim op ty1 ty2 = match op with
    Plus -> (match ty1, ty2 with
               TyInt, TyInt -> TyInt
             | _ -> err ("Argument must be of integer: +"))
  | Minus -> (match ty1, ty2 with
               TyInt, TyInt -> TyInt
             | _ -> err ("Argument must be of integer: -"))
  | Mult -> (match ty1, ty2 with
               TyInt, TyInt -> TyInt
             | _ -> err ("Argument must be of integer: *"))
  | Lt -> (match ty1, ty2 with
             TyInt, TyInt -> TyInt
           | _ -> err ("Argument must be of integer: <"))
  | Eq -> (match ty1, ty2 with
              x, y when (x = y) -> x
            | _ -> err ("Both arguments must be same: ="))
  | And -> (match ty1, ty2 with
              TyBool, TyBool -> TyBool
            | _ -> err ("Argument must be of boolean: &&"))
  | Or -> (match ty1, ty2 with
             TyBool, TyBool -> TyBool
           | _ -> err ("Argument must be of boolean: ||"))
  | Cons ->

let rec ty_exp tyenv = function
    Var x -> 
      (try Environment.lookup x tyenv with
         Environment.Not_bound -> err ("variable not bound: " ^ x))
  | ILit -> TyInt
  | BLit -> TyBool
  | BinOp (op, exp1, exp2) ->
  | BinOp (op, exp1, exp2) ->
      let tyarg1 = ty_exp tyenv exp1 in
      let tyarg2 = ty_exp tyenv exp2 in
        ty_prim op tyarg1 tyarg2
  | IfExp (exp1, exp2, exp3) ->
      let tyarg1 = ty_exp tyenv exp1 in
      if tyarg1 <> TyBool then err ("Condition must be of boolean: if")
      else
        let tyarg2 = ty_exp tyenv exp2 in
        let tyarg3 = ty_exp tyenv exp3 in
        if tyarg2 = tyarg3 then tyarg2
        else err ("Argument of then part must be same as argument of else part: if")
  | LetExp (id, exp1, exp2) ->
      let tyarg1 = ty_exp tyenv exp1 in
      let newtyenv = Environment id tyarg1 tyenv in
      ty_exp newtyenv exp2
  | _ -> err ("Not Implemented!")

let ty_decl tyenv = function
    Exp e -> ty_exp tyenv e
  | _ -> err ("Not Implemented!")
