open Syntax

exception Error of string

let err s = raise (Error s)


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
             TyInt, TyInt -> TyBool
           | _ -> err ("Argument must be of integer: <"))
  | Eq -> (match ty1, ty2 with
              x, y when (x = y) -> x
            | _ -> err ("Both arguments must be same: ="))
  | Cons -> err ("Noy Im")

let ty_logic_prim op ty1 ty2 = match op with
    And -> (match ty1, ty2 with
              TyBool, TyBool -> TyBool
            | _ -> err ("Argument must be of boolean: &&"))
  | Or -> (match ty1, ty2 with
             TyBool, TyBool -> TyBool
           | _ -> err ("Argument must be of boolean: ||"))

let rec ty_exp tyenv = function
    Var x -> 
      (try Environment.lookup x tyenv with
         Environment.Not_bound -> err ("variable not bound: " ^ x))
  | ILit _ -> TyInt
  | BLit _ -> TyBool
  | BinOp (op, exp1, exp2)->
      let tyarg1 = ty_exp tyenv exp1 in
      let tyarg2 = ty_exp tyenv exp2 in
        ty_prim op tyarg1 tyarg2
  | BinLogicOp (op, exp1, exp2) ->
      let tyarg1 = ty_exp tyenv exp1 in
      let tyarg2 = ty_exp tyenv exp2 in
        ty_logic_prim op tyarg1 tyarg2
  | IfExp (exp1, exp2, exp3) ->
      let tyarg1 = ty_exp tyenv exp1 in
      if tyarg1 <> TyBool then err ("Test expression must be of boolean: if")
      else
        let tyarg2 = ty_exp tyenv exp2 in
        let tyarg3 = ty_exp tyenv exp3 in
        if tyarg2 = tyarg3 then tyarg2
        else err ("Argument of then part must be same as argument of else part: if")
  | LetExp (l, exp2) ->
      let rec ty_let_list l tyenv' id_l =
        match l with
          [] -> ty_exp tyenv' exp2
        | (id, exp1) :: rest ->
            if List.exists (fun x -> x = id) id_l then
              err ("one variable is bound several times in this expression")
            else
              let tyarg1 = ty_exp tyenv exp1 in
              let newtyenv = Environment.extend id tyarg1 tyenv' in
                ty_let_list rest newtyenv (id :: id_l)                                      
      in 
        ty_let_list l tyenv []
  | _ -> err ("Not Implemented!")

let ty_decl tyenv = function
    Exp e -> let t = ty_exp tyenv e in [[("-", tyenv, t)]]
  | Decls l ->
      let rec make_decl_ty_list l tyenv =
     (match l with
        [] -> [[]]
      | head :: outer_rest -> 
          let rec make_anddecl_ty_list l tyenv' id_l =
           (match l with
              [] -> tyenv := tyenv';
                    []
            | (id, e) :: inner_rest ->
                if List.exists (fun x -> x = id) id_l then
                  err ("one variable is bound several times in this expression")
                else 
                  let t = ty_exp !tyenv e in
                  let newtyenv = Environment.extend id t tyenv' in
                    (id, newtyenv, t) :: make_anddecl_ty_list inner_rest newtyenv (id :: id_l))
           in
             let and_list = make_anddecl_ty_list head !tyenv [] in
               and_list :: make_decl_ty_list outer_rest tyenv)
      in
        make_decl_ty_list l (ref tyenv)
  | _ -> err ("Not Implemented!")
