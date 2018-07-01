open Syntax

type subst = (tyvar * ty) list

exception Error of string

let err s = raise (Error s)

let rec subst_type (subst : subst) t =
  let rec subst_one_type (tv, ty) t =
    match t with
      TyVar tv' when tv = tv' -> ty
    | TyFun (domty, ranty) -> TyFun (subst_one_type (tv, ty) domty, subst_one_type (tv, ty) ranty)
    | TyList ty' -> TyList (subst_one_type (tv, ty) ty')
    | _ -> t
  in
    match subst with
      [] -> t
    | head :: rest -> subst_type rest (subst_one_type head t)

let rec eqs_of_subst (s : subst) =
  match s with
    [] -> []
  | (tyvar, ty) :: rest -> (TyVar tyvar, ty) :: (eqs_of_subst rest)

let rec subst_eqs (s : subst) eqs =
  match eqs with
    [] -> []
  | (ty1, ty2) :: rest -> (subst_type s ty1, subst_type s ty2) :: subst_eqs s rest

let rec unify = function
    [] -> []
  | (ty1, ty2) :: rest ->
     (match ty1, ty2 with
        x, y when x = y -> unify rest
      | TyFun (dty1, rty1), TyFun (dty2, rty2) -> unify ((dty1, dty2) :: (rty1, rty2) :: rest)
      | TyVar alpha, _ ->
          if MySet.member alpha (freevar_ty ty2) then err ("Type error")
          else (alpha, ty2) :: unify (subst_eqs [(alpha, ty2)] rest)
      | _, TyVar alpha ->
          if MySet.member alpha (freevar_ty ty1) then err ("Type error")
          else (alpha, ty1) :: unify (subst_eqs [(alpha, ty1)] rest)
      | _ -> err ("Type error"))
      


let ty_prim op ty1 ty2 = match op with
    Plus -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)
  | Minus -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)
  | Mult -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)
  | Lt -> ([(ty1, TyInt); (ty2, TyInt)], TyBool)
  | Eq -> ([(ty1, ty2)], TyBool)
  | Cons -> 
     (match ty2 with
        TyList ty -> ([(ty, ty1)], ty2)
      | _ -> err ("right side must be list: ::"))

let ty_logic_prim op ty1 ty2 = match op with
    And -> ([(ty1, TyBool); (ty2, TyBool)], TyBool)
  | Or -> ([(ty1, TyBool); (ty2, TyBool)], TyBool)

let rec ty_exp tyenv = function
    Var x -> 
      (try ([], Environment.lookup x tyenv) with
         Environment.Not_bound -> err ("variable not bound: " ^ x))
  | ILit _ -> ([], TyInt)
  | BLit _ -> ([], TyBool)
  | BinOp (op, exp1, exp2)->
      let (s1, ty1) = ty_exp tyenv exp1 in
      let (s2, ty2) = ty_exp tyenv exp2 in
      let (eqs3, ty) =  ty_prim op ty1 ty2 in
      let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ eqs3 in
      let s3 = unify eqs in
      (s3, subst_type s3 ty)
  | BinLogicOp (op, exp1, exp2) ->
      let (s1, ty1) = ty_exp tyenv exp1 in
      let (s2, ty2) = ty_exp tyenv exp2 in
      let (eqs3, ty) =  ty_logic_prim op ty1 ty2 in
      let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ eqs3 in
      let s3 = unify eqs in
      (s3, subst_type s3 ty)
  | IfExp (exp1, exp2, exp3) ->
      let (s1, ty1) = ty_exp tyenv exp1 in
      let (s2, ty2) = ty_exp tyenv exp2 in
      let (s3, ty3) = ty_exp tyenv exp3 in
      let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ (eqs_of_subst s3) @ [(ty1, TyBool); (ty2, ty3)] in
      let s4 = unify eqs in
      (s4, subst_type s4 ty2)
  | LetExp (l, exp2) ->
      let rec ty_let_list l tyenv' subst id_l =
        match l with
          [] -> 
            let (s2, ty2) = ty_exp tyenv' exp2 in
            let eqs = (eqs_of_subst subst) @ (eqs_of_subst s2) in
            let s3 = unify eqs in
            (s3, subst_type s3 ty2)
        | (id, exp1) :: rest ->
            if List.exists (fun x -> x = id) id_l then
              err ("one variable is bound several times in this expression")
            else
              let (s1, ty1) = ty_exp tyenv exp1 in
              let newtyenv = Environment.extend id ty1 tyenv' in
              ty_let_list rest newtyenv (s1 @ subst) (id :: id_l) 
      in
        ty_let_list l tyenv [] []
  | FunExp (id, exp) ->
      let domty = TyVar (fresh_tyvar ()) in
      let (s, ranty) = ty_exp (Environment.extend id domty tyenv) exp in
      (s, TyFun (subst_type s domty, ranty))
  | AppExp (exp1, exp2) ->
      let (s1, ty1) = ty_exp tyenv exp1 in
      let (s2, ty2) = ty_exp tyenv exp2 in
     (match ty1 with
        TyFun (domty, ranty) ->
          let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ [(domty, ty2)] in
          let s3 = unify eqs in
          (s3, subst_type s3 ranty)
      | TyVar _  ->
          let domty = TyVar (fresh_tyvar ()) in
          let ranty = TyVar (fresh_tyvar ()) in
          let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ [(ty1, TyFun (domty, ranty)); (domty, ty2)] in
          let s3 = unify eqs in
          (s3, subst_type s3 ranty)
      | _ -> err ("Non-function value is applied"))
  | LetRecExp (l, exp2) ->
      let rec ty_letrec_list l tyenv para_ty_exp_l id_l =
        match l with
          [] -> 
            let rec make_subst = function
                [] -> []
              | (para, ty, exp) :: rest ->
                  let (s, _) = ty_exp (Environment.extend para ty !tyenv) exp in
                  s :: make_subst rest 
            in
              let s_list = List.concat (make_subst para_ty_exp_l) in
              let (s2, ty2) = ty_exp !tyenv exp2 in
              let eqs = (eqs_of_subst s_list) @ (eqs_of_subst s2) in
              let s3 = unify eqs in
              (s3, subst_type s3 ty2)
        | (id, para, exp1) :: rest ->
            if List.exists (fun x -> x = id) id_l then
              err ("one variable is bound several times in this expression")
            else
              let domty = TyVar (fresh_tyvar ()) in
              let ranty = TyVar (fresh_tyvar ()) in
              let newtyenv = Environment.extend id (TyFun (domty, ranty)) !tyenv in
              tyenv := newtyenv;
              ty_letrec_list rest tyenv ((para, domty, exp1) :: para_ty_exp_l) (id :: id_l) 
      in
        ty_letrec_list l (ref tyenv) [] []
  | ListExp l ->
     (match l with
        Emp -> ([], TyList (TyVar (fresh_tyvar ())))
      | Cons (exp, l) ->
          let (s1, ty1) = ty_exp tyenv exp in
          let (s2, ty2) = ty_exp tyenv (ListExp l) in
         (match ty2 with
            TyList ty ->
              let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ [(ty, ty1)] in
              let s3 = unify eqs in
              (s3, TyList (subst_type s3 ty1))
          | _ -> err ("This error cannot happen")))
 (* | MatchExp (exps, pattern_and_body_list)*)
  | _ -> err ("Not Implemented!")

let ty_decl tyenv = function
    Exp e -> let (_, ty) = ty_exp tyenv e in [(tyenv, ty)]
  | Decls l ->
      let rec make_decl_ty_list l tyenv =
        match l with
          [] -> []
        | head :: outer_rest ->
            let rec make_anddecl_ty_list l tyenv' id_l =
             (match l with
                [] -> tyenv := tyenv';
                      []
             | (id, e) :: inner_rest ->
                 if List.exists (fun x -> x = id) id_l then
                   err ("one variable is bound several times in this expression")
                 else
                   let (_, ty) = ty_exp !tyenv e in
                   let newtyenv = Environment.extend id ty tyenv' in
                   (newtyenv, ty) :: make_anddecl_ty_list inner_rest newtyenv (id :: id_l))
            in
              let and_list = make_anddecl_ty_list head !tyenv [] in
              and_list @ make_decl_ty_list outer_rest tyenv
      in
        make_decl_ty_list l (ref tyenv)
  | RecDecls l ->
      let rec make_recdecl_ty_list l tyenv =
       (match l with
          [] -> []
        | head :: outer_rest ->
            let rec make_andrecdecl_ty_list l tyenv' para_ty_body_l id_l =
             (match l with
                [] -> 
                  let rec make_subst_ty_list = function
                      [] -> []
                    | (para, ty, body) :: rest ->
                        let (s, t) = ty_exp (Environment.extend para ty tyenv') body in
                        (s, t) :: make_subst_ty_list rest 
                  and make_eqs = function
                      [] -> [[]]
                    | (s, _) :: rest -> (eqs_of_subst s) :: make_eqs rest
                  and make_final_list s id_l ptb_l st_l tyenv'' =
                    match id_l, ptb_l, st_l with
                      [], [], [] -> tyenv := tyenv''; []
                    | id :: id_rest, (_, domty, _) :: ptb_rest, (_, ranty) :: st_rest ->
                      let t = TyFun ((subst_type s domty), (subst_type s ranty)) in
                      let newtyenv = Environment.extend id t tyenv'' in
                      (newtyenv, t) :: make_final_list s id_rest ptb_rest st_rest newtyenv
                  in
                    let subst_ty_list = make_subst_ty_list para_ty_body_l in
                    let eqs = List.concat (make_eqs subst_ty_list) in
                    let s = unify eqs in
                    make_final_list s id_l para_ty_body_l subst_ty_list tyenv'                
              | (id, para, body) :: inner_rest ->
                  if List.exists (fun x -> x = id) id_l then
                    err ("one variable is bound several times in this expression")
                  else
                    let domty = TyVar (fresh_tyvar ()) in
                    let ranty = TyVar (fresh_tyvar ()) in
                    let newtyenv = Environment.extend id (TyFun (domty, ranty)) tyenv' in
                    make_andrecdecl_ty_list inner_rest newtyenv ((para, domty, body) :: para_ty_body_l) (id :: id_l))
            in
              let and_list = make_andrecdecl_ty_list head !tyenv [] [] in
              and_list @ make_recdecl_ty_list outer_rest tyenv)
      in
        make_recdecl_ty_list l (ref tyenv)
