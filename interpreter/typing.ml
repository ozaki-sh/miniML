open Syntax

type subst = (tyvar * ty) list
type tyenv = tysc Environment.t

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
      | TyList ty', TyList ty'' -> unify ((ty', ty'') :: rest)
      | TyVar alpha, _ ->
          if MySet.member alpha (freevar_ty ty2) then err ("Type error")
          else (alpha, ty2) :: unify (subst_eqs [(alpha, ty2)] rest)
      | _, TyVar alpha ->
          if MySet.member alpha (freevar_ty ty1) then err ("Type error")
          else (alpha, ty1) :: unify (subst_eqs [(alpha, ty1)] rest)
      | _ -> err ("Type error"))

let rec freevar_tyenv (tyenv : tyenv) =
  Environment.fold_right (fun x y -> MySet.union (freevar_tysc x) y) tyenv MySet.empty

let closure ty (tyenv : tyenv) subst =
  let fv_tyenv' = freevar_tyenv tyenv in
  let fv_tyenv =
    MySet.bigunion
      (MySet.map
        (fun id -> freevar_ty (subst_type subst (TyVar id))) 
        fv_tyenv') in
  let ids = MySet.diff (freevar_ty ty) fv_tyenv in
    TyScheme (MySet.to_list ids, ty)
      

let rec pattern_match pattern ty =
  match pattern, ty with
    ILit _, TyInt -> ([], [])
  | ILit _, TyVar tyvar -> ([], [(tyvar, TyInt)])
  | BLit _, TyBool -> ([], [])
  | BLit _, TyVar tyvar -> ([], [(tyvar, TyBool)])
  | Var id, _ -> ([(id, ty)], [])
  | ListExp Emp, TyList _ -> ([], [])
  | ListExp Emp, TyVar tyvar -> ([], [(tyvar, TyList (TyVar (fresh_tyvar ())))])
  | ListExp (Cons (pt, Emp)), TyList ty' -> pattern_match pt ty'
  | ListExp (Cons (pt, Emp)), TyVar tyvar -> 
      let newTyVar = TyVar (fresh_tyvar ()) in
      let (id_and_ty_list, subst_list) = pattern_match pt newTyVar in
      (id_and_ty_list, (tyvar, TyList newTyVar) :: subst_list)
  | ListExp (Cons (pt1, (Cons (pt2, Emp)))), TyList ty' ->
      let (id_and_ty_list1, subst_list1) = pattern_match pt1 ty' in
      let (id_and_ty_list2, subst_list2) = pattern_match pt2 ty in
      (id_and_ty_list1 @ id_and_ty_list2, subst_list1 @ subst_list2)
  | ListExp (Cons (pt1, (Cons (pt2, Emp)))), TyVar tyvar ->
      let newTyVar = TyVar (fresh_tyvar ()) in
      let (id_and_ty_list1, subst_list1) = pattern_match pt1 newTyVar in
      let (id_and_ty_list2, subst_list2) = pattern_match pt2 ty in
      (id_and_ty_list1 @ id_and_ty_list2, (tyvar, TyList newTyVar) :: (subst_list1 @ subst_list2))
  | Wildcard, _ -> ([], [])
  | _ -> err ("expression must have same type as pattern")

let rec make_ty_eqs_list = function
    [] -> []
  | [ty] -> []
  | ty1 :: ty2 :: rest -> (ty1, ty2) :: make_ty_eqs_list (ty2 :: rest)



let rec string_of_tyenv id_l tyenv =
  match id_l with
    [] -> ""
  | id :: rest -> "(" ^ id ^ ", " ^ (string_of_tysc (Environment.lookup id tyenv)) ^ ") " ^ string_of_tyenv rest tyenv

let rec string_of_eqs eqs =
  let rec make_dummyty = function
      [] -> TyInt
    | (ty1, ty2) :: rest -> TyFun ((TyFun (ty1, ty2)), make_dummyty rest)
  in
    let tyvar_string_list = make_tyvar_string_list (make_dummyty eqs) in
    let rec string_of_ty ty =
      match ty with
        TyInt -> "int"
      | TyBool -> "bool"
      | TyVar tyvar -> List.assoc tyvar tyvar_string_list
      | TyFun (TyFun (_, _) as domty, ranty) -> "(" ^ (string_of_ty domty) ^ ")" ^
                                                " -> " ^ (string_of_ty ranty)
      | TyFun (domty, ranty) -> (string_of_ty domty) ^ " -> " ^ (string_of_ty ranty)
      | TyList ty -> 
         (match ty with
            TyFun (_, _) -> "(" ^ (string_of_ty ty) ^ ")" ^ " list"
          | _ -> (string_of_ty ty) ^ " list")
    and string_of_tytuple (ty1, ty2) =
      "(" ^ (string_of_ty ty1) ^ ", " ^ (string_of_ty ty2) ^ ")"
    in
      "[" ^ (List.fold_right (fun x y -> x ^ " " ^ y) (List.map (string_of_tytuple) eqs) "") ^ "]"
  
        




let ty_prim op ty1 ty2 = match op with
    Plus -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)
  | Minus -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)
  | Mult -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)
  | Lt -> ([(ty1, TyInt); (ty2, TyInt)], TyBool)
  | Eq -> ([(ty1, ty2)], TyBool)
  | Cons -> 
     (match ty1, ty2 with
        TyList (TyVar alpha), TyList (TyVar beta) when alpha = beta -> ([], TyList ty2)
      | _, TyList _
      | _, TyVar _ -> ([(TyList ty1, ty2)], TyList ty1)
      | _ -> err ("right side must be list: ::"))

let ty_logic_prim op ty1 ty2 = match op with
    And -> ([(ty1, TyBool); (ty2, TyBool)], TyBool)
  | Or -> ([(ty1, TyBool); (ty2, TyBool)], TyBool)

let rec ty_exp tyenv = function
    Var x -> 
      (try
        let TyScheme (vars, ty) = Environment.lookup x tyenv in
        let s = List.map (fun id -> (id, TyVar (fresh_tyvar ()))) vars in
          ([], subst_type s ty)
       with Environment.Not_bound -> err ("variable not bound: " ^ x))
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
              let tysc = closure ty1 tyenv [] in
              let newtyenv = Environment.extend id tysc tyenv' in
              ty_let_list rest newtyenv (s1 @ subst) (id :: id_l) 
      in
        ty_let_list l tyenv [] []
  | FunExp (id, exp) ->
      let domty = TyVar (fresh_tyvar ()) in
      let (s, ranty) = ty_exp (Environment.extend id (TyScheme ([], domty)) tyenv) exp in
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
      let rec main_loop l tyenv' para_ty_exp_l id_l =
        match l with
          [] -> 
            let rec make_eqs_list = function
                [] -> []
              | (para, domty, ranty, exp) :: rest ->
                  let (s, t) = ty_exp (Environment.extend para (TyScheme ([], domty)) tyenv') exp in
                  (eqs_of_subst s) :: [(t, ranty)] :: make_eqs_list rest
            in
              print_string (string_of_tyenv id_l tyenv');
              print_newline();
              let eqs_list = List.concat (make_eqs_list para_ty_exp_l) in
              let rec make_newtyenv id_l =                
                match id_l with
                  [] -> tyenv
                | id :: rest ->
                    let TyScheme (_, ty) = Environment.lookup id tyenv' in
                    let tysc = closure (subst_type (unify eqs_list) ty) tyenv [] in
                    Environment.extend id tysc (make_newtyenv rest)
              in
                let newtyenv = make_newtyenv id_l in
                print_string (string_of_tyenv id_l newtyenv);
                print_newline();
                let (s2, ty2) = ty_exp newtyenv exp2 in
                let eqs = eqs_list @ (eqs_of_subst s2) in
                print_string (string_of_eqs eqs);
                print_newline();
                let s3 = unify eqs in
                print_string (string_of_eqs (eqs_of_subst s3));
                print_newline();
                (s3, subst_type s3 ty2)
        | (id, para, exp1) :: rest ->
            if List.exists (fun x -> x = id) id_l then
              err ("one variable is bound several times in this expression")
            else
              let domty = TyVar (fresh_tyvar ()) in
              let ranty = TyVar (fresh_tyvar ()) in
              let newtyenv = Environment.extend id (TyScheme ([], (TyFun (domty, ranty)))) tyenv' in
              main_loop rest newtyenv ((para, domty, ranty, exp1) :: para_ty_exp_l) (id :: id_l) 
      in
        main_loop l tyenv [] []      
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
  | MatchExp (exps, pattern_and_body_list) ->
      let rec ty_exps = function
          [] -> []
        | head :: rest ->
            (ty_exp tyenv head) :: ty_exps rest
      in
        let subst_ty_list1 = ty_exps exps in
        let (subst_list1, tys1) = List.split subst_ty_list1 in
        let subst1 = List.concat subst_list1 in
        let eqs1 = eqs_of_subst subst1 in
        let rec outer_loop = function
            [] -> []
          | (patterns, body) :: rest ->
              let (id_and_ty_list, subst_list) = inner_loop patterns tys1 in
              if check_whether_duplication id_and_ty_list [] then
                err ("one variable is bound several times in this expression")
              else
                let newtyenv = bind_and_return_tyenv tyenv id_and_ty_list in
                let (subst, ty) = ty_exp newtyenv body in
                (subst @ subst_list, ty) :: outer_loop rest
        (* パターン列を順にマッチさせていく *)
        and inner_loop pt_l ty_l =
          match pt_l, ty_l with
            [pattern], [ty] -> pattern_match pattern ty
          | (pattern :: pattern_rest), (ty :: ty_rest) ->
              let (id_and_ty_list1, subst_list1) = pattern_match pattern ty in
              let (id_and_ty_list2, subst_list2) = inner_loop pattern_rest ty_rest in
              (id_and_ty_list1 @ id_and_ty_list2, subst_list1 @ subst_list2)
          | _, _ -> err ("The number of patterns must be same as the number of expressions")
        (* 同一パターン列の中に同じ変数が現れてないかをチェック *)
        and check_whether_duplication checked_l id_l =
          match checked_l with
            [] -> false
          | (id, _) :: rest ->
              if List.exists (fun x -> x = id) id_l then true
              else check_whether_duplication rest (id :: id_l)
        (* パターンマッチの結果束縛する必要がある変数を束縛した環境を返す *)
        and bind_and_return_tyenv tyenv = function
            [] -> tyenv
          | (id, ty) :: rest ->
              let newtyenv = Environment.extend id (TyScheme ([], ty)) tyenv in
              bind_and_return_tyenv newtyenv rest 
        in
          let subst_ty_list2 = outer_loop pattern_and_body_list in
          let (subst_list2, tys2) = List.split subst_ty_list2 in
          let subst2 = List.concat subst_list2 in
          let eqs2 = eqs_of_subst subst2 in
          let eqs3 = make_ty_eqs_list tys2 in
          let eqs = eqs1 @ eqs2 @ eqs3 in
          let s = unify eqs in
          (s, subst_type s (List.hd tys2))
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
                   let tysc = closure ty !tyenv [] in
                   let newtyenv = Environment.extend id tysc tyenv' in
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
            let rec make_andrecdecl_ty_list l and_tyenv para_ty_body_l id_l =
             (match l with
                [] -> 
                  let rec make_eqs = function
                      [] -> []
                    | (para, domty, ranty, body) :: rest ->
                        let (s, t) = ty_exp (Environment.extend para (TyScheme ([], domty)) and_tyenv) body in
                        (eqs_of_subst s) :: [(t, ranty)] :: make_eqs rest 
                  and make_final_list s id_l tyenv'' =
                    match id_l with
                      [] -> tyenv := tyenv''; []
                    | id :: id_rest ->
                      let TyScheme (_, ty) = Environment.lookup id and_tyenv in
                      let newty = subst_type s ty in
                      let tysc = closure newty !tyenv [] in
                      let newtyenv = Environment.extend id tysc tyenv'' in
                      (newtyenv, newty) :: make_final_list s id_rest newtyenv
                  in
                    let eqs = List.concat (make_eqs para_ty_body_l) in
                    let s = unify eqs in
                    make_final_list s id_l and_tyenv                
              | (id, para, body) :: inner_rest ->
                  if List.exists (fun x -> x = id) id_l then
                    err ("one variable is bound several times in this expression")
                  else
                    let domty = TyVar (fresh_tyvar ()) in
                    let ranty = TyVar (fresh_tyvar ()) in
                    let newtyenv = Environment.extend id (TyScheme ([], (TyFun (domty, ranty)))) and_tyenv in
                    make_andrecdecl_ty_list inner_rest newtyenv ((para, domty, ranty, body) :: para_ty_body_l) (id :: id_l))
            in
              let and_list = make_andrecdecl_ty_list head !tyenv [] [] in
              and_list @ make_recdecl_ty_list outer_rest tyenv)
      in
        make_recdecl_ty_list l (ref tyenv)
