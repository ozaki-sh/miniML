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


let rec ty_of_attached_ty = function
    Tyint -> TyInt
  | Tybool -> TyBool
  | Tyfun (domty, ranty) -> TyFun (ty_of_attached_ty domty, ty_of_attached_ty ranty)
  | Tylist ty -> TyList (ty_of_attached_ty ty)
  | TransformedTyvar tyvar -> TyVar tyvar

let make_eqs_about_att_ty ty attached_ty_list =
  let rec main_loop = function
    [] -> []
  | attached_ty :: rest ->
      match attached_ty with
        Ranty ty' -> (ty, TyFun (TyVar (fresh_tyvar ()), ty_of_attached_ty ty')) :: main_loop rest
      | ty' -> (ty, ty_of_attached_ty ty') :: main_loop rest
  in
    main_loop attached_ty_list 
      

let rec pattern_match pattern ty =
  match pattern, ty with
    (ILit _, att_ty), TyInt -> ([], [], make_eqs_about_att_ty ty att_ty)
  | (ILit _, att_ty), TyVar tyvar -> ([], [(tyvar, TyInt)], make_eqs_about_att_ty ty att_ty)
  | (BLit _, att_ty), TyBool -> ([], [], make_eqs_about_att_ty ty att_ty)
  | (BLit _, att_ty), TyVar tyvar -> ([], [(tyvar, TyBool)], make_eqs_about_att_ty ty att_ty)
  | (Var id, att_ty), _ -> ([(id, ty)], [], make_eqs_about_att_ty ty att_ty)
  | (ListExp Emp, att_ty), TyList _ -> ([], [], make_eqs_about_att_ty ty att_ty)
  | (ListExp Emp, att_ty), TyVar tyvar -> ([], [(tyvar, TyList (TyVar (fresh_tyvar ())))], make_eqs_about_att_ty ty att_ty)
  | (ListExp (Cons (pt, Emp)), att_ty), TyList ty' -> 
      let (id_and_ty_list, subst_list, eqs) = pattern_match pt ty' in
      (id_and_ty_list, subst_list, (make_eqs_about_att_ty ty att_ty) @ eqs)
  | (ListExp (Cons (pt, Emp)), att_ty), TyVar tyvar -> 
      let newTyVar = TyVar (fresh_tyvar ()) in
      let (id_and_ty_list, subst_list, eqs) = pattern_match pt newTyVar in
      (id_and_ty_list, (tyvar, TyList newTyVar) :: subst_list, (make_eqs_about_att_ty ty att_ty) @ eqs)
  | (ListExp (Cons (pt1, (Cons (pt2, Emp)))), att_ty), TyList ty' ->
      let (id_and_ty_list1, subst_list1, eqs1) = pattern_match pt1 ty' in
      let (id_and_ty_list2, subst_list2, eqs2) = pattern_match pt2 ty in
      (id_and_ty_list1 @ id_and_ty_list2, subst_list1 @ subst_list2, (make_eqs_about_att_ty ty att_ty) @ eqs1 @ eqs2)
  | (ListExp (Cons (pt1, (Cons (pt2, Emp)))), att_ty), TyVar tyvar ->
      let newTyVar = TyVar (fresh_tyvar ()) in
      let (id_and_ty_list1, subst_list1, eqs1) = pattern_match pt1 newTyVar in
      let (id_and_ty_list2, subst_list2, eqs2) = pattern_match pt2 ty in
      (id_and_ty_list1 @ id_and_ty_list2, (tyvar, TyList newTyVar) :: (subst_list1 @ subst_list2), (make_eqs_about_att_ty ty att_ty) @ eqs1 @ eqs2)
  | (Wildcard, att_ty), _ -> ([], [], make_eqs_about_att_ty ty att_ty)
  | _ -> err ("expression must have same type as pattern")

let rec make_ty_eqs_list = function
    [] -> []
  | [ty] -> []
  | ty1 :: ty2 :: rest -> (ty1, ty2) :: make_ty_eqs_list (ty2 :: rest)



let rec get_attached_ty_list (exp, att_ty) =
  let from_exp exp =
    let rec from_id_exp_list = function
        [] -> []
      | ((id, ty), exp) :: rest -> ty @ (get_attached_ty_list exp) @ from_id_exp_list rest
    and from_listExp = function
        Emp -> []
      | Cons (exp, l) -> (get_attached_ty_list exp) @ from_listExp l
    and from_exp_list = function
        [] -> []
      | exp :: rest -> (get_attached_ty_list exp) @ from_exp_list rest
    and from_explist_exp_list = function
        [] -> []
      | (explist, exp) :: rest -> (from_exp_list explist) @ (get_attached_ty_list exp) @ from_explist_exp_list rest
    in 
      match exp with
        Var _
      | ILit _
      | BLit _ -> []
      | BinOp (_, exp1, exp2) -> (get_attached_ty_list exp1) @ (get_attached_ty_list exp2)
      | BinLogicOp (_, exp1, exp2) -> (get_attached_ty_list exp1) @ (get_attached_ty_list exp2)
      | IfExp (exp1, exp2, exp3) -> (get_attached_ty_list exp1) @ (get_attached_ty_list exp2) @ (get_attached_ty_list exp3)
      | LetExp (l, exp) -> (from_id_exp_list l) @ (get_attached_ty_list exp)
      | FunExp ((id, ty), exp) -> ty @ (get_attached_ty_list exp)
      | DFunExp ((id, ty), exp) -> ty @ (get_attached_ty_list exp)
      | AppExp (exp1, exp2) -> (get_attached_ty_list exp1) @ (get_attached_ty_list exp2)
      | LetRecExp (l, exp) -> (from_id_exp_list l) @ (get_attached_ty_list exp)
      | ListExp listExp -> from_listExp listExp
      | MatchExp (l1, l2) -> (from_exp_list l1) @ (from_explist_exp_list l2)
      | Wildcard -> []
  in
    (from_exp exp) @ att_ty

let rec get_attached_ty_list_from_decl = function
    [] -> []
  | ((id, att_ty), exp) :: rest -> att_ty @ (get_attached_ty_list exp) @ get_attached_ty_list_from_decl rest

let rec get_attached_tyvar_list = function
    Tyint -> []
  | Tybool -> []
  | Tyvar tyvar -> [Tyvar tyvar]
  | Tyfun (domty, ranty) -> (get_attached_tyvar_list domty) @ (get_attached_tyvar_list ranty)
  | Tylist ty -> get_attached_tyvar_list ty
  | Ranty ty -> get_attached_tyvar_list ty


let make_Tyvar_to_TyVar_list exp =
  let rec main_loop used_list = function
      [] -> []
    | attached_ty :: rest ->
        match attached_ty with
          Tyvar tyvar ->
            if List.exists (fun x -> x = tyvar) used_list then main_loop used_list rest
            else (tyvar, (fresh_tyvar ())) :: main_loop (tyvar :: used_list) rest
  in
    let attached_ty_list = get_attached_ty_list exp in
    let attached_tyvar_list = List.concat (List.map (get_attached_tyvar_list) attached_ty_list) in
    main_loop [] attached_tyvar_list

let make_Tyvar_to_TyVar_list_for_decl decl =
  let rec main_loop used_list = function
      [] -> []
    | attached_ty :: rest ->
        match attached_ty with
          Tyvar tyvar ->
            if List.exists (fun x -> x = tyvar) used_list then main_loop used_list rest
            else (tyvar, (fresh_tyvar ())) :: main_loop (tyvar :: used_list) rest
  in
    let attached_ty_list = get_attached_ty_list_from_decl decl in
    let attached_tyvar_list = List.concat (List.map (get_attached_tyvar_list) attached_ty_list) in
    main_loop [] attached_tyvar_list


let rec transform exp_with_ty stv_to_itv_list =
  let rec transform_att_ty = function
      Tyint -> Tyint
    | Tybool -> Tybool
    | Tyvar tyvar -> TransformedTyvar (List.assoc tyvar stv_to_itv_list)
    | Tyfun (domty, ranty) -> Tyfun (transform_att_ty domty, transform_att_ty ranty)
    | Tylist ty -> Tylist (transform_att_ty ty)
    | Ranty ty -> Ranty (transform_att_ty ty)
  and transform_att_ty_list = function
    [] -> []
  | attached_ty :: rest -> (transform_att_ty attached_ty) :: transform_att_ty_list rest
  and body_func (exp, att_ty) = 
    let transform_exp exp =
      let rec transform_id_exp_list = function
          [] -> []
        | ((id, ty), exp) :: rest -> ((id, transform_att_ty_list ty), body_func exp) :: transform_id_exp_list rest
      and transform_listExp = function
          Emp -> Emp
        | Cons (exp, l) -> Cons (body_func exp, transform_listExp l)
      and transform_exp_list = function
          [] -> []
        | exp :: rest -> (body_func exp) :: transform_exp_list rest
      and transform_explist_exp_list = function
          [] -> []
        | (explist, exp) :: rest -> (transform_exp_list explist, body_func exp) :: transform_explist_exp_list rest
      in
        match exp with
          Var x -> Var x
        | ILit i -> ILit i
        | BLit b -> BLit b
        | BinOp (op, exp1, exp2) -> BinOp (op, body_func exp1, body_func exp2)
        | BinLogicOp (op, exp1, exp2) -> BinLogicOp (op, body_func exp1, body_func exp2)
        | IfExp (exp1, exp2, exp3) -> IfExp (body_func exp1, body_func exp2, body_func exp3)
        | LetExp (l, exp) -> LetExp (transform_id_exp_list l, body_func exp)
        | FunExp ((id, ty), exp) -> FunExp ((id, transform_att_ty_list ty), body_func exp)
        | DFunExp ((id, ty), exp) -> DFunExp ((id, transform_att_ty_list ty), body_func exp)
        | AppExp (exp1, exp2) -> AppExp (body_func exp1, body_func exp2)
        | LetRecExp (l, exp) -> LetRecExp (transform_id_exp_list l, body_func exp)
        | ListExp listExp -> ListExp (transform_listExp listExp)
        | MatchExp (l1, l2) -> MatchExp (transform_exp_list l1, transform_explist_exp_list l2)
        | Wildcard -> Wildcard
    in
      (transform_exp exp, transform_att_ty_list att_ty)
  in
    body_func exp_with_ty
      
let rec transform_decl decl stv_to_itv_list =
  let rec transform_att_ty = function
      Tyint -> Tyint
    | Tybool -> Tybool
    | Tyvar tyvar -> TransformedTyvar (List.assoc tyvar stv_to_itv_list)
    | Tyfun (domty, ranty) -> Tyfun (transform_att_ty domty, transform_att_ty ranty)
    | Tylist ty -> Tylist (transform_att_ty ty)
    | Ranty ty -> Ranty (transform_att_ty ty)
  and transform_att_ty_list = function
    [] -> []
  | attached_ty :: rest -> (transform_att_ty attached_ty) :: transform_att_ty_list rest
  in
    match decl with
      [] -> []
    | ((id, att_ty), exp) :: rest -> ((id, transform_att_ty_list att_ty), transform exp stv_to_itv_list) :: transform_decl rest stv_to_itv_list
    




(* for debug *)
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
    (Var x, att_ty) -> 
      (try
        let TyScheme (vars, ty) = Environment.lookup x tyenv in
        let s1 = List.map (fun id -> (id, TyVar (fresh_tyvar ()))) vars in
        let ty' = subst_type s1 ty in
        let eqs = make_eqs_about_att_ty ty' att_ty in
        let s2 = unify eqs in
          (s2, subst_type s2 ty')
       with Environment.Not_bound -> err ("variable not bound: " ^ x))
  | (ILit _, att_ty) -> 
      let eqs = make_eqs_about_att_ty TyInt att_ty in
      let s = unify eqs in
      (s, TyInt)
  | (BLit _, att_ty) ->
      let eqs = make_eqs_about_att_ty TyBool att_ty in
      let s = unify eqs in
      (s, TyBool)
  | (BinOp (op, exp1, exp2), att_ty)->
      let (s1, ty1) = ty_exp tyenv exp1 in
      let (s2, ty2) = ty_exp tyenv exp2 in
      let (eqs3, ty) =  ty_prim op ty1 ty2 in
      let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ eqs3 @ (make_eqs_about_att_ty ty att_ty) in
      let s3 = unify eqs in
      (s3, subst_type s3 ty)
  | (BinLogicOp (op, exp1, exp2), att_ty) ->
      let (s1, ty1) = ty_exp tyenv exp1 in
      let (s2, ty2) = ty_exp tyenv exp2 in
      let (eqs3, ty) =  ty_logic_prim op ty1 ty2 in
      let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ eqs3 @ (make_eqs_about_att_ty ty att_ty) in
      let s3 = unify eqs in
      (s3, subst_type s3 ty)
  | (IfExp (exp1, exp2, exp3), att_ty) ->
      let (s1, ty1) = ty_exp tyenv exp1 in
      let (s2, ty2) = ty_exp tyenv exp2 in
      let (s3, ty3) = ty_exp tyenv exp3 in
      let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ (eqs_of_subst s3) @ [(ty1, TyBool); (ty2, ty3)] 
                @ (make_eqs_about_att_ty ty2 att_ty) in
      let s4 = unify eqs in
      (s4, subst_type s4 ty2)
  | (LetExp (l, exp2), att_ty) ->
      let rec ty_let_list l tyenv' subst id_l =
        match l with
          [] -> 
            let (s3, ty2) = ty_exp tyenv' exp2 in
            let eqs = (eqs_of_subst subst) @ (eqs_of_subst s3) @ (make_eqs_about_att_ty ty2 att_ty) in
            let s4 = unify eqs in
            (s4, subst_type s4 ty2)
        | ((id, att_ty'), exp1) :: rest ->
            if List.exists (fun x -> x = id) id_l then
              err ("one variable is bound several times in this expression")
            else
              let (s1, ty1) = ty_exp tyenv exp1 in
              let eqs = (eqs_of_subst s1) @ (make_eqs_about_att_ty ty1 att_ty') in
              let s2 = unify eqs in
              let tysc = closure ty1 tyenv s2 in
              let newtyenv = Environment.extend id tysc tyenv' in
              ty_let_list rest newtyenv (s2 @ subst) (id :: id_l) 
      in
        ty_let_list l tyenv [] []
  | (FunExp ((id, att_ty'), exp), att_ty) ->
      let domty = TyVar (fresh_tyvar ()) in
      let (s1, ranty) = ty_exp (Environment.extend id (TyScheme ([], domty)) tyenv) exp in
      let ty = TyFun (subst_type s1 domty, ranty) in
      let eqs = (eqs_of_subst s1) @ (make_eqs_about_att_ty (subst_type s1 domty) att_ty') @ (make_eqs_about_att_ty ty att_ty) in 
      let s2 = unify eqs in 
      (s2, subst_type s2 ty)
  | (AppExp (exp1, exp2), att_ty) ->
      let (s1, ty1) = ty_exp tyenv exp1 in
      let (s2, ty2) = ty_exp tyenv exp2 in
     (match ty1 with
        TyFun (domty, ranty) ->
          let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ [(domty, ty2)] @ (make_eqs_about_att_ty ranty att_ty) in
          let s3 = unify eqs in
          (s3, subst_type s3 ranty)
      | TyVar _  ->
          let domty = TyVar (fresh_tyvar ()) in
          let ranty = TyVar (fresh_tyvar ()) in
          let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ [(ty1, TyFun (domty, ranty)); (domty, ty2)] 
                    @ (make_eqs_about_att_ty ranty att_ty) in
          let s3 = unify eqs in
          (s3, subst_type s3 ranty)
      | _ -> err ("Non-function value is applied"))
  | (LetRecExp (l, exp2), att_ty) ->
      let rec main_loop l tyenv' exp_dom_ran_l id_l =
        match l with
          [] -> 
            let rec make_eqs_list = function
                [] -> []
              | ((FunExp ((para, att_ty1), exp), att_ty2), domty, ranty) :: rest ->
                  let (s, t) = ty_exp (Environment.extend para (TyScheme ([], domty)) tyenv') exp in
                  (eqs_of_subst s) :: [(t, ranty)] :: (make_eqs_about_att_ty (TyFun (domty, ranty)) att_ty2) 
                  :: (make_eqs_about_att_ty (subst_type s domty) att_ty1) :: make_eqs_list rest
            in
              let eqs_list = List.concat (make_eqs_list exp_dom_ran_l) in
              let rec make_newtyenv id_l =                
                match id_l with
                  [] -> tyenv
                | (id, att_ty) :: rest ->
                    let TyScheme (_, ty) = Environment.lookup id tyenv' in
                    let s1 = unify eqs_list in
                    let eqs = (eqs_of_subst s1) @ (make_eqs_about_att_ty (subst_type s1 ty) att_ty) in
                    let s2 = unify eqs in
                    let tysc = closure (subst_type s2 ty) tyenv s2 in
                    Environment.extend id tysc (make_newtyenv rest)
              in
                let newtyenv = make_newtyenv id_l in
                let (s2, ty2) = ty_exp newtyenv exp2 in
                let eqs = eqs_list @ (eqs_of_subst s2) @ (make_eqs_about_att_ty ty2 att_ty) in
                let s3 = unify eqs in
                (s3, subst_type s3 ty2)
        | (typed_id, exp) :: rest ->
            let (id, _) = typed_id in
            if List.mem_assoc id id_l then
              err ("one variable is bound several times in this expression")
            else
              let domty = TyVar (fresh_tyvar ()) in
              let ranty = TyVar (fresh_tyvar ()) in
              let newtyenv = Environment.extend id (TyScheme ([], (TyFun (domty, ranty)))) tyenv' in
              main_loop rest newtyenv ((exp, domty, ranty) :: exp_dom_ran_l) (typed_id :: id_l) 
      in
        main_loop l tyenv [] []      
  | (ListExp l, att_ty) ->
     (match l with
        Emp -> ([], TyList (TyVar (fresh_tyvar ())))
      | Cons (exp, l) ->
          let (s1, ty1) = ty_exp tyenv exp in
          let (s2, (TyList ty2)) = ty_exp tyenv ((ListExp l), []) in
          let eqs1 = (eqs_of_subst s1) @ (eqs_of_subst s2) @ [(ty2, ty1)] in
          let s3 = unify eqs1 in
          let ty3 = TyList (subst_type s3 ty1) in
          let eqs2 = (eqs_of_subst s3) @ (make_eqs_about_att_ty ty3 att_ty) in
          let s4 = unify eqs2 in
          (s4, subst_type s4 ty3))
  | (MatchExp (exps, pattern_and_body_list), att_ty) ->
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
            [] -> ([], [])
          | (patterns, body) :: rest ->
              let (id_and_ty_list, subst_list, eqs) = inner_loop patterns tys1 in
              if check_whether_duplication id_and_ty_list [] then
                err ("one variable is bound several times in this expression")
              else
                let newtyenv = bind_and_return_tyenv tyenv id_and_ty_list in
                let (subst, ty) = ty_exp newtyenv body in
                let (subst_ty_list, eqs_list) = outer_loop rest in
                ((subst @ subst_list, ty) :: subst_ty_list, eqs :: eqs_list)
        (* パターン列を順にマッチさせていく *)
        and inner_loop pt_l ty_l =
          match pt_l, ty_l with
            [pattern], [ty] -> pattern_match pattern ty
          | (pattern :: pattern_rest), (ty :: ty_rest) ->
              let (id_and_ty_list1, subst_list1, eqs1) = pattern_match pattern ty in
              let (id_and_ty_list2, subst_list2, eqs2) = inner_loop pattern_rest ty_rest in
              (id_and_ty_list1 @ id_and_ty_list2, subst_list1 @ subst_list2, eqs1 @ eqs2)
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
          let (subst_ty_list2, eqs_list) = outer_loop pattern_and_body_list in
          let (subst_list2, tys2) = List.split subst_ty_list2 in
          let subst2 = List.concat subst_list2 in
          let eqs2 = eqs_of_subst subst2 in
          let eqs3 = make_ty_eqs_list tys2 in
          let eqs4 = List.concat eqs_list in
          let eqs5 = eqs1 @ eqs2 @ eqs3 @ eqs4 in
          let s1 = unify eqs5 in
          let ty = subst_type s1 (List.hd tys2) in
          let eqs6 = (eqs_of_subst s1) @ (make_eqs_about_att_ty ty att_ty) in
          let s2 = unify eqs6 in
          (s2, subst_type s2 ty)
  | _ -> err ("Not Implemented!")

let ty_decl tyenv = function
    Exp e -> 
      let stringtyvar_to_inttyvar_list = make_Tyvar_to_TyVar_list e in
      let transformed_e = transform e stringtyvar_to_inttyvar_list in
      let (_, ty) = ty_exp tyenv transformed_e in [(tyenv, ty)]
 | Decls l ->
      let rec make_decl_ty_list l tyenv =
        match l with
          [] -> []
        | head :: outer_rest ->            
            let rec make_anddecl_ty_list l tyenv' id_l =
             (match l with
                [] -> tyenv := tyenv';
                      []
             | ((id, att_ty), e) :: inner_rest ->
                 if List.exists (fun x -> x = id) id_l then
                   err ("one variable is bound several times in this expression")
                 else
                   let (s1, ty) = ty_exp !tyenv e in
                   let eqs = (eqs_of_subst s1) @ (make_eqs_about_att_ty ty att_ty) in
                   let s2 = unify eqs in
                   let tysc = closure ty !tyenv s2 in
                   let newtyenv = Environment.extend id tysc tyenv' in
                   (newtyenv, subst_type s2 ty) :: make_anddecl_ty_list inner_rest newtyenv (id :: id_l))
            in
              let stringtyvar_to_inttyvar_list = make_Tyvar_to_TyVar_list_for_decl head in
              let transformed_head = transform_decl head stringtyvar_to_inttyvar_list in
              let and_list = make_anddecl_ty_list transformed_head !tyenv [] in
              and_list @ make_decl_ty_list outer_rest tyenv
      in
        make_decl_ty_list l (ref tyenv)
  | RecDecls l ->
      let rec make_recdecl_ty_list l tyenv =
       (match l with
          [] -> []
        | head :: outer_rest ->
            let rec make_andrecdecl_ty_list l and_tyenv exp_dom_ran_l id_l =
             (match l with
                [] -> 
                  let rec make_eqs = function
                      [] -> []
                    | ((FunExp ((para, att_ty1), body), att_ty2), domty, ranty) :: rest ->
                        let (s, t) = ty_exp (Environment.extend para (TyScheme ([], domty)) and_tyenv) body in
                        (eqs_of_subst s) :: [(t, ranty)] :: (make_eqs_about_att_ty (TyFun (domty, ranty)) att_ty2) 
                        :: (make_eqs_about_att_ty (subst_type s domty) att_ty1) :: make_eqs rest
                  and make_final_list s id_l tyenv'' =
                    match id_l with
                      [] -> tyenv := tyenv''; []
                    | (id, att_ty) :: id_rest ->
                      let TyScheme (_, ty) = Environment.lookup id and_tyenv in
                      let newty = subst_type s ty in
                      let eqs = (eqs_of_subst s) @ (make_eqs_about_att_ty newty att_ty) in
                      let s' = unify eqs in
                      let newerty = subst_type s' newty in
                      let tysc = closure newerty !tyenv s' in
                      let newtyenv = Environment.extend id tysc tyenv'' in
                      (newtyenv, newerty) :: make_final_list s' id_rest newtyenv
                  in
                    let eqs = List.concat (make_eqs exp_dom_ran_l) in
                    let s = unify eqs in
                    make_final_list s id_l and_tyenv                
              | (typed_id, exp) :: inner_rest ->
                  let (id, _) = typed_id in
                  if List.mem_assoc id id_l then
                    err ("one variable is bound several times in this expression")
                  else
                    let domty = TyVar (fresh_tyvar ()) in
                    let ranty = TyVar (fresh_tyvar ()) in
                    let newtyenv = Environment.extend id (TyScheme ([], (TyFun (domty, ranty)))) and_tyenv in
                    make_andrecdecl_ty_list inner_rest newtyenv ((exp, domty, ranty) :: exp_dom_ran_l) (typed_id :: id_l))
            in
              let stringtyvar_to_inttyvar_list = make_Tyvar_to_TyVar_list_for_decl head in
              let transformed_head = transform_decl head in
              let and_list = make_andrecdecl_ty_list head !tyenv [] [] in
              and_list @ make_recdecl_ty_list outer_rest tyenv)
      in
        make_recdecl_ty_list l (ref tyenv)
