open Syntax

type subst = (tyvar * ty) list
type tyenv = tysc Environment.t

exception Error of string

let err s = raise (Error s)

let defenv = ref []
let rev_defenv = ref []

let rec subst_type (subst : subst) t =
  let rec subst_tytuple (tv, ty) tytup =
    match tytup with
      TyEmpT -> TyEmpT
    | TyConsT (ty', tytup') -> TyConsT (subst_one_type (tv, ty) ty', subst_tytuple (tv, ty) tytup')
  and subst_one_type (tv, ty) t =
    match t with
      TyVar tv' when tv = tv' -> ty
    | TyFun (domty, ranty) -> TyFun (subst_one_type (tv, ty) domty, subst_one_type (tv, ty) ranty)
    | TyList ty' -> TyList (subst_one_type (tv, ty) ty')
    | TyTuple tytup -> TyTuple (subst_tytuple (tv, ty) tytup)
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
      | TyTuple TyEmpT, TyTuple TyEmpT -> unify rest
      | TyTuple TyEmpT, TyTuple (TyConsT (_, _))
      | TyTuple (TyConsT (_, _)), TyTuple TyEmpT -> err ("Type error")
      | TyTuple (TyConsT (ty1', tytup1)), TyTuple (TyConsT (ty2', tytup2)) ->
         unify ((ty1', ty2') :: (TyTuple tytup1, TyTuple tytup2) :: rest)
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

let make_eqs_about_att_ty ty attached_ty_list =
  let rec main_loop = function
      [] -> []
    | attached_ty :: rest ->
       (ty, attached_ty) :: main_loop rest
  in
  main_loop attached_ty_list

(* (束縛すべき変数と型の組のリスト,型代入の集合,型注釈に関するeqsの集合)を返す *)
let rec pattern_match (pattern, att_ty) ty =
  let body_func pattern ty =
    match pattern, ty with
      ILit _, TyInt -> ([], [], [])
    | ILit _, TyVar tyvar -> ([], [(tyvar, TyInt)], [])
    | BLit _, TyBool -> ([], [], [])
    | BLit _, TyVar tyvar -> ([], [(tyvar, TyBool)], [])
    | SLit _, TyString -> ([], [], [])
    | SLit _, TyVar tyvar -> ([], [(tyvar, TyString)], [])
    | Var id, _ -> ([(id, ty)], [], [])
    | ListExp Emp, TyList _ -> ([], [], [])
    | ListExp Emp, TyVar tyvar -> ([], [(tyvar, TyList (TyVar (fresh_tyvar ())))], [])
    | ListExp (Cons (pt, Emp)), TyList ty' -> pattern_match pt ty'
    | ListExp (Cons (pt, Emp)), TyVar tyvar ->
       let newTyVar = TyVar (fresh_tyvar ()) in
       let (id_and_ty_list, subst_list, eqs) = pattern_match pt newTyVar in
       (id_and_ty_list, (tyvar, TyList newTyVar) :: subst_list, eqs)
    | ListExp (Cons (pt1, (Cons (pt2, Emp)))), TyList ty' ->
       let (id_and_ty_list1, subst_list1, eqs1) = pattern_match pt1 ty' in
       let (id_and_ty_list2, subst_list2, eqs2) = pattern_match pt2 ty in
       (id_and_ty_list1 @ id_and_ty_list2, subst_list1 @ subst_list2, eqs1 @ eqs2)
    | ListExp (Cons (pt1, (Cons (pt2, Emp)))), TyVar tyvar ->
       let newTyVar = TyVar (fresh_tyvar ()) in
       let (id_and_ty_list1, subst_list1, eqs1) = pattern_match pt1 newTyVar in
       let (id_and_ty_list2, subst_list2, eqs2) = pattern_match pt2 ty in
       (id_and_ty_list1 @ id_and_ty_list2, (tyvar, TyList newTyVar) :: (subst_list1 @ subst_list2), eqs1 @ eqs2)
    | TupleExp EmpT, TyTuple TyEmpT -> ([], [], [])
    | TupleExp (ConsT (pt, l)), TyTuple (TyConsT (ty, tytup)) ->
       let (id_and_ty_list1, subst_list1, eqs1) = pattern_match pt ty in
       let (id_and_ty_list2, subst_list2, eqs2) = pattern_match ((TupleExp l, [])) (TyTuple tytup) in
       (id_and_ty_list1 @ id_and_ty_list2, subst_list1 @ subst_list2, eqs1 @ eqs2)
    | Wildcard, _ -> ([], [], [])
    | _ -> err ("expression must have same type as pattern")
  in
  let (id_and_ty_list, subst_list, eqs) = body_func pattern ty in
  (id_and_ty_list, subst_list, (make_eqs_about_att_ty ty att_ty) @ eqs)

(* match文において各パターンにマッチしたときの本体式の型が同じであることを表現するeqsを作るための関数 *)
let rec make_ty_eqs_list = function
    [] -> []
  | [ty] -> []
  | ty1 :: ty2 :: rest -> (ty1, ty2) :: make_ty_eqs_list (ty2 :: rest)


(* ある式中に現れるすべての型注釈に使われている型のリストを返す *)
let rec get_attached_ty_list (exp, att_ty) =
  let from_exp exp =
    let rec from_id_exp_list = function
        [] -> []
      | ((id, ty), exp) :: rest -> ty @ (get_attached_ty_list exp) @ from_id_exp_list rest
    and from_listExp = function
        Emp -> []
      | Cons (exp, l) -> (get_attached_ty_list exp) @ from_listExp l
    and from_tupleExp = function
        EmpT -> []
      | ConsT (exp, l) -> (get_attached_ty_list exp) @ from_tupleExp l
    and from_exp_exp_list = function
        [] -> []
      | (exp1, exp2) :: rest -> (get_attached_ty_list exp1) @ (get_attached_ty_list exp2) @ from_exp_exp_list rest
    in
    match exp with
      Var _
    | ILit _
    | BLit _
    | SLit _ -> []
    | Constr (_, None) -> []
    | Constr (_, Some exp) -> get_attached_ty_list exp
    | BinOp (_, exp1, exp2) -> (get_attached_ty_list exp1) @ (get_attached_ty_list exp2)
    | BinLogicOp (_, exp1, exp2) -> (get_attached_ty_list exp1) @ (get_attached_ty_list exp2)
    | IfExp (exp1, exp2, exp3) -> (get_attached_ty_list exp1) @ (get_attached_ty_list exp2) @ (get_attached_ty_list exp3)
    | LetExp (l, exp) -> (from_id_exp_list l) @ (get_attached_ty_list exp)
    | FunExp ((id, ty), exp) -> ty @ (get_attached_ty_list exp)
    | DFunExp ((id, ty), exp) -> ty @ (get_attached_ty_list exp)
    | AppExp (exp1, exp2) -> (get_attached_ty_list exp1) @ (get_attached_ty_list exp2)
    | LetRecExp (l, exp) -> (from_id_exp_list l) @ (get_attached_ty_list exp)
    | ListExp listExp -> from_listExp listExp
    | MatchExp (exp, l) -> (get_attached_ty_list exp) @ (from_exp_exp_list l)
    | TupleExp tupleExp -> from_tupleExp tupleExp
    | Wildcard -> []
  in
  (from_exp exp) @ att_ty

(* let宣言、let rec宣言用 *)
let rec get_attached_ty_list_from_decl = function
    [] -> []
  | ((id, att_ty), exp) :: rest -> att_ty @ (get_attached_ty_list exp) @ get_attached_ty_list_from_decl rest

(* あるattached_tyに現れるすべてのTyStringVarのリストを返す *)
let rec get_attached_tyvar_list = function
    TyInt -> []
  | TyBool -> []
  | TyString -> []
  | TyVar _ -> []
  | TyStringVar tyvar -> [TyStringVar tyvar]
  | TyFun (domty, ranty) -> (get_attached_tyvar_list domty) @ (get_attached_tyvar_list ranty)
  | TyList ty -> get_attached_tyvar_list ty
  | TyTuple TyEmpT -> []
  | TyTuple (TyConsT (ty, tytup)) -> (get_attached_tyvar_list ty) @ (get_attached_tyvar_list (TyTuple tytup))
  | TyUser _ -> []
  | _ -> err ("For debug : this error cannot occur (get_attached_tyvar_list)")

(* attached_tyの型変数とtyの型変数の対応表を作る *)
let make_Tyvar_to_TyVar_list exp =
  let rec main_loop used_list = function
      [] -> []
    | attached_ty :: rest ->
       match attached_ty with
         TyStringVar tyvar ->
          if List.exists (fun x -> x = tyvar) used_list then main_loop used_list rest
          else (tyvar, (fresh_tyvar ())) :: main_loop (tyvar :: used_list) rest
       | _ -> err ("For debug : this error cannot occur (make_Tyvar_to_tyvar_list)")
  in
  (* 式中の型注釈に使われている型を集めて *)
  let attached_ty_list = get_attached_ty_list exp in
  (* その中からTyvar（型変数)だけ取り出す *)
  let attached_tyvar_list = List.concat (List.map (get_attached_tyvar_list) attached_ty_list) in
  main_loop [] attached_tyvar_list

(* let宣言、 let rec宣言用 *)
let make_Tyvar_to_TyVar_list_for_decl decl =
  let rec main_loop used_list = function
      [] -> []
    | attached_ty :: rest ->
       match attached_ty with
         TyStringVar tyvar ->
          if List.exists (fun x -> x = tyvar) used_list then main_loop used_list rest
          else (tyvar, (fresh_tyvar ())) :: main_loop (tyvar :: used_list) rest
       | _ -> err ("For debug : this error cannot occur (make_Tyvar_to_tyvar_list_for_decl)")
  in
  let attached_ty_list = get_attached_ty_list_from_decl decl in
  let attached_tyvar_list = List.concat (List.map (get_attached_tyvar_list) attached_ty_list) in
  main_loop [] attached_tyvar_list

(* 対応表を用いて型注釈に使われている型変数をstringで表現されたものからintで表現されたものに変換する *)
let rec transform exp_with_ty stv_to_itv_list =
  (* ある型に使われている型変数をすべて変換する *)
  let rec transform_att_ty = function
      TyInt -> TyInt
    | TyBool -> TyBool
    | TyString -> TyString
    | TyStringVar tyvar -> TyVar (List.assoc tyvar stv_to_itv_list)
    | TyFun (domty, ranty) -> TyFun (transform_att_ty domty, transform_att_ty ranty)
    | TyList ty -> TyList (transform_att_ty ty)
    | TyTuple tytup -> TyTuple (transform_att_tytuple tytup)
    | TyUser x -> TyUser x
    | _ -> err ("For debug : this error cannot occur")
  and transform_att_tytuple = function
      TyEmpT -> TyEmpT
    | TyConsT (ty, tytup) -> TyConsT (transform_att_ty ty, transform_att_tytuple tytup)
  (* ある型のリストに使われている型変数をすべて変換する *)
  and transform_att_ty_list = function
      [] -> []
    | attached_ty :: rest -> (transform_att_ty attached_ty) :: transform_att_ty_list rest
  (* 本体 *)
  and body_func (exp, att_ty) =
    let transform_exp exp =
      (* 各データ構造に対応 *)
      let rec transform_id_exp_list = function
          [] -> []
        | ((id, ty), exp) :: rest -> ((id, transform_att_ty_list ty), body_func exp) :: transform_id_exp_list rest
      and transform_listExp = function
          Emp -> Emp
        | Cons (exp, l) -> Cons (body_func exp, transform_listExp l)
      and transform_tupleExp = function
          EmpT -> EmpT
        | ConsT (exp, l) -> ConsT (body_func exp, transform_tupleExp l)
      and transform_exp_exp_list = function
          [] -> []
        | (exp1, exp2) :: rest -> (body_func exp1, body_func exp2) :: (transform_exp_exp_list rest)
      in
      match exp with
        Var x -> Var x
      | ILit i -> ILit i
      | BLit b -> BLit b
      | SLit s -> SLit s
      | Constr (id, None) -> Constr (id, None)
      | Constr (id, Some exp) -> Constr (id, Some (body_func exp))
      | BinOp (op, exp1, exp2) -> BinOp (op, body_func exp1, body_func exp2)
      | BinLogicOp (op, exp1, exp2) -> BinLogicOp (op, body_func exp1, body_func exp2)
      | IfExp (exp1, exp2, exp3) -> IfExp (body_func exp1, body_func exp2, body_func exp3)
      | LetExp (l, exp) -> LetExp (transform_id_exp_list l, body_func exp)
      | FunExp ((id, ty), exp) -> FunExp ((id, transform_att_ty_list ty), body_func exp)
      | DFunExp ((id, ty), exp) -> DFunExp ((id, transform_att_ty_list ty), body_func exp)
      | AppExp (exp1, exp2) -> AppExp (body_func exp1, body_func exp2)
      | LetRecExp (l, exp) -> LetRecExp (transform_id_exp_list l, body_func exp)
      | ListExp listExp -> ListExp (transform_listExp listExp)
      | MatchExp (l1, l2) -> MatchExp (body_func l1, transform_exp_exp_list l2)
      | TupleExp tupleExp -> TupleExp (transform_tupleExp tupleExp)
      | Wildcard -> Wildcard
    in
    (transform_exp exp, transform_att_ty_list att_ty)
  in
  body_func exp_with_ty

(* let宣言、 let rec宣言用 *)
let rec transform_decl decl stv_to_itv_list =
  let rec transform_att_ty = function
      TyInt -> TyInt
    | TyBool -> TyBool
    | TyString -> TyString
    | TyStringVar tyvar -> TyVar (List.assoc tyvar stv_to_itv_list)
    | TyFun (domty, ranty) -> TyFun (transform_att_ty domty, transform_att_ty ranty)
    | TyList ty -> TyList (transform_att_ty ty)
    | TyTuple tytup -> TyTuple (transform_att_tytuple tytup)
    | _ -> err ("For debug : this error cannot occur (transform_decl)")
  and transform_att_ty_list = function
      [] -> []
    | attached_ty :: rest -> (transform_att_ty attached_ty) :: transform_att_ty_list rest
  and transform_att_tytuple = function
      TyEmpT -> TyEmpT
    | TyConsT (ty, tytup) -> TyConsT (transform_att_ty ty, transform_att_tytuple tytup)
  in
  match decl with
    [] -> []
  | ((id, att_ty), exp) :: rest -> ((id, transform_att_ty_list att_ty), transform exp stv_to_itv_list) :: transform_decl rest stv_to_itv_list




let ty_prim op ty1 ty2 = match op with
    Plus -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)
  | Minus -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)
  | Mult -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)
  | Lt -> ([(ty1, TyInt); (ty2, TyInt)], TyBool)
  | Mt -> ([(ty1, TyInt); (ty2, TyInt)], TyBool)
  | Eq -> ([(ty1, ty2)], TyBool)
  | Cons ->
     (match ty1, ty2 with
        TyList (TyVar alpha), TyList (TyVar beta) when alpha = beta -> ([], TyList ty2)
      | _, TyList _
      | _, TyVar _ -> ([(TyList ty1, ty2)], TyList ty1)
      | _ -> err ("right side must be list: ::"))
  | Hat -> ([(ty1, TyString); (ty2, TyString)], TyString)
  | Expo -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)

let ty_logic_prim op ty1 ty2 = match op with
    And -> ([(ty1, TyBool); (ty2, TyBool)], TyBool)
  | Or -> ([(ty1, TyBool); (ty2, TyBool)], TyBool)

(* 値を返す前に型注釈に関してもチェックしている *)
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
  | (SLit _, att_ty) ->
     let eqs = make_eqs_about_att_ty TyString att_ty in
     let s = unify eqs in
     (s, TyString)
  | (Constr (id, tyop), att_ty) ->
     (try
        let tyuser_l = Rev_environment.lookup (Constructor (id, tyop)) rev_defenv in
        
  | (BinOp (op, exp1, exp2), att_ty) ->
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
          (* 本当に束縛すべき値を評価する *)
          let rec make_eqs_list = function
              [] -> []
            | ((FunExp ((para, att_ty1), exp), att_ty2), domty, ranty) :: rest ->
               let (s, t) = ty_exp (Environment.extend para (TyScheme ([], domty)) tyenv') exp in
               (eqs_of_subst s) :: [(t, ranty)] :: (make_eqs_about_att_ty (TyFun (domty, ranty)) att_ty2)
               :: (make_eqs_about_att_ty (subst_type s domty) att_ty1) :: make_eqs_list rest
            | _ -> err ("For debug : this error cannot occur")
          in
          let eqs_list = List.concat (make_eqs_list exp_dom_ran_l) in
          (* 本当に束縛すべき値を変数に束縛する *)
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
       (* まず変数が適当な関数に束縛されているようにする *)
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
        Emp ->
         let ty = TyList (TyVar (fresh_tyvar ())) in
         let eqs = make_eqs_about_att_ty ty att_ty in
         let s = unify eqs in
         (s, subst_type s ty)
      | Cons (exp, l) ->
         let (s1, ty1) = ty_exp tyenv exp in
         let (s2, ty2') = ty_exp tyenv ((ListExp l), []) in
         match ty2' with
           TyList ty2 ->
            let eqs1 = (eqs_of_subst s1) @ (eqs_of_subst s2) @ [(ty2, ty1)] in
            let s3 = unify eqs1 in
            let ty3 = TyList (subst_type s3 ty1) in
            let eqs2 = (eqs_of_subst s3) @ (make_eqs_about_att_ty ty3 att_ty) in
            let s4 = unify eqs2 in
            (s4, subst_type s4 ty3)
         | _ -> err ("For debug : this error cannot occur"))
  | (MatchExp (exp, pattern_and_body_list), att_ty) ->
     let (s1, ty) = ty_exp tyenv exp in
     let eqs1 = eqs_of_subst s1 in
     (* 各パターン列を評価 *)
     let rec main_loop = function
         [] -> ([], [])
       | (pattern, body) :: rest ->
          let (id_and_ty_list, subst_list, eqs) = pattern_match pattern ty in
          if check_whether_duplication id_and_ty_list [] then
            err ("one variable is bound several times in this expression")
          else
            let newtyenv = bind_and_return_tyenv tyenv id_and_ty_list in
            let (subst, ty) = ty_exp newtyenv body in
            let (subst_ty_list, eqs_list) = main_loop rest in
            ((subst @ subst_list, ty) :: subst_ty_list, eqs :: eqs_list)
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
     (* 単一化 *)
     let (subst_ty_list, eqs_list) = main_loop pattern_and_body_list in
     let (subst_list, tys) = List.split subst_ty_list in
     let s2 = List.concat subst_list in
     let eqs2 = eqs_of_subst s2 in
     let eqs3 = make_ty_eqs_list tys in
     let eqs4 = List.concat eqs_list in
     let eqs5 = eqs1 @ eqs2 @ eqs3 @ eqs4 in
     let s3 = unify eqs5 in
     let ty = subst_type s3 (List.hd tys) in
     let eqs6 = (eqs_of_subst s3) @ (make_eqs_about_att_ty ty att_ty) in
     let s4 = unify eqs6 in
     (s4, subst_type s4 ty)
  | (TupleExp l, att_ty) ->
     let rec ty_tupleExp l subst =
       match l with
         EmpT -> (subst, TyEmpT)
       | ConsT (exp, l') ->
          let (s, ty) = ty_exp tyenv exp in
          let (subst', tytuple) = ty_tupleExp l' subst in
          ((s @ subst'), TyConsT (ty, tytuple))
     in
     let (s1, tytuple) = ty_tupleExp l [] in
     let eqs1 = eqs_of_subst s1 in
     let s2 = unify eqs1 in
     let ty = subst_type s2 (TyTuple tytuple) in
     let eqs2 = (eqs_of_subst s2) @ (make_eqs_about_att_ty ty att_ty) in
     let s3 = unify eqs2 in
     (s3, subst_type s3 ty)
  | _ -> err ("not implemented yet")


let ty_decl tyenv defenv' rev_defenv' decl =
  defenv := defenv'; rev_defenv := rev_defenv';
  match decl with
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
                  err ("one variable is bound several times in this declaration")
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
                 (* 本当に束縛すべき値を評価する *)
                 let rec make_eqs = function
                     [] -> []
                   | ((FunExp ((para, att_ty1), body), att_ty2), domty, ranty) :: rest ->
                      let (s, t) = ty_exp (Environment.extend para (TyScheme ([], domty)) and_tyenv) body in
                      (eqs_of_subst s) :: [(t, ranty)] :: (make_eqs_about_att_ty (TyFun (domty, ranty)) att_ty2)
                      :: (make_eqs_about_att_ty (subst_type s domty) att_ty1) :: make_eqs rest
                   | _ -> err ("For debug : this error cannot occur")
                 (* 本当に束縛すべき値を変数に束縛する *)
                 and make_final_list s id_l tyenv' =
                   match id_l with
                     [] -> tyenv := tyenv'; [] (* andでつながれているものはすべて環境に追加したところで環境を更新 *)
                   | (id, att_ty) :: id_rest ->
                      let TyScheme (_, ty) = Environment.lookup id and_tyenv in
                      let newty = subst_type s ty in
                      let eqs = (eqs_of_subst s) @ (make_eqs_about_att_ty newty att_ty) in
                      let s' = unify eqs in
                      let newerty = subst_type s' newty in
                      let tysc = closure newerty !tyenv s' in (* ここの環境は外の環境 *)
                      let newtyenv = Environment.extend id tysc tyenv' in
                      (newtyenv, newerty) :: make_final_list s' id_rest newtyenv
                 in
                 let eqs = List.concat (make_eqs exp_dom_ran_l) in
                 let s = unify eqs in
                 make_final_list s id_l and_tyenv
              | (typed_id, exp) :: inner_rest ->
                 (* まず変数が適当な関数に束縛されているようにする *)
                 let (id, _) = typed_id in
                 if List.mem_assoc id id_l then
                   err ("one variable is bound several times in this declaration")
                 else
                   let domty = TyVar (fresh_tyvar ()) in
                   let ranty = TyVar (fresh_tyvar ()) in
                   let newtyenv = Environment.extend id (TyScheme ([], (TyFun (domty, ranty)))) and_tyenv in
                   make_andrecdecl_ty_list inner_rest newtyenv ((exp, domty, ranty) :: exp_dom_ran_l) (typed_id :: id_l))
           in
           let stringtyvar_to_inttyvar_list = make_Tyvar_to_TyVar_list_for_decl head in
           let transformed_head = transform_decl head stringtyvar_to_inttyvar_list in
           let and_list = make_andrecdecl_ty_list transformed_head !tyenv [] [] in
           and_list @ make_recdecl_ty_list outer_rest tyenv)
     in
     make_recdecl_ty_list l (ref tyenv)
