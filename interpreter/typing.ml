open Syntax

type subst = (tyvar * ty) list
type tyenv = tysc Environment.t
type defenv = (string list * tydecl list) Environment.t

exception Error of string
exception TypeError
exception Not_exact_matched of (ty option * ty option)

let err s = raise (Error s)

let (defenv : defenv ref) = ref Environment.empty
let (vardefenv : defenv ref) = ref Environment.empty
let recdefenv = ref Environment.empty
let rev_defenv = ref Rev_environment.empty

let rec subst_type (subst : subst) t =
  let rec subst_tytuple (tv, ty) tytup =
    match tytup with
      TyEmpT -> TyEmpT
    | TyConsT (ty', tytup') -> TyConsT (subst_one_type (tv, ty) ty', subst_tytuple (tv, ty) tytup')
  and subst_ty_list (tv, ty) l =
    match l with
      [] -> []
    | head :: rest -> subst_one_type (tv, ty) head :: subst_ty_list (tv, ty) rest
  and subst_one_type (tv, ty) t =
    match t with
      TyVar (tv', _) when tv = tv' -> ty
    | TyFun (domty, ranty) -> TyFun (subst_one_type (tv, ty) domty, subst_one_type (tv, ty) ranty)
    | TyList ty' -> TyList (subst_one_type (tv, ty) ty')
    | TyTuple tytup -> TyTuple (subst_tytuple (tv, ty) tytup)
    | TyVariant (x, l) -> TyVariant (x, subst_ty_list (tv, ty) l)
    | TyRecord (x, l) -> TyRecord (x, subst_ty_list (tv, ty) l)
    | TySet (tv', l) when tv = tv' -> ty
    | _ -> t
  in
  match subst with
    [] -> t
  | head :: rest -> subst_type rest (subst_one_type head t)

let rec eqs_of_subst (s : subst) =
  match s with
    [] -> []
  | (tyvar, ty) :: rest -> (TyVar (tyvar, Safe), ty) :: (eqs_of_subst rest)

let rec subst_eqs (s : subst) eqs =
  match eqs with
    [] -> []
  | (ty1, ty2) :: rest -> (subst_type s ty1, subst_type s ty2) :: subst_eqs s rest

let rec unify eqs =
  match eqs with
    [] -> []
  | (ty1, ty2) :: rest ->
     (match ty1, ty2 with
        x, y when x = y -> unify rest
      | TyFun (dty1, rty1), TyFun (dty2, rty2) -> unify ((dty1, dty2) :: (rty1, rty2) :: rest)
      | TyList ty', TyList ty'' -> unify ((ty', ty'') :: rest)
      | TyTuple TyEmpT, TyTuple TyEmpT -> unify rest
      | TyTuple TyEmpT, TyTuple (TyConsT (_, _))
      | TyTuple (TyConsT (_, _)), TyTuple TyEmpT -> raise TypeError
      | TyTuple (TyConsT (ty1', tytup1)), TyTuple (TyConsT (ty2', tytup2)) ->
         unify ((ty1', ty2') :: (TyTuple tytup1, TyTuple tytup2) :: rest)
      | TyVariant (name1, tys1), TyVariant (name2, tys2) when name1 = name2 && List.length tys1 = List.length tys2 ->
         unify ((List.combine tys1 tys2) @ rest)
      | TyRecord (name1, tys1), TyRecord (name2, tys2) when name1 = name2 && List.length tys1 = List.length tys2->
         unify ((List.combine tys1 tys2) @ rest)
      | TyVar (alpha, may_poly), _ -> (* TODO *)
         if MySet.member alpha (freevar_ty ty2) then raise TypeError
         else (alpha, ty2) :: unify (subst_eqs [(alpha, ty2)] rest)
      | _, TyVar (alpha, may_poly) ->
         if MySet.member alpha (freevar_ty ty1) then raise TypeError
         else (alpha, ty1) :: unify (subst_eqs [(alpha, ty1)] rest)
      | TyNone _, TyNone _ -> unify rest
      | TyNone name, _ -> err ("arguments not expected: " ^ name)
      | _, TyNone name -> err ("arguments expected: " ^ name)
      | TySet (alpha, l1), TySet (beta, l2) ->
         let l = MySet.intersection l1 l2 in
         (match (MySet.to_list l) with
            [] -> raise TypeError
          | [ty] -> (alpha, ty) :: (beta, ty) :: unify (subst_eqs [(alpha, ty); (beta, ty)] rest)
          | _ ->
             let ty' = TySet (alpha, l) in
             let ty'' = TySet (beta, l) in
             (alpha, ty') :: (beta, ty'') :: unify (subst_eqs [(alpha, ty'); (beta, ty'')] rest))
      | TySet (alpha, l1), _ ->
         if MySet.member ty2 l1 then (alpha, ty2) :: unify (subst_eqs [(alpha, ty2)] rest) else raise TypeError
      | _, TySet (alpha, l2) ->
         if MySet.member ty1 l2 then (alpha, ty1) :: unify (subst_eqs [(alpha, ty1)] rest) else raise TypeError
      | _ -> raise TypeError)


let rec reflect_dependency dependent_relation (s : subst) =
  match s with
    [] -> []
  | (tyvar, ty) :: rest ->
     (try
        (List.assoc (tyvar, ty) dependent_relation) :: reflect_dependency dependent_relation rest
      with
        Not_found -> reflect_dependency dependent_relation rest)

let squeeze_subst (s : subst) =
  let rec squeeze ty_list ty =
    match ty_list with
      [] -> ty
    | head :: rest ->
       (match head, ty with
          TySet (alpha, l1), TySet (_, l2) ->
           let l = MySet.to_list (MySet.intersection l1 l2) in
           (match l with
              [] -> raise TypeError
            | [ty'] -> squeeze rest ty'
            | _ -> squeeze rest (TySet (alpha, MySet.from_list l)))
        | TySet (_, l1), _ ->
           if MySet.member ty l1 then squeeze rest ty else raise TypeError
        | _, TySet (_, l2) ->
           if MySet.member head l2 then squeeze rest head else raise TypeError
        | x, y when x = y -> squeeze rest ty
        | _ -> raise TypeError)
  and body_func tyvar_set =
    match tyvar_set with
      [] -> []
    | head :: rest ->
       let (_, ty_list) = List.split (List.filter (fun (x, _) -> x = head) s) in
       (head, squeeze (List.tl ty_list) (List.hd ty_list)) :: body_func rest
  in
  let (tyvar_list, _) = List.split s in
  let tyvar_set = MySet.to_list (MySet.from_list tyvar_list) in
  body_func tyvar_set

let rec delete_TySet ty =
  let rec case_tytuple tytup =
    match tytup with
      TyEmpT -> TyEmpT
    | TyConsT (ty', tytup') -> TyConsT (delete_TySet ty', case_tytuple tytup')
  and case_ty_list l =
    match l with
      [] -> []
    | head :: rest -> delete_TySet head :: case_ty_list rest
  in
  match ty with
    TySet (_, l) -> List.hd (MySet.to_list l)
  | TyList ty -> TyList (delete_TySet ty)
  | TyTuple tytup -> TyTuple (case_tytuple tytup)
  | TyVariant (x, l) -> TyVariant (x, case_ty_list l)
  | TyRecord (x, l) -> TyRecord (x, case_ty_list l)
  | _ -> ty

let finalize_subst (s: subst) =
  List.map (fun (x, y) -> (x, delete_TySet y)) s


let rec freevar_tyenv (tyenv : tyenv) =
  Environment.fold_right (fun x y -> MySet.union (freevar_tysc x) y) tyenv MySet.empty

let closure ty (tyenv : tyenv) subst =
  let fv_tyenv' = freevar_tyenv tyenv in
  let fv_tyenv =
    MySet.bigunion
      (MySet.map
         (fun id -> freevar_ty (subst_type subst (TyVar (id, Safe))))
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

let rec make_dependent_relation alpha beta l =
  match l with
    [] -> []
  | (arg_ty, this_ty) :: rest ->
     ((alpha, this_ty), (beta, arg_ty)) :: make_dependent_relation alpha beta rest


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
    and from_recordExp = function
        EmpR -> []
      | ConsR ((_, exp), l) -> (get_attached_ty_list exp) @ from_recordExp l
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
    | Record recordExp -> from_recordExp recordExp
    | RecordWith (exp, recordExp) -> (get_attached_ty_list exp) @ (from_recordExp recordExp)
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
    | RecordPattern recordExp -> from_recordExp recordExp
    | AssignExp (exp1, _, exp2) -> (get_attached_ty_list exp1) @ (get_attached_ty_list exp2)
    | Unit -> []
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
  | TyStringVar tyvar -> [TyStringVar tyvar]
  | TyFun (domty, ranty) -> (get_attached_tyvar_list domty) @ (get_attached_tyvar_list ranty)
  | TyList ty -> get_attached_tyvar_list ty
  | TyTuple TyEmpT -> []
  | TyTuple (TyConsT (ty, tytup)) -> (get_attached_tyvar_list ty) @ (get_attached_tyvar_list (TyTuple tytup))
  | TyUser (_, l) -> List.concat (List.map get_attached_tyvar_list l)
  | TyUnit -> []
  | _ -> err ("For debug : at get_attached_tyvar_list")

(* attached_tyの型変数とtyの型変数の対応表を作る *)
let make_Tyvar_to_TyVar_list exp =
  let rec main_loop used_list = function
      [] -> []
    | attached_ty :: rest ->
       match attached_ty with
         TyStringVar tyvar ->
          if List.exists (fun x -> x = tyvar) used_list then main_loop used_list rest
          else (tyvar, (fresh_tyvar ())) :: main_loop (tyvar :: used_list) rest
       | _ -> err ("For debug : at make_Tyvar_to_tyvar_list")
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
       | _ -> err ("For debug : at make_Tyvar_to_tyvar_list_for_decl")
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
    | TyStringVar tyvar -> TyVar ((List.assoc tyvar stv_to_itv_list), Safe)
    | TyFun (domty, ranty) -> TyFun (transform_att_ty domty, transform_att_ty ranty)
    | TyList ty -> TyList (transform_att_ty ty)
    | TyTuple tytup -> TyTuple (transform_att_tytuple tytup)
    | TyUser (x, tys) ->
       (try
          let (_, def) = Environment.dlookup x !defenv in
          let indexed_x = Environment.ilookup x !defenv in
          (match List.hd def with
             Constructor _ -> TyVariant (indexed_x, transform_att_ty_list tys)
           | Field _ -> TyRecord (indexed_x, transform_att_ty_list tys))
        with
          Environment.Not_bound -> err ("type not defined: " ^ x))
    | TyUnit -> TyUnit
    | _ -> err ("For debug : at transform_att_ty")
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
      and transform_recordExp = function
          EmpR -> EmpR
        | ConsR ((name, exp), l) -> ConsR ((name, body_func exp), transform_recordExp l)
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
      | Record recordExp -> Record (transform_recordExp recordExp)
      | RecordWith (exp, recordExp) -> RecordWith (body_func exp, transform_recordExp recordExp)
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
      | RecordPattern recordExp -> RecordPattern (transform_recordExp recordExp)
      | AssignExp (exp1, name, exp2) -> AssignExp (body_func exp1, name, body_func exp2)
      | Unit -> Unit
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
    | TyStringVar tyvar -> TyVar ((List.assoc tyvar stv_to_itv_list), Safe)
    | TyFun (domty, ranty) -> TyFun (transform_att_ty domty, transform_att_ty ranty)
    | TyList ty -> TyList (transform_att_ty ty)
    | TyTuple tytup -> TyTuple (transform_att_tytuple tytup)
    | TyUser (x, tys) ->
       (try
          let (_, def) = Environment.dlookup x !defenv in
          let indexed_x = Environment.ilookup x !defenv in
          (match List.hd def with
             Constructor _ -> TyVariant (indexed_x, transform_att_ty_list tys)
           | Field _ -> TyRecord (indexed_x, transform_att_ty_list tys))
        with
          Environment.Not_bound -> err ("type not defined: " ^ x))
    | TyUnit -> TyUnit
    | _ -> err ("For debug : at transform_decl")
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


let replace stv_to_itv_list ty =
  let rec body_func = function
      TyInt -> TyInt
    | TyBool -> TyBool
    | TyString -> TyString
    | TyStringVar tyvar -> TyVar ((List.assoc tyvar stv_to_itv_list), Safe)
    | TyFun (domty, ranty) -> TyFun (body_func domty, body_func ranty)
    | TyList ty' -> TyList (body_func ty')
    | TyTuple tytup -> TyTuple (case_tytuple tytup)
    | TyVariant (id, l) -> TyVariant (id, case_ty_list l)
    | TyRecord (id, l) -> TyRecord (id, case_ty_list l)
    | TyNone name -> TyNone name
    | TyUnit -> TyUnit
    | _ -> err ("For debug: at replace")
  and case_tytuple = function
      TyEmpT -> TyEmpT
    | TyConsT (ty', tytup') ->
       TyConsT (body_func ty', case_tytuple tytup')
  and case_ty_list = function
      [] -> []
    | head :: rest ->
       body_func head :: case_ty_list rest
  in
  body_func ty

let replace_another assoc_list ty =
  let rec body_func = function
      TyInt -> TyInt
    | TyBool -> TyBool
    | TyString -> TyString
    | TyStringVar tyvar -> List.assoc tyvar assoc_list
    | TyFun (domty, ranty) -> TyFun (body_func domty, body_func ranty)
    | TyList ty' -> TyList (body_func ty')
    | TyTuple tytup -> TyTuple (case_tytuple tytup)
    | TyVariant (id, l) -> TyVariant (id, case_ty_list l)
    | TyRecord (id, l) -> TyRecord (id, case_ty_list l)
    | TyNone name -> TyNone name
    | TyUnit -> TyUnit
    | _ -> err ("For debug: at replace")
  and case_tytuple = function
      TyEmpT -> TyEmpT
    | TyConsT (ty', tytup') ->
       TyConsT (body_func ty', case_tytuple tytup')
  and case_ty_list = function
      [] -> []
    | head :: rest ->
       body_func head :: case_ty_list rest
  in
  body_func ty



let ty_prim op ty1 ty2 = match op with
    Plus -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)
  | Minus -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)
  | Mult -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)
  | Lt -> ([(ty1, TyInt); (ty2, TyInt)], TyBool)
  | Mt -> ([(ty1, TyInt); (ty2, TyInt)], TyBool)
  | Eq -> ([(ty1, ty2)], TyBool)
  | Cons ->
     (match ty1, ty2 with
        TyList (TyVar (alpha, _)), TyList (TyVar (beta, _)) when alpha = beta -> ([], TyList ty2)
      | _, TyList _
      | _, TyVar _ -> ([(TyList ty1, ty2)], TyList ty1)
      | _ -> err ("right side must be list: ::"))
  | Hat -> ([(ty1, TyString); (ty2, TyString)], TyString)
  | Expo -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)

let ty_logic_prim op ty1 ty2 = match op with
    And -> ([(ty1, TyBool); (ty2, TyBool)], TyBool)
  | Or -> ([(ty1, TyBool); (ty2, TyBool)], TyBool)


let rec get_candidates is_first candidates name_l = function
    EmpR -> (MySet.to_list candidates, name_l)
  | ConsR ((name, _), rest) ->
     if List.mem name name_l then err ("The record field label " ^ name ^ " is defined several times")
     else
       (try
          let this_ty_names = List.map (fun (_, this_ty_name) -> this_ty_name) (Rev_environment.lookup name !rev_defenv) in
          if is_first then
            get_candidates false (MySet.from_list this_ty_names) (name :: name_l) rest
          else
            let now_candidates = MySet.intersection (MySet.from_list this_ty_names) candidates in
            if MySet.length now_candidates = 0 then
              let this_ty_name = List.hd this_ty_names in
                   let expected_ty_name = List.hd (MySet.to_list candidates) in
                   err ("The record field " ^ name ^ " belongs to type " ^ Syntax.remove_index (this_ty_name) ^ "\n"
                        ^ "       but is mixed here with fields of type " ^ Syntax.remove_index (expected_ty_name))
            else
              get_candidates false now_candidates (name :: name_l) rest
        with
          Rev_environment.Not_bound -> err ("record field not bound: " ^ name))

let rec filter_satisfied candidates name_l =
  match candidates with
    [] -> ([], "")
  | candidate :: rest ->
     let (_, body_l) = Environment.lookup candidate !recdefenv in
     let name_l' = List.map (fun x -> match x with Field (n, _, _) -> n | _ -> "" (* nonsense *)) body_l in
     let name_set = MySet.from_list name_l in
     let name_set' = MySet.from_list name_l' in
     let diff_set = MySet.diff name_set' name_set in
     if MySet.length diff_set = 0 then
       let (l', fo) = filter_satisfied rest name_l in
       (candidate :: l', fo)
     else
       let this_is_first_out = List.hd (MySet.to_list diff_set) in
       let (l', _) = filter_satisfied rest name_l in
       (l', this_is_first_out)

let rec make_name_beta_l = function
    [] -> []
  | name :: rest ->
     let beta = fresh_tyvar () in (* HHHHHEEEEERRRRREEEE *)
     (name, beta) :: make_name_beta_l rest

let rec make_this_ty_assoc_list = function
    [] -> []
  | head :: rest ->
     let (params, _) = Environment.lookup head !recdefenv in
     let tyvars = List.map (fun _ -> fresh_tyvar ()) params in
     (head, List.combine params tyvars) :: make_this_ty_assoc_list rest

let rec make_subst_and_rel tyenv alpha this_ty_l this_ty_assoc_list name_beta_l = function
    EmpR -> ([], [])
  | ConsR ((name, exp), rest) ->
     let (s, ty, rel) = ty_exp tyenv exp in
     let (s', rel') = make_subst_and_rel tyenv alpha this_ty_l this_ty_assoc_list name_beta_l rest in
     let beta = List.assoc name name_beta_l in
     let f (arg_ty, this_ty_name) =
       let stv_to_itv_list = List.assoc this_ty_name this_ty_assoc_list in
       let replaced_arg_ty = replace stv_to_itv_list arg_ty in
       let (_, tyvars) = List.split stv_to_itv_list in
       let tyVars = List.map (fun tyvar -> TyVar (tyvar, Safe)) tyvars in
       (replaced_arg_ty, TyRecord (this_ty_name, tyVars)) in
     let l = List.map f (List.filter (fun (_, this_ty) -> List.mem this_ty this_ty_l) (Rev_environment.lookup name !rev_defenv)) in
     let (field_ty_l, _) = List.split l in
     let s'' =
       if List.length l = 1 then
         unify [(TyVar (beta, Safe), List.hd field_ty_l); (TyVar (beta, Safe), ty)]
       else
         unify [(TyVar (beta, Safe), TySet (beta, MySet.from_list field_ty_l)); (TyVar (beta, Safe), ty)] in
     let rel'' = make_dependent_relation alpha beta l in
     (s @ s'' @ s', rel @ rel'' @ rel)

(* 値を返す前に型注釈に関してもチェックしている *)
and ty_exp tyenv = function
    (Var x, att_ty) ->
     (try
        let TyScheme (vars, ty) = Environment.lookup x tyenv in
        let s1 = List.map (fun id -> (id, TyVar ((fresh_tyvar (), Safe)))) vars in
        let ty' = subst_type s1 ty in
        let eqs = make_eqs_about_att_ty ty' att_ty in
        let s2 = unify eqs in
        (s2, subst_type s2 ty', [])
      with Environment.Not_bound -> err ("variable not bound: " ^ x))
  | (ILit _, att_ty) ->
     let eqs = make_eqs_about_att_ty TyInt att_ty in
     let s = unify eqs in
     (s, TyInt, [])
  | (BLit _, att_ty) ->
     let eqs = make_eqs_about_att_ty TyBool att_ty in
     let s = unify eqs in
     (s, TyBool, [])
  | (SLit _, att_ty) ->
     let eqs = make_eqs_about_att_ty TyString att_ty in
     let s = unify eqs in
     (s, TyString, [])
  | (Constr (name, expop), att_ty) ->
     (try
        let f (arg_ty, this_ty_name) =
          let (params, _) = Environment.lookup this_ty_name !vardefenv in
          let tyvars = List.map (fun _ -> fresh_tyvar ()) params in
          let tyVars = List.map (fun tyvar -> TyVar (tyvar, Safe)) tyvars in
          let replaced_arg_ty = replace (List.combine params tyvars) arg_ty in
          (replaced_arg_ty, TyVariant (this_ty_name, tyVars)) in
        let l = List.map f (Rev_environment.lookup name !rev_defenv) in
        let (arg_ty_l, this_ty_l) = List.split l in
        let (s1, arg_ty, arg_rel) =
          match expop with
            None -> ([], TyNone name, [])
          | Some exp -> ty_exp tyenv exp in
        let alpha = fresh_tyvar () in
        let beta = fresh_tyvar () in
        let rel = make_dependent_relation alpha beta l in
        let arg_ty_set = MySet.from_list arg_ty_l in
        let arg_s =
          if MySet.length arg_ty_set = 1 then
            unify [(TyVar (beta, Safe), List.hd arg_ty_l); (TyVar (beta, Safe), arg_ty)]
          else
            unify [(TyVar (beta, Safe), TySet (beta, arg_ty_set)); (TyVar (beta, Safe), arg_ty)] in
        let this_ty_set = MySet.from_list this_ty_l in
        let this_s =
          if MySet.length this_ty_set = 1 then
            [(alpha, List.hd this_ty_l)]
          else
            [(alpha, TySet (alpha, this_ty_set))] in
        let arg_eqs = eqs_of_subst (squeeze_subst arg_s) in
        let this_eqs = eqs_of_subst this_s in
        let eqs = (eqs_of_subst s1) @ arg_eqs @ this_eqs @ make_eqs_about_att_ty (TyVar (alpha, Safe)) att_ty in
        let s2 = squeeze_subst (unify eqs) in
        (s2, subst_type s2 (TyVar (alpha, Safe)), rel @ arg_rel)
      with
        Rev_environment.Not_bound -> err ("constructor not bound: " ^ name))
  | (Record l, att_ty) ->
     let (candidates, name_l) = get_candidates true MySet.empty [] l in
     let (this_ty_l, first_out) = filter_satisfied candidates name_l in
     if List.length this_ty_l = 0 then
       err ("Some record fields are undefined: " ^ first_out)
     else
       let alpha = fresh_tyvar () in
       let name_beta_l = make_name_beta_l name_l in
       let this_ty_assoc_list = make_this_ty_assoc_list this_ty_l in
       let f this_ty_name =
         let stv_to_itv_list = List.assoc this_ty_name this_ty_assoc_list in
         let (_, tyvars) = List.split stv_to_itv_list in
         let tyVars = List.map (fun tyvar -> TyVar (tyvar, Safe)) tyvars in
         TyRecord (this_ty_name, tyVars) in
       let this_ty_set = MySet.from_list (List.map f this_ty_l) in
       let (field_s, rel) = make_subst_and_rel tyenv alpha this_ty_l this_ty_assoc_list name_beta_l l in
       let this_s =
         if MySet.length this_ty_set = 1 then
           [(alpha, (List.hd (MySet.to_list this_ty_set)))]
         else
           [(alpha, TySet (alpha, this_ty_set))] in
       let field_eqs = eqs_of_subst (squeeze_subst field_s) in
       let this_eqs = eqs_of_subst this_s in
       let eqs = field_eqs @ this_eqs @ make_eqs_about_att_ty (TyVar (alpha, Safe)) att_ty in
       let s = squeeze_subst (unify eqs) in
       (s, subst_type s (TyVar (alpha, Safe)), rel)
  | (RecordWith (exp, l), att_ty) ->
     let (s1, ty, rel1) = ty_exp tyenv exp in
     let (candidates, name_l) = get_candidates true MySet.empty [] l in
     let alpha = fresh_tyvar () in
     let name_beta_l = make_name_beta_l name_l in
     let this_ty_assoc_list = make_this_ty_assoc_list candidates in
     let f this_ty_name =
       let stv_to_itv_list = List.assoc this_ty_name this_ty_assoc_list in
       let (_, tyvars) = List.split stv_to_itv_list in
       let tyVars = List.map (fun tyvar -> TyVar (tyvar, Safe)) tyvars in
       TyRecord (this_ty_name, tyVars) in
     let this_ty_set = MySet.from_list (List.map f candidates) in
     let (field_s, rel2) = make_subst_and_rel tyenv alpha candidates this_ty_assoc_list name_beta_l l in
     let this_s =
       if MySet.length this_ty_set = 1 then
         unify [(TyVar (alpha, Safe), (List.hd (MySet.to_list this_ty_set))); (TyVar (alpha, Safe), ty)]
       else
         unify [(TyVar (alpha, Safe), TySet (alpha, this_ty_set)); (TyVar (alpha, Safe), ty)] in
     let field_eqs = eqs_of_subst (squeeze_subst field_s) in
     let this_eqs = eqs_of_subst (squeeze_subst this_s) in
     let eqs = (eqs_of_subst s1) @ field_eqs @ this_eqs @ make_eqs_about_att_ty (TyVar (alpha, Safe)) att_ty in
     let s2 = squeeze_subst (unify eqs) in
     (s2, subst_type s2 (TyVar (alpha, Safe)), rel1 @ rel2)
  | (BinOp (op, exp1, exp2), att_ty) ->
     let (s1, ty1, rel1) = ty_exp tyenv exp1 in
     let (s2, ty2, rel2) = ty_exp tyenv exp2 in
     let (eqs3, ty) =  ty_prim op ty1 ty2 in
     let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ eqs3 @ (make_eqs_about_att_ty ty att_ty) in
     let s3 = squeeze_subst (unify eqs) in
     (s3, subst_type s3 ty, rel1 @ rel2)
  | (BinLogicOp (op, exp1, exp2), att_ty) ->
     let (s1, ty1, rel1) = ty_exp tyenv exp1 in
     let (s2, ty2, rel2) = ty_exp tyenv exp2 in
     let (eqs3, ty) =  ty_logic_prim op ty1 ty2 in
     let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ eqs3 @ (make_eqs_about_att_ty ty att_ty) in
     let s3 = squeeze_subst (unify eqs) in
     (s3, subst_type s3 ty, rel1 @ rel2)
  | (IfExp (exp1, exp2, exp3), att_ty) ->
     let (s1, ty1, rel1) = ty_exp tyenv exp1 in
     let (s2, ty2, rel2) = ty_exp tyenv exp2 in
     let (s3, ty3, rel3) = ty_exp tyenv exp3 in
     let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ (eqs_of_subst s3) @ [(ty1, TyBool); (ty2, ty3)]
               @ (make_eqs_about_att_ty ty2 att_ty) in
     let s4 = squeeze_subst (unify eqs) in
     (s4, subst_type s4 ty2, rel1 @ rel2 @ rel3)
  | (LetExp (l, exp2), att_ty) ->
     let rec ty_let_list l tyenv' subst id_l =
       match l with
         [] ->
          let (s3, ty2, rel2) = ty_exp tyenv' exp2 in
          let eqs = (eqs_of_subst subst) @ (eqs_of_subst s3) @ (make_eqs_about_att_ty ty2 att_ty) in
          let s4 = squeeze_subst (unify eqs) in
          (s4, subst_type s4 ty2, rel2)
       | ((id, att_ty'), exp1) :: rest ->
          if List.exists (fun x -> x = id) id_l then
            err ("one variable is bound several times in this expression")
          else
            let (s1, ty1, rel1) = ty_exp tyenv exp1 in
            let eqs = (eqs_of_subst s1) @ (make_eqs_about_att_ty ty1 att_ty') in
            let s2 = squeeze_subst (unify eqs) in
            let s3 = finalize_subst s2 in
            let s4 = unify (eqs_of_subst (s3 @ reflect_dependency rel1 s3)) in
            let tysc = closure ty1 tyenv s4 in
            let newtyenv = Environment.extend id tysc tyenv' in
            ty_let_list rest newtyenv (s4 @ subst) (id :: id_l)
     in
     ty_let_list l tyenv [] []
  | (FunExp ((id, att_ty'), exp), att_ty) ->
     let domty = TyVar (fresh_tyvar (), Out) in
     let (s1, ranty, rel) = ty_exp (Environment.extend id (TyScheme ([], domty)) tyenv) exp in
     let ty = TyFun (subst_type s1 domty, ranty) in
     let eqs = (eqs_of_subst s1) @ (make_eqs_about_att_ty (subst_type s1 domty) att_ty') @ (make_eqs_about_att_ty ty att_ty) in
     let s2 = squeeze_subst (unify eqs) in
     (s2, subst_type s2 ty, rel)
  | (AppExp (exp1, exp2), att_ty) ->
     let (s1, ty1, rel1) = ty_exp tyenv exp1 in
     let (s2, ty2, rel2) = ty_exp tyenv exp2 in
     (match ty1 with
        TyFun (domty, ranty) ->
         let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ [(domty, ty2)] @ (make_eqs_about_att_ty ranty att_ty) in
         let s3 = squeeze_subst (unify eqs) in
         (s3, subst_type s3 ranty, rel1 @ rel2)
      | TyVar _  ->
         let domty = TyVar (fresh_tyvar (), Out) in
         let ranty = TyVar (fresh_tyvar (), Safe) in
         let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ [(ty1, TyFun (domty, ranty)); (domty, ty2)]
                   @ (make_eqs_about_att_ty ranty att_ty) in
         let s3 = squeeze_subst (unify eqs) in
         (s3, subst_type s3 ranty, rel1 @ rel2)
      | _ -> err ("Non-function value is applied"))
  | (LetRecExp (l, exp2), att_ty) ->
     let rec main_loop l tyenv' exp_dom_ran_l id_l =
       match l with
         [] ->
          (* 本当に束縛すべき値を評価する *)
          let rec make_eqs_list = function
              [] -> []
            | ((FunExp ((para, att_ty1), exp), att_ty2), domty, ranty) :: rest ->
               let (s, t, rel) = ty_exp (Environment.extend para (TyScheme ([], domty)) tyenv') exp in
               ((eqs_of_subst s) :: [(t, ranty)] :: (make_eqs_about_att_ty (TyFun (domty, ranty)) att_ty2)
               :: [make_eqs_about_att_ty (subst_type s domty) att_ty1], rel) :: make_eqs_list rest
            | _ -> err ("For debug : this error cannot occur")
          in
          let (eqs_list, rel1) = (fun (x, y) -> (List.concat (List.concat x), List.concat y)) (List.split (make_eqs_list exp_dom_ran_l)) in
          (* 本当に束縛すべき値を変数に束縛する *)
          let rec make_newtyenv id_l =
            match id_l with
              [] -> tyenv
            | (id, att_ty) :: rest ->
               let TyScheme (_, ty) = Environment.lookup id tyenv' in
               let s1 = squeeze_subst (unify eqs_list) in
               let eqs = (eqs_of_subst s1) @ (make_eqs_about_att_ty (subst_type s1 ty) att_ty) in
               let s2 = squeeze_subst (unify eqs) in
               let tysc = closure (subst_type s2 ty) tyenv s2 in
               Environment.extend id tysc (make_newtyenv rest)
          in
          let newtyenv = make_newtyenv id_l in
          let (s2, ty2, rel2) = ty_exp newtyenv exp2 in
          let eqs = eqs_list @ (eqs_of_subst s2) @ (make_eqs_about_att_ty ty2 att_ty) in
          let s3 = squeeze_subst (unify eqs) in
          (s3, subst_type s3 ty2, rel1 @ rel2)
       (* まず変数が適当な関数に束縛されているようにする *)
       | (typed_id, exp) :: rest ->
          let (id, _) = typed_id in
          if List.mem_assoc id id_l then
            err ("one variable is bound several times in this expression")
          else
            let domty = TyVar (fresh_tyvar (), Out) in
            let ranty = TyVar (fresh_tyvar (), Safe) in
            let newtyenv = Environment.extend id (TyScheme ([], (TyFun (domty, ranty)))) tyenv' in
            main_loop rest newtyenv ((exp, domty, ranty) :: exp_dom_ran_l) (typed_id :: id_l)
     in
     main_loop l tyenv [] []
  | (ListExp l, att_ty) ->
     (match l with
        Emp ->
         let ty = TyList (TyVar (fresh_tyvar (), Safe)) in
         let eqs = make_eqs_about_att_ty ty att_ty in
         let s = squeeze_subst (unify eqs) in
         (s, subst_type s ty, [])
      | Cons (exp, l) ->
         let (s1, ty1, rel1) = ty_exp tyenv exp in
         let (s2, ty2', rel2) = ty_exp tyenv ((ListExp l), []) in
         match ty2' with
           TyList ty2 ->
            let eqs1 = (eqs_of_subst s1) @ (eqs_of_subst s2) @ [(ty2, ty1)] in
            let s3 = squeeze_subst (unify eqs1) in
            let ty3 = TyList (subst_type s3 ty1) in
            let eqs2 = (eqs_of_subst s3) @ (make_eqs_about_att_ty ty3 att_ty) in
            let s4 = squeeze_subst (unify eqs2) in
            (s4, subst_type s4 ty3, rel1 @ rel2)
         | _ -> err ("For debug : this error cannot occur"))
  | (MatchExp (exp, pattern_and_body_list), att_ty) ->
     let rec gather_id_from_pattern pattern =
       let rec case_list = function
           Emp -> []
         | Cons (exp, l) -> (gather_id_from_pattern exp) @ case_list l
       and case_tuple = function
           EmpT -> []
         | ConsT (exp, l) -> (gather_id_from_pattern exp) @ case_tuple l
       and case_record = function
           EmpR -> []
         | ConsR ((_, exp), l) -> (gather_id_from_pattern exp) @ case_record l
       in
       match pattern with
       | (Var id, _) -> [id]
       | (ILit _, _) | (BLit _, _) | (SLit _, _) -> []
       | (Constr (_, None), _) -> []
       | (Constr (_, Some exp), _) -> gather_id_from_pattern exp
       | (BinOp (Cons, exp1, exp2), _) -> (gather_id_from_pattern exp1) @ (gather_id_from_pattern exp2)
       | (ListExp l, _) -> case_list l
       | (TupleExp l, _) -> case_tuple l
       | (RecordPattern l, _) -> case_record l
       | (Wildcard, _) -> []
       | _ -> err ("For debug: at gather_id_form_pattern")
     and check_whether_duplication checked_l id_l =
       match checked_l with
         [] -> false
       | id :: rest ->
          if List.exists (fun x -> x = id) id_l then true
          else check_whether_duplication rest (id :: id_l)
     and bind_id id_l =
       match id_l with
         [] -> tyenv
       | head :: rest ->
          Environment.extend head (TyScheme ([], (TyVar (fresh_tyvar (), Safe)))) (bind_id rest)
     and eval_ty = function
         [] -> ([], [], [], [], [], [])
       | (pattern, body) :: rest ->
          let id_in_pattern = gather_id_from_pattern pattern in
          if check_whether_duplication id_in_pattern [] then
            err ("one variables is bound several times in this expression")
          else
            let newtyenv = bind_id id_in_pattern in
            let (s_patterns, ty_patterns, rel_patterns, s_bodies, ty_bodies, rel_bodies) = eval_ty rest in
            let (s1, ty1, rel1) = ty_exp newtyenv pattern in
            let (s2, ty2, rel2) = ty_exp newtyenv body in
            (s1 :: s_patterns, ty1 :: ty_patterns, rel1 :: rel_patterns, s2 :: s_bodies, ty2 :: ty_bodies, rel2 :: rel_bodies)
     in
     let (s, ty, rel) = ty_exp tyenv exp in
     let (ss1, tys1, rels1, ss2, tys2, rels2) = eval_ty pattern_and_body_list in
     let s1 = List.concat ss1 in
     let s2 = List.concat ss2 in
     let eqs_list1 = make_ty_eqs_list (ty :: tys1) in
     let eqs_list2 = make_ty_eqs_list tys2 in
     let rel1 = List.concat rels1 in
     let rel2 = List.concat rels2 in
     let eqs = ((eqs_of_subst s) @ (eqs_of_subst s1) @ (eqs_of_subst s2) @ eqs_list1 @ eqs_list2) in
     let s3 = squeeze_subst (unify eqs) in
     let this_ty = subst_type s3 (List.hd tys2) in
     let s4 = squeeze_subst (unify ((eqs_of_subst s3) @ (make_eqs_about_att_ty this_ty att_ty))) in
     (s4, subst_type s4 this_ty, rel @ rel1 @ rel2)
  | (TupleExp l, att_ty) ->
     let rec ty_tupleExp l subst relation =
       match l with
         EmpT -> (subst, TyEmpT, relation)
       | ConsT (exp, l') ->
          let (s, ty, rel) = ty_exp tyenv exp in
          let (subst', tytuple, relation') = ty_tupleExp l' subst rel in
          ((s @ subst'), TyConsT (ty, tytuple), (rel @ relation'))
     in
     let (s1, tytuple, rel) = ty_tupleExp l [] [] in
     let eqs1 = eqs_of_subst s1 in
     let s2 = squeeze_subst (unify eqs1) in
     let ty = subst_type s2 (TyTuple tytuple) in
     let eqs2 = (eqs_of_subst s2) @ (make_eqs_about_att_ty ty att_ty) in
     let s3 = squeeze_subst (unify eqs2) in
     (s3, subst_type s3 ty, rel)
  | (RecordPattern l, att_ty) ->
     let (candidates, name_l) = get_candidates true MySet.empty [] l in
     let alpha = fresh_tyvar () in
     let name_beta_l = make_name_beta_l name_l in
      let this_ty_assoc_list = make_this_ty_assoc_list candidates in
      let f this_ty_name =
        let stv_to_itv_list = List.assoc this_ty_name this_ty_assoc_list in
        let (_, tyvars) = List.split stv_to_itv_list in
        let tyVars = List.map (fun tyvar -> TyVar (tyvar, Safe)) tyvars in
        TyRecord (this_ty_name, tyVars) in
     let this_ty_set = MySet.from_list (List.map f candidates) in
     let (field_s, rel) = make_subst_and_rel tyenv alpha candidates this_ty_assoc_list name_beta_l l in
     let this_s =
       if MySet.length this_ty_set = 1 then
         [(alpha, (List.hd (MySet.to_list this_ty_set)))]
       else
         [(alpha, TySet (alpha, this_ty_set))] in
     let field_eqs = eqs_of_subst (squeeze_subst field_s) in
     let this_eqs = eqs_of_subst this_s in
     let eqs = field_eqs @ this_eqs @ make_eqs_about_att_ty (TyVar (alpha, Safe)) att_ty in
     let s = squeeze_subst (unify eqs) in
     (s, subst_type s (TyVar (alpha, Safe)), rel)
  | (AssignExp (exp1, name, exp2), att_ty) ->
     let rec extract x = function
         [] -> err ("For debug: at extract")
       | head :: rest ->
          (match head with
             Field (x', arg_ty, mutability) when x = x' -> (arg_ty, mutability)
           | _ -> extract x rest)
     in
     (try
        let (s1, ty1, rel1) = ty_exp tyenv exp1 in
        let candidates = List.map (fun (_, y) -> y) (Rev_environment.lookup name !rev_defenv) in
        let alpha = fresh_tyvar () in
        let ty_assoc_list = make_this_ty_assoc_list candidates in
        let f this_ty_name =
          let stv_to_itv_list = List.assoc this_ty_name ty_assoc_list in
          let (_, tyvars) = List.split stv_to_itv_list in
          let tyVars = List.map (fun tyvar -> TyVar (tyvar, Safe)) tyvars in
          TyRecord (this_ty_name, tyVars) in
        let ty_set = MySet.from_list (List.map f candidates) in
        let s2 =
          if MySet.length ty_set = 1 then
            unify [(TyVar (alpha, Safe), (List.hd (MySet.to_list ty_set))); (TyVar (alpha, Safe), ty1)]
          else
            unify [(TyVar (alpha, Safe), TySet (alpha, ty_set)); (TyVar (alpha, Safe), ty1)] in
        let eqs1 = (eqs_of_subst s1) @ (eqs_of_subst (squeeze_subst s2)) in
        let s3 = squeeze_subst (unify eqs1) in
        let s4 = finalize_subst s3 in
        let s5 = unify (eqs_of_subst (s4 @ reflect_dependency rel1 s4)) in
        let ty2 = subst_type s5 (TyVar (alpha, Safe)) in
        (match ty2 with
           TyRecord (ty_name, l) ->
            let (param, body_l) = Environment.lookup ty_name !recdefenv in
            let (arg_ty, mutability) = extract name body_l in
            (match mutability with
               Mutable ->
                let assoc_list = List.combine param l in
                let replaced_arg_ty = replace_another assoc_list arg_ty in
                let (s6, ty3, rel2) = ty_exp tyenv exp2 in
                let eqs2 = (eqs_of_subst s5) @ (eqs_of_subst s6) @ [(replaced_arg_ty, ty3)] @ (make_eqs_about_att_ty TyUnit att_ty) in
                let s7 = squeeze_subst (unify eqs2) in
                (s7, TyUnit, rel2)
             | Immutable -> err ("The record field " ^ name ^ " is not mutable"))
         | _ -> err ("For debug: at AssignExp"))
      with
        Rev_environment.Not_bound -> err ("record field not bound: " ^ name))
  | (Unit, att_ty) ->
     let eqs = make_eqs_about_att_ty TyUnit att_ty in
     let s = squeeze_subst (unify eqs) in
     (s, TyUnit, [])
  | (Wildcard, att_ty) ->
     let ty = TyVar (fresh_tyvar (), Safe) in
     let eqs = make_eqs_about_att_ty ty att_ty in
     let s = squeeze_subst (unify eqs) in
     (s, subst_type s ty, [])
  | _ -> err ("not implemented yet")


let ty_decl tyenv defenv' vardefenv' recdefenv' rev_defenv' decl =
  defenv := defenv'; vardefenv := vardefenv'; recdefenv := recdefenv'; rev_defenv := rev_defenv';
  match decl with
    Exp e ->
     let stringtyvar_to_inttyvar_list = make_Tyvar_to_TyVar_list e in
     let transformed_e = transform e stringtyvar_to_inttyvar_list in
     let (s1, ty, rel) = ty_exp tyenv transformed_e in
     let s2 = finalize_subst s1 in
     let s3 = unify (eqs_of_subst (s2 @ reflect_dependency rel s2)) in
     [(tyenv, subst_type s3 ty)]
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
                  let (s1, ty, rel) = ty_exp !tyenv e in
                  let eqs = (eqs_of_subst s1) @ (make_eqs_about_att_ty ty att_ty) in
                  let s2 = squeeze_subst (unify eqs) in
                  let s3 = finalize_subst s2 in
                  let s4 = finalize_subst (squeeze_subst (unify (eqs_of_subst ((reflect_dependency rel s3) @ s2)))) in
                  let tysc = closure (subst_type s4 ty) !tyenv s4 in
                  let newtyenv = Environment.extend id tysc tyenv' in
                  (newtyenv, subst_type s4 (subst_type s4 ty)) :: make_anddecl_ty_list inner_rest newtyenv (id :: id_l))
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
                      let (s, t, rel) = ty_exp (Environment.extend para (TyScheme ([], domty)) and_tyenv) body in
                      ((eqs_of_subst s) :: [(t, ranty)] :: (make_eqs_about_att_ty (TyFun (domty, ranty)) att_ty2)
                      :: [make_eqs_about_att_ty (subst_type s domty) att_ty1], rel) :: make_eqs rest
                   | _ -> err ("For debug : this error cannot occur")
                 (* 本当に束縛すべき値を変数に束縛する *)
                 and make_final_list s rel id_l tyenv' =
                   match id_l with
                     [] -> tyenv := tyenv'; [] (* andでつながれているものはすべて環境に追加したところで環境を更新 *)
                   | (id, att_ty) :: id_rest ->
                      let TyScheme (_, ty1) = Environment.lookup id and_tyenv in
                      let ty2 = subst_type s ty1 in
                      let eqs = (eqs_of_subst s) @ (make_eqs_about_att_ty ty2 att_ty) in
                      let s1 = squeeze_subst (unify eqs) in
                      let s2 = finalize_subst s1 in
                      let s3 = finalize_subst (squeeze_subst (unify (eqs_of_subst ((reflect_dependency rel s2) @ s1)))) in
                      let ty3 = subst_type s3 ty2 in
                      let tysc = closure ty3 !tyenv s3 in (* ここの環境は外の環境 *)
                      let newtyenv = Environment.extend id tysc tyenv' in
                      (newtyenv, ty3) :: make_final_list s3 rel id_rest newtyenv
                 in
                 let (eqs, rel) = (fun (x, y) -> (List.concat (List.concat x), List.concat y)) (List.split (make_eqs exp_dom_ran_l)) in
                 let s = squeeze_subst (unify eqs) in
                 make_final_list s rel id_l and_tyenv
              | (typed_id, exp) :: inner_rest ->
                 (* まず変数が適当な関数に束縛されているようにする *)
                 let (id, _) = typed_id in
                 if List.mem_assoc id id_l then
                   err ("one variable is bound several times in this declaration")
                 else
                   let domty = TyVar (fresh_tyvar (), Out) in
                   let ranty = TyVar (fresh_tyvar (), Safe) in
                   let newtyenv = Environment.extend id (TyScheme ([], (TyFun (domty, ranty)))) and_tyenv in
                   make_andrecdecl_ty_list inner_rest newtyenv ((exp, domty, ranty) :: exp_dom_ran_l) (typed_id :: id_l))
           in
           let stringtyvar_to_inttyvar_list = make_Tyvar_to_TyVar_list_for_decl head in
           let transformed_head = transform_decl head stringtyvar_to_inttyvar_list in
           let and_list = make_andrecdecl_ty_list transformed_head !tyenv [] [] in
           and_list @ make_recdecl_ty_list outer_rest tyenv)
     in
     make_recdecl_ty_list l (ref tyenv)
  | _ -> err ("For debug: this error cannot occur")
