open Syntax

(* 値の定義 *)

(* exval は式を評価して得られる値．dnval は変数と紐付けられる値．今回
   の言語ではこの両者は同じになるが，この2つが異なる言語もある．教科書
   参照． *)
type exval =
  | IntV of int
  | BoolV of bool
  | StringV of string
  | ConstrV of name * exval option
  | RecordV of recordval
  | ProcV of id * exp * dnval Environment.t ref
  | DProcV of id * exp
  | ListV of listval
  | TupleV of tupleval
and listval = EmpV | ConsV of exval * listval
and tupleval = EmpTV | ConsTV of exval * tupleval
and recordval = EmpRV | ConsRV of (name * exval) * recordval
and dnval = exval


exception Error of string
exception MatchError

let err s = raise (Error s)

let rec assocList_of_recordval = function
    EmpRV -> []
  | ConsRV ((name, exval), rest) -> (name, exval) :: assocList_of_recordval rest

let replace param_ty_assoc_list ty =
  let rec case_tytuple = function
      TyEmpT -> TyEmpT
    | TyConsT (ty', tytup') -> TyConsT (body_func ty', case_tytuple tytup')
  and case_ty_list = function
      [] -> []
    | head :: rest -> body_func head :: case_ty_list rest
  and body_func = function
      TyInt -> TyInt
    | TyBool -> TyBool
    | TyString -> TyString
    | TyVar tyvar -> TyVar tyvar
    | TyStringVar tyvar -> List.assoc tyvar param_ty_assoc_list
    | TyFun (domty, ranty) -> TyFun (body_func domty, body_func ranty)
    | TyList ty' -> TyList (body_func ty')
    | TyTuple tytup -> TyTuple (case_tytuple tytup)
    | TyVariant (x, l) -> TyVariant (x, case_ty_list l)
    | TyRecord (x, l) -> TyRecord (x, case_ty_list l)
    | TyNone name -> TyNone name
    | _ -> err ("For debug: at replace (eval.ml)")
  in
  body_func ty


let rec string_of_list ty defenv l =
  let ty' = match ty with TyList ty' -> ty' | _ -> TyInt (* nonsense *) in
  let rec inner_loop l =
    match l with
      EmpV -> "]"
    | ConsV (head, rest) ->
       "; " ^ (string_of_exval ty' defenv head) ^ (inner_loop rest)
  in
  let str = inner_loop l in
  let str_length = String.length str in
  if str_length <= 2 then "[]"
  else "[" ^ String.sub str 2 (str_length - 2)

and string_of_tuple ty defenv l =
  let tytup = match ty with TyTuple tytup -> tytup | _ -> TyEmpT (* nonsense *) in
  let rec inner_loop l tytup =
    match l, tytup with
      EmpTV, TyEmpT -> ")"
    | ConsTV (head, rest1), TyConsT (ty', rest2) ->
       ", " ^ (string_of_exval ty' defenv head) ^ (inner_loop rest1 rest2)
    | _ -> err ("For debug: at string_of_tuple")
  in
  let str = inner_loop l tytup in
  let str_length = String.length str in
  "(" ^ String.sub str 2 (str_length - 2)

and string_of_constr ty defenv name valueop =
  match valueop with
    None -> name
  | Some v ->
     let (id, tys) = match ty with TyVariant (x, l) -> (x, l) | _ -> ("", []) (* nonsense *) in
     let (param, body_l) = Environment.lookup id defenv in
     let more_body_l = List.map (fun x -> match x with Constructor (n, t) -> (n, t) | Field (n, t, _) -> (n, t) (* nonsense *)) body_l in
     let param_ty_assoc_list = List.combine param tys in
     let ty' = replace param_ty_assoc_list (List.assoc name more_body_l) in
     (match v with
        ConstrV (_, Some _) -> name ^ " (" ^ (string_of_exval ty' defenv v) ^ ")"
      | _ -> name ^ " " ^ (string_of_exval ty' defenv v))

and string_of_record ty defenv l =
  let (id, tys) = match ty with TyRecord (x, l) -> (x, l) | _ -> ("", []) (* nonsense *) in
  let (param, body_l) = Environment.lookup id defenv in
  let param_ty_assoc_list = List.combine param tys in
  let recordval_assoc_list = assocList_of_recordval l in
  let rec inner_loop body_l =
    match body_l with
      [] -> "}"
    | Field (name, ty', _) :: rest ->
       "; " ^ name ^ " = " ^ (string_of_exval (replace param_ty_assoc_list ty') defenv (List.assoc name recordval_assoc_list)) ^ (inner_loop rest)
    | _ -> err ("For debug: at string_of_record")
  in
  let str = inner_loop body_l in
  let str_length = String.length str in
  "{" ^ String.sub str 2 (str_length - 2)

(* pretty printing *)
and string_of_exval ty defenv = function
    IntV i -> string_of_int i
  | BoolV b -> string_of_bool b
  | StringV s -> "\"" ^ s ^ "\""
  | ConstrV (name, valueop) -> string_of_constr ty defenv name valueop
  | RecordV l -> string_of_record ty defenv l
  | ProcV (_, _, _) -> "<fun>"
  | DProcV (_, _) -> "<dfun>"
  | ListV l -> string_of_list ty defenv l
  | TupleV l -> string_of_tuple ty defenv l

let pp_val v ty defenv = print_string (string_of_exval ty defenv v)



let rec pattern_match pattern value =
  let rec case_record pt value_list =
    match pt with
      EmpR -> []
    | ConsR ((name, (pt, _)), rest) ->
       (try
          let va = List.assoc name value_list in
          pattern_match pt va @ case_record rest value_list
        with
          Not_found -> err ("For debug: at case_record in pattern_match"))
  in
  match pattern, value with
    ILit i1, IntV i2 when (i1 = i2) -> []
  | BLit b1, BoolV b2 when (b1 = b2) -> []
  | SLit s1, StringV s2 when (s1 = s2) -> []
  | Var x, _ -> [(x, value)]
  | Constr (name1, None), ConstrV (name2, None) when (name1 = name2) -> []
  | Constr (name1, Some (pt, _)), ConstrV (name2, Some v) when (name1 = name2) ->
     pattern_match pt v
  | RecordPattern pt, RecordV l -> case_record pt (assocList_of_recordval l)
  | BinOp (Cons, (pt1, _), (pt2, _)), ListV (ConsV (v, l)) ->
     (pattern_match pt1 v) @ (pattern_match pt2 (ListV l))
  | ListExp Emp, ListV EmpV -> []
  | ListExp (Cons ((pt, _), l1)), ListV (ConsV (v, l2)) ->
     (pattern_match pt v) @ (pattern_match (ListExp l1) (ListV l2))
  | TupleExp EmpT, TupleV EmpTV -> []
  | TupleExp (ConsT ((pt, _), l1)), TupleV (ConsTV (v, l2)) ->
     (pattern_match pt v) @ (pattern_match (TupleExp l1) (TupleV l2))
  | Wildcard, _ -> []
  | _, _ -> raise MatchError


let rec apply_prim op arg1 arg2 =
  match op, arg1, arg2 with
    Plus, IntV i1, IntV i2 -> IntV (i1 + i2)
  | Minus, IntV i1, IntV i2 -> IntV (i1 - i2)
  | Mult, IntV i1, IntV i2 -> IntV (i1 * i2)
  | Lt, IntV i1, IntV i2 -> BoolV (i1 < i2)
  | Mt, IntV i1, IntV i2 -> BoolV (i1 > i2)
  | Eq, IntV i1, IntV i2 -> BoolV (i1 = i2)
  | Eq, BoolV b1, BoolV b2 -> BoolV (b1 = b2)
  | Eq, StringV s1, StringV s2 -> BoolV (s1 = s2)
  | Eq, _, _ -> err ("= accepts int bool string only")
  | Cons, _, ListV l -> ListV (ConsV (arg1, l))
  | Hat, StringV s1, StringV s2 -> StringV (s1 ^ s2)
  | Expo, IntV i1, IntV i2 ->
     if i2 < 0 then err ("right argument must be non-negative : **")
     else IntV (int_of_float ((float_of_int i1) ** (float_of_int i2)))
  | _ -> err ("For debug : this error cannot occur")


let rec apply_logic_prim op arg1 exp2 env = match op, arg1 with
    And, BoolV b1 ->
     if b1 then
       let arg2 = eval_exp env exp2 in
       (match arg2 with
          BoolV _ -> arg2
        | _ -> err "For debug : this error cannot occur")
     else BoolV false
  | Or, BoolV b1 ->
     if b1 then BoolV true
     else
       let arg2 = eval_exp env exp2 in
       (match arg2 with
          BoolV _ -> arg2
        | _ -> err "For debug : this error cannot occur")
  | _ -> err ("For debug : this error cannot occur")

and eval_exp env = function
    Var x ->
     (try Environment.lookup x env with
        Environment.Not_bound -> err ("Variable not bound: " ^ x))
  | ILit i -> IntV i
  | BLit b -> BoolV b
  | SLit s -> StringV s
  | Constr (name, expop) ->
     (match expop with
        None -> ConstrV (name, None)
      | Some (exp, _) ->
         let arg = eval_exp env exp in
         ConstrV (name, Some arg))
  | Record rexp ->
      let rec eval_record rexp =
       match rexp with
         EmpR -> EmpRV
       | ConsR ((name, (exp, _)), rest) ->
          let value = eval_exp env exp in
          ConsRV ((name, value), eval_record rest)
     in
     RecordV (eval_record rexp)
  | RecordWith ((exp, _), rexp) ->
     let rec assocList_of_recordval = function
         EmpRV -> []
       | ConsRV ((name, value), rest) -> (name, value) :: assocList_of_recordval rest
     and replace old_recordval new_recordval_assoc_list =
       match old_recordval with
         EmpRV -> EmpRV
       | ConsRV ((name, value), rest) ->
          (try
             let new_value = List.assoc name new_recordval_assoc_list in
             ConsRV ((name, new_value), replace rest new_recordval_assoc_list)
           with
             Not_found -> ConsRV ((name, value), replace rest new_recordval_assoc_list))
     in
     let old_value = eval_exp env exp in
     let new_value = eval_exp env (Record rexp) in
     (match old_value, new_value with
        RecordV old_recordval, RecordV new_recordval ->
         let l = replace old_recordval (assocList_of_recordval new_recordval) in
         RecordV l
      | _ -> err ("For debug: at case RecordWith in eval_exp"))
  | BinOp (op, (exp1, _), (exp2, _)) ->
     let arg1 = eval_exp env exp1 in
     let arg2 = eval_exp env exp2 in
     apply_prim op arg1 arg2
  | BinLogicOp (op, (exp1, _), (exp2, _)) ->
     let arg1 = eval_exp env exp1 in
     apply_logic_prim op arg1 exp2 env
  | IfExp ((exp1, _), (exp2, _), (exp3, _)) ->
     let test = eval_exp env exp1 in
     (match test with
        BoolV true -> eval_exp env exp2
      | BoolV false -> eval_exp env exp3
      | _ -> err ("For debug : this error cannot occur"))
  | LetExp (l, (exp2, _)) ->
     let rec eval_let_list l env' =
       match l with
         [] -> eval_exp env' exp2
       | ((id, _), (exp1, _)) :: rest ->
          let value = eval_exp env exp1 in
          let newenv = Environment.extend id value env' in
          eval_let_list rest newenv
     in
     eval_let_list l env
  | FunExp ((id, _), (exp, _)) -> ProcV (id, exp, ref env)
  | DFunExp ((id, _), (exp, _)) -> DProcV (id, exp)
  | AppExp ((exp1, _), (exp2, _)) ->
     let funval = eval_exp env exp1 in
     let arg = eval_exp env exp2 in
     (match funval with
        ProcV (id, body, env') ->
         let newenv = Environment.extend id arg !env' in
         eval_exp newenv body
      | DProcV (id, body) ->
         let newenv = Environment.extend id arg env in
         eval_exp newenv body
      | _ -> err ("For debug : this error cannot occur"))
  | LetRecExp (l, (exp2, _)) ->
     let rec eval_letrec_list l env =
       match l with
         [] -> eval_exp !env exp2
       | ((id, _), ((FunExp ((para, _), (exp1, _))), _)) :: rest ->
          let value = ProcV (para, exp1, env) in
          let newenv = Environment.extend id value !env in
          env := newenv;
          eval_letrec_list rest env
       | _ -> err ("For debug : this error cannot occur")
     in
     eval_letrec_list l (ref env)
  | ListExp lexp ->
     let rec eval_list lexp =
       match lexp with
         Emp -> EmpV
       | Cons ((exp, _), rest) ->
          let value = eval_exp env exp in
          ConsV (value, eval_list rest)
     in
     ListV (eval_list lexp)
  | MatchExp ((exp, _), pattern_and_body_list) ->
     (* マッチする対象を評価 *)
     let value = eval_exp env exp in
     (* (パターン列) -> (本体式) を順に取り出して処理 *)
     let rec main_loop = function
         [] -> err ("Not matched")
       | ((pattern, _), (body, _)) :: rest ->
          try
            let id_and_value_list = pattern_match pattern value in
            let newenv = bind_and_return_env env id_and_value_list in
            eval_exp newenv body
          with
            MatchError -> main_loop rest
     (* パターンマッチの結果束縛する必要がある変数を束縛した環境を返す *)
     and bind_and_return_env env = function
         [] -> env
       | (id, value) :: rest ->
          let newenv = Environment.extend id value env in
          bind_and_return_env newenv rest
     in
     main_loop pattern_and_body_list
  | TupleExp texp ->
     let rec eval_tuple texp =
       match texp with
         EmpT -> EmpTV
       | ConsT ((exp, _), rest) ->
          let value = eval_exp env exp in
          ConsTV (value, eval_tuple rest)
     in
     TupleV (eval_tuple texp)
  | _ -> err ("not implemented yet")


let eval_decl env = function
    Exp (e, _) -> let v = eval_exp env e in [("-", env, v)]
  | Decls l ->
     let rec make_decl_list l env =
       (match l with
          [] -> []
        | head :: outer_rest ->
           let rec make_anddecl_list l env' =
             (match l with
                [] -> env := env';
                      []
              | ((id, _), (e, _)) :: inner_rest ->
                 let v = eval_exp !env e in
                 let newenv = Environment.extend id v env' in
                 (id, newenv, v) :: make_anddecl_list inner_rest newenv)
           in
           let and_list = make_anddecl_list head !env in
           and_list @ make_decl_list outer_rest env)
     in
     make_decl_list l (ref env)
  | RecDecls l ->
     let rec make_recdecl_list l env =
       (match l with
          [] -> []
        | head :: outer_rest ->
           let rec make_andrecdecl_list l env =
             (match l with
                [] -> []
              | ((id,_), ((FunExp ((para, _), (body, _))), _)) :: inner_rest ->
                 let v = ProcV (para, body, env) in
                 let newenv = Environment.extend id v !env in
                 env := newenv;
                 (id, newenv, v) :: make_andrecdecl_list inner_rest env
              | _ -> err ("For debug : this error cannot occur"))
           in
           let and_list = make_andrecdecl_list head env in
           and_list @ make_recdecl_list outer_rest env)
     in
     make_recdecl_list l (ref env)
  | _ -> err ("For debug: this error cannot occur")


