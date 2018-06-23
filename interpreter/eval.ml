open Syntax 

(* 値の定義 *)

(* exval は式を評価して得られる値．dnval は変数と紐付けられる値．今回
   の言語ではこの両者は同じになるが，この2つが異なる言語もある．教科書
   参照． *)
type exval =
  | IntV of int
  | BoolV of bool
  | ProcV of id * exp * dnval Environment.t ref
  | DProcV of id * exp
  | ListV of listval
and listval = EmpV | ConsV of exval * listval
and dnval = exval

exception Error of string
exception InnerMatchError
exception MatchError

let err s = raise (Error s)

let rec string_of_list l =
  let rec inner_loop l =
    match l with
      EmpV -> "]"
    | ConsV (head, tail) ->
       (match head with
          IntV i -> "; " ^ (string_of_int i) ^ (inner_loop tail)
        | BoolV b -> "; " ^ (string_of_bool b) ^ (inner_loop tail)
        | ProcV (_,_,_) -> "; " ^ "<fun>" ^ (inner_loop tail)
        | DProcV (_,_) -> "; " ^ "<dfun>" ^ (inner_loop tail)
        | ListV l -> "; " ^ (string_of_list l) ^ (inner_loop tail))
  in
    let str = inner_loop l in
    let str_length = String.length str in
    if str_length <= 2 then "[]"
                       else "[" ^ String.sub str 2 (str_length - 2)

(* pretty printing *)
let rec string_of_exval = function
    IntV i -> string_of_int i
  | BoolV b -> string_of_bool b
  | ProcV (_, _, _) -> "<fun>"
  | DProcV (_, _) -> "<dfun>"
  | ListV l -> string_of_list l
let pp_val v = print_string (string_of_exval v)

let rec apply_prim op arg1 arg2 = match op, arg1, arg2 with
    Plus, IntV i1, IntV i2 -> IntV (i1 + i2)
  | Plus, _, _ -> err ("Both arguments must be integer: +")
  | Minus, IntV i1, IntV i2 -> IntV (i1 - i2)
  | Minus, _, _ -> err ("Both arguments must be integer: -")
  | Mult, IntV i1, IntV i2 -> IntV (i1 * i2)
  | Mult, _, _ -> err ("Both arguments must be integer: *")
  | Lt, IntV i1, IntV i2 -> BoolV (i1 < i2)
  | Lt, _, _ -> err ("Both arguments must be integer: <")
  | Eq, IntV i1, IntV i2 -> BoolV (i1 = i2)
  | Eq, BoolV b1, BoolV b2 -> BoolV (b1 = b2)
  | Eq, _, _ -> err ("Both arguments must have same type: =")
  | Cons, _, ListV l -> ListV (ConsV (arg1, l))
  | Cons, _, _ -> err ("The right operand must be list: ::")

(*let apply_list_prim op arg1 arg2 = match op, arg2 with
    Cons, ListV l -> ListV (ConsV (arg1, l*)

let rec apply_logic_prim op arg1 exp2 env = match op, arg1 with
    And, BoolV b1 ->
      if b1 then
        let arg2 = eval_exp env exp2 in
       (match arg2 with
          BoolV _ -> arg2
        | _ -> err ("Both arguments must be boolean: &&"))
      else BoolV false
  | And, _ -> err ("Both arguments must be boolean: &&")
  | Or, BoolV b1 ->
      if b1 then BoolV true
      else
        let arg2 = eval_exp env exp2 in
       (match arg2 with
          BoolV _ -> arg2
        | _ -> err ("Both argument must be boolean: ||"))
  | Or, _ -> err ("Both argument must be boolean: ||")

and eval_exp env = function
    Var x -> 
      (try Environment.lookup x env with 
        Environment.Not_bound -> err ("Variable not bound: " ^ x))
  | ILit i -> IntV i
  | BLit b -> BoolV b
  | BinOp (op, exp1, exp2) -> 
      let arg1 = eval_exp env exp1 in
      let arg2 = eval_exp env exp2 in
      apply_prim op arg1 arg2
  | BinLogicOp (op, exp1, exp2) ->
      let arg1 = eval_exp env exp1 in
      apply_logic_prim op arg1 exp2 env
  (*| BinListOp (op, exp1, exp2) ->
      let arg1 = eval_exp env exp1 in
      let arg2 = eval_exp env exp2 in
      apply_list_prim op arg1 arg2*)
  | IfExp (exp1, exp2, exp3) ->
      let test = eval_exp env exp1 in
        (match test with
            BoolV true -> eval_exp env exp2 
          | BoolV false -> eval_exp env exp3
          | _ -> err ("Test expression must be boolean: if"))
  | LetExp (l, exp2) ->
      let rec eval_let_list l env' id_l =
        match l with
          [] -> eval_exp env' exp2
        | (id, exp1) :: rest ->
            if List.exists (fun x -> x = id) id_l then
              err ("one variable is bound several times in this expression")
            else
              let value = eval_exp env exp1 in
              let newenv = Environment.extend id value env' in
                eval_let_list rest newenv (id :: id_l)
      in 
        eval_let_list l env []
  | FunExp (id, exp) -> ProcV (id, exp, ref env)
  | DFunExp (id, exp) -> DProcV (id, exp)       
  | AppExp (exp1, exp2) ->
      let funval = eval_exp env exp1 in
      let arg = eval_exp env exp2 in
       (match funval with
          ProcV (id, body, env') ->
            let newenv = Environment.extend id arg !env' in
              eval_exp newenv body
        | DProcV (id, body) ->
            let newenv = Environment.extend id arg env in
              eval_exp newenv body
        | _ -> err ("Non-function value is applied"))
  | LetRecExp (l, exp2) ->
      let rec eval_letrec_list l env id_l =
        match l with
          [] -> eval_exp !env exp2
        | (id, para, exp1) :: rest ->
            if List.exists (fun x -> x = id) id_l then
              err (| Underscore -> eval_exp env body)
            else
              let value = ProcV (para, exp1, env) in
              let newenv = Environment.extend id value !env in
                env := newenv;
                eval_letrec_list rest env (id :: id_l)
      in
        eval_letrec_list l (ref env) []
  | ListExp lexp ->
      let rec eval_list lexp =
        match lexp with
          Emp -> EmpV
        | Cons (exp, rest) -> 
            let value = eval_exp env exp in
            ConsV (value, eval_list rest)
      in
        ListV (eval_list lexp)
  | MatchExp (exp, pattern_and_body_list) ->
      let value = eval_exp env exp in
     (match value with
        IntV i1 ->
          let rec search_int_pattern_and_eval = function
              [] -> err ("Not matched")
            | (PatternExp pattern, body) :: rest ->
               (match pattern with
                  ILit i2 -> 
                    if i1 = i2 then 
                     (try 
                        eval_exp env body 
                      with MatchError -> search_int_pattern_and_eval rest)
                    else search_int_pattern_and_eval rest
                | Var x ->
                    let newenv = Environment.extend x value env in
                   (try
                      eval_exp newenv body
                    with MatchError -> search_int_pattern_and_eval rest)
                | Underscore -> eval_exp env body
                | _ -> search_int_pattern_and_eval rest)
          in
            search_int_pattern_and_eval pattern_and_body_list
      | BoolV b1 ->
          let rec search_bool_pattern_and_eval = function
              [] -> err ("Not matched")
            | (PatternExp pattern, body) :: rest ->
               (match pattern with
                  BLit b2 -> 
                    if b1 = b2 then
                     (try
                        eval_exp env body 
                      with MatchError -> search_bool_pattern_and_eval rest)
                    else search_bool_pattern_and_eval rest
                | Var x ->
                    let newenv = Environment.extend x value env in
                   (try
                      eval_exp newenv body
                    with MatchError -> search_bool_pattern_and_eval rest)
                | Underscore -> eval_exp env body
                | _ -> search_bool_pattern_and_eval rest)
          in
            search_bool_pattern_and_eval pattern_and_body_list

      | ProcV (_,_,_) 
      | DProcV (_,_)  ->
          let rec search_function_pattern_and_eval = function
              [] -> err ("Not matched")
            | (PatternExp pattern, body) :: rest ->
               (match pattern with
                  Var x ->
                    let newenv = Environment.extend x value env in
                   (try
                      eval_exp newenv body
                    with MatchError -> search_function_pattern_and_eval rest)
                | Underscore -> eval_exp env body
                | _ -> search_function_pattern_and_eval rest)
          in
            search_function_pattern_and_eval pattern_and_body_list
      | ListV l ->
          let rec search_list_pattern_and_eval = function
              [] -> err ("Not matched")
            | (PatternExp pattern, body) :: rest ->
               (match pattern with
                  Var x ->
                    let newenv = Environment.extend x value env in
                   (try
                      eval_exp newenv body
                    with MatchError -> search_list_pattern_and_eval rest)
                | ListExp Emp ->
                   (match l with
                      EmpV -> 
                       (try
                          eval_exp env body
                        with MatchError -> search_list_pattern_and_eval rest)
                    | _ -> search_list_pattern_and_eval rest)
                | ListExp (Cons (Var x, Emp)) ->
                   (match l with
                      ConsV (v, EmpV) -> 
                        let newenv = Environment.extend x v env in
                        try
                          eval_exp newenv body
                        with MatchError -> search_list_pattern_and_eval rest
                    | _ -> search_list_pattern_and_eval rest)
                | ListExp (Cons (Var x1, Cons (Var x2, Emp))) ->
                   if x1 = x2 then err ("one variable is bound several times in this expression")
                   else
                     (match l with
                        ConsV (v1, v2) ->
                          let newenv = Environment.extend x1 v1 env in
                          let newerenv = Environment.extend x2 (ListV v2) newenv in
                          try
                            eval_exp newerenv body
                          with MatchError -> search_list_pattern_and_eval rest
                      | _ -> search_list_pattern_and_eval rest)
                | Underscore -> eval_exp env body
                | _ -> search_list_pattern_and_eval rest)
          in
            search_list_pattern_and_eval pattern_and_body_list)
  | MatchOneExp (exp, one_element_list) ->
      let value = eval_exp env exp in
      match value with
        IntV i1 ->
          let [(PatternExp pattern, body)] = one_element_list in
         (match pattern with
            ILit i2 -> 
              if i1 = i2 then eval_exp env body 
              else raise MatchError
          | Var x ->
              let newenv = Environment.extend x value env in
              eval_exp newenv body
          | Underscore -> eval_exp env body
          | _ -> raise MatchError)
      | BoolV b1 ->
          let [(PatternExp pattern, body)] = one_element_list in
         (match pattern with
            BLit b2 -> 
              if b1 = b2 then eval_exp env body 
              else raise MatchError
          | Var x ->
              let newenv = Environment.extend x value env in
               eval_exp newenv body
          | Underscore -> eval_exp env body
          | _ -> raise MatchError)
      | ProcV (_,_,_) 
      | DProcV (_,_)  ->
          let [(PatternExp pattern, body)] = one_element_list in
         (match pattern with
          | Var x ->
              let newenv = Environment.extend x value env in
               eval_exp newenv body
          | Underscore -> eval_exp env body
          | _ -> raise MatchError)
      | ListV l ->
          let [(PatternExp pattern, body)] = one_element_list in
         (match pattern with
            Var x ->
              let newenv = Environment.extend x value env in
              eval_exp newenv body
          | ListExp Emp ->
             (match l with
                EmpV -> eval_exp env body
              | _ -> raise MatchError)
          | ListExp (Cons (Var x, Emp)) ->
             (match l with
                ConsV (v, EmpV) -> 
                  let newenv = Environment.extend x v env in
                  eval_exp newenv body
              | _ -> raise MatchError)
          | ListExp (Cons (Var x1, Cons (Var x2, Emp))) ->
             (match l with
                ConsV (v1, v2) ->
                  let newenv = Environment.extend x1 v1 env in
                  let newerenv = Environment.extend x2 (ListV v2) newenv in
                  eval_exp newerenv body
              | _ -> raise MatchError)
          | Underscore -> eval_exp env body
          | _ -> raise MatchError)

                           

let eval_decl env = function
    Exp e -> let v = eval_exp env e in [[("-", env, v)]]
  | Decls l ->
      let rec make_decl_list l env =
     (match l with
        [] -> [[]]
      | head :: outer_rest -> 
          let rec make_anddecl_list l env' id_l =
           (match l with
              [] -> env := env';
                    []
            | (id, e) :: inner_rest ->
                if List.exists (fun x -> x = id) id_l then
                  err ("one variable is bound several times in this expression")
                else 
                  let v = eval_exp !env e in
                  let newenv = Environment.extend id v env' in
                    (id, newenv, v) :: make_anddecl_list inner_rest newenv (id :: id_l))
           in
             let and_list = make_anddecl_list head !env [] in
               and_list :: make_decl_list outer_rest env)
      in
        make_decl_list l (ref env)
  | RecDecls l ->
      let rec make_recdecl_list l env =
     (match l with
        [] -> [[]]
      | head :: outer_rest ->
          let rec make_andrecdecl_list l env id_l =
           (match l with
              [] -> []
            | (id, para, body) :: inner_rest ->
                if List.exists (fun x -> x = id) id_l then
                  err ("one variable is bound several times in this expression")
                else
                  let v = ProcV (para, body, env) in
                  let newenv = Environment.extend id v !env in
                    env := newenv;
                    (id, newenv, v) :: make_andrecdecl_list inner_rest env (id :: id_l))
          in
            let and_list = make_andrecdecl_list head env [] in
              and_list :: make_recdecl_list outer_rest env)
      in
        make_recdecl_list l (ref env)
                  

