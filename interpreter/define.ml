open Syntax

exception Error of string

let err s = raise (Error s)

let rec get_TyUser_list ty =
  let rec case_tytuple tytup =
    match tytup with
      TyEmpT -> MySet.empty
    | TyConsT (ty, tytup') -> MySet.union (get_TyUser_list ty) (case_tytuple tytup')
  in
  match ty with
    TyInt
  | TyBool
  | TyString
  | TyStringVar _ -> MySet.empty
  | TyFun (domty, ranty) -> MySet.union (get_TyUser_list domty) (get_TyUser_list ranty)
  | TyList ty -> get_TyUser_list ty
  | TyTuple tytup -> case_tytuple tytup
  | TyUser x -> MySet.singleton x
  | TyNone _  -> MySet.empty
  | _ -> err ("For debug: at get_TyUser_list")


let rec get_name_and_TyUser_list = function
    [] -> ([], MySet.empty)
  | head :: rest ->
     let (cname_l, tyuser_s) = get_name_and_TyUser_list rest in
     (match head with
        Constructor (id,ty) -> (id :: cname_l, MySet.union (get_TyUser_list ty) tyuser_s)
      | Field (id, ty) -> (id :: cname_l, MySet.union (get_TyUser_list ty) tyuser_s))


 let rec check_whether_duplication l =
   match l with
     [] -> false
   | head :: rest ->
      if List.mem head rest then true else check_whether_duplication rest


let rec check_bound tyuser_l defenv =
  match tyuser_l with
    [] -> "OK"
  | head :: rest ->
     if Environment.member head defenv then check_bound rest defenv
     else head

let rec replace ty defenv =
  let rec case_tytuple = function
      TyEmpT -> TyEmpT
    | TyConsT (ty', tytup') -> TyConsT (replace ty' defenv, case_tytuple tytup')
  in
  match ty with
    TyUser id ->
     (try
        (match List.hd (Environment.lookup id defenv) with
           Constructor _ -> TyVariant id
         | Field _ -> TyUser id)
      with
        Environment.Not_bound -> err ("type not defined: " ^ id))
  | TyFun (domty, ranty) -> TyFun (replace domty defenv, replace ranty defenv)
  | TyList ty' -> TyList (replace ty' defenv)
  | TyTuple tytup -> TyTuple (case_tytuple tytup)
  | _ -> ty

let rec bind_defenv l defenv  =
  match l with
    [] -> defenv
  | (id, body_l) :: rest ->
     let newdefenv = Environment.extend id body_l defenv in
     bind_defenv rest newdefenv


let rec bind_rev_defenv l rev_defenv =
  let rec inner_loop id body_l rev_defenv' =
    match body_l with
      [] -> rev_defenv'
    | Constructor (name, ty) :: rest ->
       let newrev_defenv' = Rev_environment.extend name (ty, id) rev_defenv' in
       inner_loop id rest newrev_defenv'
    | Field (name, ty) :: rest ->
       let newrev_defenv' = Rev_environment.extend name (ty, id) rev_defenv' in
       inner_loop id rest newrev_defenv'
  in
  match l with
    [] -> rev_defenv
  | (id, body_l) :: rest ->
     let newrev_defenv = inner_loop id body_l rev_defenv in
     bind_rev_defenv rest newrev_defenv

let rec def_decl defenv rev_defenv = function
    TypeDecls l ->
      let rec make_newenv l defenv rev_defenv =
        (match l with
           [] -> (!defenv, !rev_defenv)
         | head :: outer_rest ->
            let rec make_and_newenv all_l l id_l defenv' =
              (match l with
                 [] ->
                  let replaced_l =
                    List.map
                      (fun (id, body_l) ->
                        (id, (List.map
                                (fun z -> match z with
                                            Constructor (name, ty) -> Constructor (name, replace ty defenv')
                                          | Field (name, ty) -> Field (name, replace ty defenv'))
                                body_l))) all_l in
                  let newdefenv = bind_defenv replaced_l !defenv in
                  let newrev_defenv = bind_rev_defenv replaced_l !rev_defenv in
                  defenv := newdefenv;
                  rev_defenv := newrev_defenv;
               | (id, body_l) :: inner_rest ->
                  let (cname_l, tyuser_s) = get_name_and_TyUser_list body_l in
                  if check_whether_duplication cname_l
                  then
                    err ("one type cannot have elements which have same name")
                  else if check_whether_duplication (id :: id_l)
                  then
                    err ("multiple definition of type " ^ id)
                  else
                    let newdefenv = Environment.extend id body_l defenv' in
                    make_and_newenv all_l inner_rest (id :: id_l) newdefenv)
            in
            make_and_newenv head head [] !defenv;
            make_newenv outer_rest defenv rev_defenv)
      in
      make_newenv l (ref defenv) (ref rev_defenv)
  | _ -> err ("For debug: this error cannot occur")
