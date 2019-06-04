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


let rec get_ConstrName_and_TyUser_list = function
    [] -> ([], MySet.empty)
  | head :: rest ->
     let (cname_l, tyuser_s) = get_ConstrName_and_TyUser_list rest in
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


let rec bind_rev_defenv id l rev_defenv =
  match l with
    [] -> rev_defenv
  | Constructor (name, ty) :: rest ->
     let newrev_defenv = Rev_environment.extend name (ty, id) rev_defenv in
     bind_rev_defenv id rest newrev_defenv
  | Field (name, ty) :: rest ->
     let newrev_defenv = Rev_environment.extend name (ty, id) rev_defenv in
     bind_rev_defenv id rest newrev_defenv


let rec def_decl defenv rev_defenv = function
    TypeDecls l ->
      let rec make_newenv l defenv rev_defenv =
        (match l with
           [] -> (!defenv, !rev_defenv)
         | head :: outer_rest ->
            let rec make_and_newenv l tyuser_set defenv' rev_defenv' =
              (match l with
                 [] ->
                  let x = check_bound (MySet.to_list tyuser_set) defenv' in
                  if x = "OK"
                  then
                    (defenv := defenv'; rev_defenv := rev_defenv')
                  else
                    err ("Type not defined: " ^ x)
               | (id, body_l) :: inner_rest ->
                  let (cname_l, tyuser_s) = get_ConstrName_and_TyUser_list body_l in
                  if check_whether_duplication cname_l
                  then
                    err ("one type cannot have elements which have same name")
                  else
                    let newdefenv = Environment.extend id body_l defenv' in
                    let newrev_defenv = bind_rev_defenv id body_l rev_defenv' in
                    make_and_newenv inner_rest (MySet.union tyuser_s tyuser_set) newdefenv newrev_defenv)
            in
            make_and_newenv head MySet.empty !defenv !rev_defenv;
            make_newenv outer_rest defenv rev_defenv)
      in
      make_newenv l (ref defenv) (ref rev_defenv)
  | _ -> err ("For debug: this error cannot occur")
