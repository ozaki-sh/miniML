open Syntax

exception Error of string

let err s = raise (Error s)

let fresh_index =
  let counter = ref 0 in
  let body () =
    let v = !counter in
    counter := v + 1; v
  in body

let rec get_tyvar_list ty =
  let rec case_tytuple = function
      TyEmpT -> []
    | TyConsT (ty, tytup') -> get_tyvar_list ty @ case_tytuple tytup'
  and case_ty_list = function
      [] -> []
    | head :: rest -> get_tyvar_list head @ case_ty_list rest
  in
  match ty with
    TyInt
  | TyBool
  | TyString -> []
  | TyStringVar tyvar -> [tyvar]
  | TyFun (domty, ranty) -> get_tyvar_list domty @ get_tyvar_list ranty
  | TyList ty -> get_tyvar_list ty
  | TyTuple tytup -> case_tytuple tytup
  | TyUser (_, l) -> case_ty_list l
  | TyNone x -> []
  | _ -> err ("For debug: at get_tyvar_list")


let rec get_name_and_tyvar_list = function
    [] -> ([], [])
  | head :: rest ->
     let (name_l, tyvars) = get_name_and_tyvar_list rest in
     (match head with
        Constructor (name, ty) -> (name :: name_l, get_tyvar_list ty @ tyvars)
      | Field (name, ty, _) -> (name :: name_l, get_tyvar_list ty @ tyvars))


 let rec check_whether_duplication l =
   match l with
     [] -> false
   | head :: rest ->
      if List.mem head rest then true else check_whether_duplication rest

let rec check_tyvars_are_bound param tyvars =
  match tyvars with
    [] -> (true, "" (* nonsense *))
  | head :: rest ->
     if List.mem head param then check_tyvars_are_bound param rest else (false, head)


let rec replace ty defenv =
  let rec case_tytuple = function
      TyEmpT -> TyEmpT
    | TyConsT (ty', tytup') -> TyConsT (replace ty' defenv, case_tytuple tytup')
  in
  match ty with
    TyUser (id, l) ->
     (try
        let (_, body_l) = Environment.dlookup id defenv in
        (match List.hd body_l with
           Constructor _ -> TyVariant ((Environment.ilookup id defenv), l)
         | Field _ -> TyRecord ((Environment.ilookup id defenv), l))
      with
        Environment.Not_bound -> err ("type not defined: " ^ id))
  | TyFun (domty, ranty) -> TyFun (replace domty defenv, replace ranty defenv)
  | TyList ty' -> TyList (replace ty' defenv)
  | TyTuple tytup -> TyTuple (case_tytuple tytup)
  | _ -> ty

let rec bind_defenv l defenv  =
  match l with
    [] -> defenv
  | (id, param, body_l) :: rest ->
     let newdefenv = Environment.extend id (param, body_l) defenv in
     bind_defenv rest newdefenv


let rec bind_rev_defenv l rev_defenv =
  let rec inner_loop id body_l rev_defenv' =
    match body_l with
      [] -> rev_defenv'
    | Constructor (name, ty) :: rest ->
       let newrev_defenv' = Rev_environment.extend name (ty, id) rev_defenv' in
       inner_loop id rest newrev_defenv'
    | Field (name, ty, _) :: rest ->
       let newrev_defenv' = Rev_environment.extend name (ty, id) rev_defenv' in
       inner_loop id rest newrev_defenv'
  in
  match l with
    [] -> rev_defenv
  | (id, _, body_l) :: rest ->
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
                      (fun (id, param, body_l) ->
                        (id, param, (List.map
                                (fun z -> match z with
                                            Constructor (name, ty) -> Constructor (name, replace ty defenv')
                                          | Field (name, ty, mutability) -> Field (name, replace ty defenv', mutability))
                                body_l))) all_l in
                  let newdefenv = bind_defenv replaced_l !defenv in
                  let newrev_defenv = bind_rev_defenv replaced_l !rev_defenv in
                  defenv := newdefenv;
                  rev_defenv := newrev_defenv;
               | (id, param, body_l) :: inner_rest ->
                  let (name_l, tyvars) = get_name_and_tyvar_list body_l in
                  let (is_ok, not_bound_param) = check_tyvars_are_bound param tyvars in
                  if not is_ok then
                    err ("type parameter not bound: " ^ not_bound_param)
                  else if check_whether_duplication name_l then
                    err ("one type cannot have elements which have same name")
                  else if List.mem id id_l then
                    err ("multiple definition of type " ^ id)
                  else
                    let indexed_id = (string_of_int (fresh_index ())) ^ "#" ^ id in
                    let newdefenv = Environment.extend indexed_id (param, body_l) defenv' in
                    let all_l' = List.map (fun (x, y, z) -> if x = id then (indexed_id, y, z) else (x, y, z)) all_l in
                    make_and_newenv all_l' inner_rest (id :: id_l) newdefenv)
            in
            make_and_newenv head head [] !defenv;
            make_newenv outer_rest defenv rev_defenv)
      in
      make_newenv l (ref defenv) (ref rev_defenv)
  | _ -> err ("For debug: this error cannot occur")
