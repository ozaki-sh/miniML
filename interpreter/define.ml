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
        let (_, _, body_l) = Environment.dlookup id defenv in
        (match List.hd body_l with
           Constructor _ -> TyVariant ((Environment.ilookup id defenv), l)
         | Field _ -> TyRecord ((Environment.ilookup id defenv), l))
      with
        Environment.Not_bound -> err ("type not defined: " ^ id))
  | TyFun (domty, ranty) -> TyFun (replace domty defenv, replace ranty defenv)
  | TyList ty' -> TyList (replace ty' defenv)
  | TyTuple tytup -> TyTuple (case_tytuple tytup)
  | _ -> ty


let rec merge_into_one param properties =
  match param with
    [] -> []
  | head :: rest ->
     let (_, property) = List.split (List.filter (fun (x, _) -> x = head) properties) in
     if List.exists (fun x -> x = Out) property then
       Out :: merge_into_one rest properties
     else
       Safe :: merge_into_one rest properties

let rec update_mini_env id e = function
    [] -> []
  | (id', e') :: rest ->
     if id = id' then
       (id', e) :: rest
     else
       (id', e') :: update_mini_env id e rest

let rec add_property_for_ty ty defenv mini_env default_property =
  let rec case_tytuple tytup property =
    match tytup with
      TyEmpT -> []
    | TyConsT (ty', tytup') -> body_func ty' property @ case_tytuple tytup' property
  and case_ty_list l properties property =
    match l, properties with
      [], [] -> []
    | ty' :: l_rest, property' :: properties_rest ->
       if property' = Out || property = Out then
         body_func ty' Out @ case_ty_list l_rest properties_rest property
       else
         body_func ty' Safe @ case_ty_list l_rest properties_rest property
    | _, _ -> err ("For debug: at case_ty_list in add_property")
  and body_func ty property =
    match ty with
      TyInt -> []
    | TyBool -> []
    | TyString -> []
    | TyStringVar tyvar -> [(tyvar, property)]
    | TyFun (domty, ranty) -> body_func domty Out @ body_func ranty property
    | TyList ty' -> body_func ty' property
    | TyTuple tytup -> case_tytuple tytup property
    | TyVariant (id, l) | TyRecord (id, l) ->
       (try
         let (_, properties, _) = Environment.lookup id defenv in
         case_ty_list l properties property
       with
         Environment.Not_bound ->
          let properties = List.assoc id mini_env in
          case_ty_list l properties property)
    | TyNone _ -> []
    | TyUnit -> []
    | _ -> err ("For debug: at add_property")
  in
  body_func ty default_property

let add_property_for_tydecl defenv mini_env = function
    Constructor (_, ty) -> add_property_for_ty ty defenv mini_env Safe
  | Field (_, ty, mutability) ->
     (match mutability with
        Mutable -> add_property_for_ty ty defenv mini_env Out
      | Immutable -> add_property_for_ty ty defenv mini_env Safe)

let rec add_property_for_triple_list triple_l defenv =
  let rec body_func mini_env =
    let rec inner_body_func l mini_env =
      match l with
        [] -> ([], mini_env)
      | (id, param, body_l) :: rest ->
         let properties = merge_into_one param (List.fold_left (@) [] (List.map (add_property_for_tydecl defenv mini_env) body_l)) in
         let new_mini_env = update_mini_env id properties mini_env in
         let (properties', mini_env') = inner_body_func rest new_mini_env in
         (properties :: properties', mini_env')
    in
    let (properties, mini_env') = inner_body_func triple_l mini_env in
    if mini_env = mini_env' then
      let rec add_property l properties =
        match l, properties with
          [], [] -> []
        | (id, param, body_l) :: l_rest, head :: p_rest ->
           (id, param, head, body_l) :: add_property l_rest p_rest
        | _ -> err ("For debug: at add_property_for_triple_list")
      in
      add_property triple_l properties
    else
      body_func mini_env'
  in
  let id_and_param = List.map (fun (id, param, _) -> (id, param)) triple_l in
  let mini_env = List.map (fun (id, param) -> (id, List.map (fun p -> Safe) param)) id_and_param in
  body_func mini_env

let rec bind_defenv l defenv  =
  match l with
    [] -> defenv
  | (id, param, property, body_l) :: rest ->
     let newdefenv = Environment.extend id (param, property, body_l) defenv in
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
                  let replaced_l_with_property = add_property_for_triple_list replaced_l !defenv in
                  let newdefenv = bind_defenv replaced_l_with_property !defenv in
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
                    let newdefenv = Environment.extend indexed_id (param, [], body_l) defenv' in
                    let all_l' = List.map (fun (x, y, z) -> if x = id then (indexed_id, y, z) else (x, y, z)) all_l in
                    make_and_newenv all_l' inner_rest (id :: id_l) newdefenv)
            in
            make_and_newenv head head [] !defenv;
            make_newenv outer_rest defenv rev_defenv)
      in
      make_newenv l (ref defenv) (ref rev_defenv)
  | _ -> err ("For debug: this error cannot occur")
