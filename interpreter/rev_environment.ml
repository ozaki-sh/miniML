type t = (Syntax.tydecl * Syntax.id) list

exception Not_bound

let empty = []
let extend x v env = (x,v)::env

let member body env =
  let rec body_func_for_Constructor id env =
    match env with
      [] -> false
    | (Syntax.Constructor (id', _), _) :: rest when id = id' -> true
    | _ :: rest -> body_func_for_Constructor id rest
  and body_func_for_Field id env =
    match env with
      [] -> false
    | (Syntax.Field (id', _), _) :: rest when id = id' -> true
    | _ :: rest -> body_func_for_Field id rest
  in
  match body with
    Syntax.Constructor (id, _) -> body_func_for_Constructor id env
  | Syntax.Field (id, _) -> body_func_for_Field id env

let rec get_possible_for_Construcor id env =
  match env with
    [] -> []
  | (Syntax.Constructor (id', _), type_name) :: rest when id = id' ->
     type_name :: get_possible_for_Construcor id rest
  | _ :: rest -> get_possible_for_Construcor id rest

let rec get_possible_for_Field id env =
  match env with
    [] -> []
  | (Syntax.Field (id', _), type_name) :: rest when id = id' ->
     type_name :: get_possible_for_Construcor id rest
  | _ :: rest -> get_possible_for_Construcor id rest


let rec lookup body env =
  if member body env then
    match body with
      Syntax.Constructor (id, tyop) ->
       get_possible_for_Construcor id env
    | Syntax.Field (id, ty) ->
       get_possible_for_Field id env
  else
    raise Not_bound
