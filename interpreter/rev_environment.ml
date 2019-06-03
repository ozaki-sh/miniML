type t = (Syntax.name * (Syntax.ty option * Syntax.id)) list

exception Not_bound

let empty = []
let extend x v env = (x,v)::env

let member = List.mem_assoc

let lookup name env =
  let rec body_func l =
    match l with
      [] -> []
    | (name', def) :: rest when name = name' ->
       def :: body_func rest
    | _ :: rest -> body_func rest
  in
  if member name env then
    body_func env
  else
    raise Not_bound
