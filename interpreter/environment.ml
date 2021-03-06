type 'a t = (Syntax.id * 'a) list

exception Not_bound

let empty = []
let extend x v env = (x,v)::env

let rec lookup x env =
  try List.assoc x env with Not_found -> raise Not_bound

let rec map f = function
    [] -> []
  | (id, v)::rest -> (id, f v) :: map f rest

let rec fold_right f env a =
  match env with
      [] -> a
    | (_, v)::rest -> f v (fold_right f rest a)

(*let member = List.mem_assoc*)

let partition p = List.partition (fun (_, v) -> p v)

let rec dlookup x env =
  match env with
    [] -> raise Not_bound
  | (id, v) :: rest ->
     if x = Syntax.remove_index id then
       v
     else
       dlookup x rest

let rec ilookup x env =
  match env with
    [] -> raise Not_bound
  | (id, v) :: rest ->
     if x = Syntax.remove_index id then
       id
     else
       ilookup x rest



