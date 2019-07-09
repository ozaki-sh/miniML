type 'a t = (int * 'a) list


let empty = []
let extend l v store = (l, v) :: store


let rec lookup l store = List.assoc l store


let rec update l v = function
    [] -> []
  | (l', v') :: rest ->
     if l = l' then (l, v) :: rest
     else (l', v') :: update l v rest
