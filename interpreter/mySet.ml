type 'a t = 'a list

let empty = []

let singleton x = [x]

let from_list x =
  let rec remove_duplication l l' =
    match l with
      [] -> []
    | head :: rest ->
       if List.mem head l' then remove_duplication rest l'
       else head :: (remove_duplication rest (head :: l'))
  in
  remove_duplication x []
let to_list x = x

let rec insert x = function
    [] -> [x]
  | y::rest -> if x = y then y :: rest else y :: insert x rest

let union xs ys =
  List.fold_left (fun zs x -> insert x zs) ys xs

let rec remove x = function
    [] -> []
  | y::rest -> if x = y then rest else y :: remove x rest

let diff xs ys =
  List.fold_left (fun zs x -> remove x zs) xs ys

let intersection xs ys =
  diff xs (diff xs ys)

let member = List.mem

let rec map f = function
    [] -> []
  | x :: rest -> insert (f x) (map f rest)

let rec bigunion = function
    [] -> []
  | set1 :: rest -> union set1 (bigunion rest)

let length = List.length
