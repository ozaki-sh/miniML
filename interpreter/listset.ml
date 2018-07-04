let rec hd l = match l with x :: rest -> x;;
let rec tl l = match l with x :: rest -> rest;;
let null l = match l with [] -> true | _ -> false;;
let rec nth n l =
  if n = 1 then hd l else nth (n - 1) (tl l);;
let rec take n l =
  if n = 0 then [] else (hd l) :: (take (n - 1) (tl l));;
let rec drop n l =
  if n = 0 then l else drop (n - 1) (tl l );;
let rec length l = 
    match l with
      [] -> 0
    | _ :: rest -> 1 + length rest;;
let rec append l1 l2 =
    match l1 with
      [] -> l2
    | x :: rest -> x :: (append rest l2);;
let rec reverse l =
    match l with
      [] -> []
    | x :: rest -> append (reverse rest) [x];;
let rec forall p l =
    match l with
      [] -> true
    | x :: rest -> if p x then forall p rest else false;;
let rec exists p l =
    match l with 
      [] -> false
    | x :: rest -> (p x) || (exists p rest);;
let rec map f l =
    match l with
      [] -> []
    | x :: rest -> f x :: map f rest;;
let rec fold_right f l e =
    match l with
      [] -> e
    | x :: rest -> f x (fold_right f rest e);;
let rec fold_left f e l =
    match l with
      [] -> e
    | x :: rest -> fold_left f (f e x) rest;;
let rec marge l1 l2 l =
  match l1, l2 with
    [], [] -> reverse l
  | [], y :: ys -> marge l1 ys (y :: l)
  | x :: xs, [] -> marge xs l2 (x :: l)
  | x :: xs, y :: ys ->
      if x < y then marge xs l2 (x :: l)
      else marge l1 ys (y :: l)

  


