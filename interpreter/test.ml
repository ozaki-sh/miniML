let l = [1;2;3];;

let rec add l =
  match l with
    [] -> 0
  | h :: t -> h + (add t);;
