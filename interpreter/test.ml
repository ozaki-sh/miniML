let rec f l =
  match l with
    [] -> []
  | [x] -> x
  | true :: r -> f r;;
