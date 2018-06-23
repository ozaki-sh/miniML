let f x l =
    match x, l with
      0, h :: t -> 0
    | 1, h :: t -> h
    | _, h :: t -> h + 1
    | _, _ -> 100;;
