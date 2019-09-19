type 'a tree = Lf | Br of 'a tree * 'a * 'a tree;;

let rec map f t =
  match t with
    Lf -> Lf
  | Br (l, x, r) -> Br (map f l, f x, map f r)

let rec fold f e t =
  match t with
    Lf -> e
  | Br (l, x, r) -> f (fold f e l) x (fold f e r);;

let t = Br (Br (Lf, 1, Lf), 2, Br (Lf, 3, Lf));;
