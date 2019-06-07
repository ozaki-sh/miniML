type tree = Lf | Br of tree * int * tree;;

let rec map f t =
  match t with
    Lf -> Lf
  | Br (l, i, r) -> Br (map f l, f i, map f r);;

let rec fold f a t =
  match t with
    Lf -> a
  | Br (l, i, r) -> f (fold f a l) i (fold f a r);;

let t1 = Br (Lf, 1, Lf);;
let t2 = Br (t1, 2, Lf);;
let t3 = Br (Lf, 3, Lf);;
let t4 = Br (t3, 4, t2);;
