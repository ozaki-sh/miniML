type a = A | B | C | D
type b = A | B | C
type c = B | C | D;;

let f x = match x with A -> 0 | B -> 1 | D -> 2;;
