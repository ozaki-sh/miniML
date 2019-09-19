let r1 = ref 0
let f1 (x:unit) = r1 := !r1 + 1;;

let r2 = ref []
let f2 x = x :: !r2;;
