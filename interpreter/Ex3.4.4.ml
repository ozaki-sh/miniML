let makemult = fun maker -> fun x ->
if x < 1 then 1 else x * maker maker (x + -1) in
let fact = fun x -> makemult makemult x in
fact 4;;

(* このプログラムが24を返す様子を示す。
   fact 4
-> makemult makemult 4
-> 4 * makemult makemult (4-1)
-> 4 * (3 * makemult makemult (3-1))
-> 4 * (3 * (2 * makemult makemult (2-1)))
-> 4 * (3 * (2 * (1 * makemult makemult (1-1))))
-> 4 * (3 * (2 * (1 * 1)))
-> 24 *)