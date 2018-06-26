let makemult = fun maker -> fun x ->
if x < 1 then 1 else x * maker maker (x + -1) in
let fact = fun x -> makemult makemult x in
fact 4;;

(* 元のプログラムは"4 +"をx回繰り返して最後に"0"がくるようになっている。
   これを階乗にするには、まず最後の"0"を"1"にする必要がある(掛け算だから)。
   そして、"4 +"を"x *"に変えれば、xは1ずつ減っていくので自然と階乗になる。
   最後にこのプログラムが24を返す様子を示す。
   fact 4
-> makemult makemult 4
-> 4 * makemult makemult (4-1)
-> 4 * (3 * makemult makemult (3-1))
-> 4 * (3 * (2 * makemult makemult (2-1)))
-> 4 * (3 * (2 * (1 * makemult makemult (1-1))))
-> 4 * (3 * (2 * (1 * 1)))
-> 24 *)
