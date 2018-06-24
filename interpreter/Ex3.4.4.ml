let makemult = fun maker -> fun x ->
if x < 1 then 1 else x * maker maker (x + -1) in
let fact = fun x -> makemult makemult x in
fact 4;;
