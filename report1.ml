(* Exercise 2.6 *)
let usdollar_of_yen yen =
  let tmp1 = (float_of_int yen) /. 111.12 *. 100.0 in
  let tmp2 = int_of_float (tmp1 *. 10.0) in
  let modulo = tmp2 mod 10 in
  if modulo >= 5 then (ceil tmp1) /. 100.0
    else (floor tmp1) /. 100.0

let capitalize x =
  let code = int_of_char x in
  if code >= 97 && code <= 122 then
    (char_of_int) (code - 32)
  else x

(* Exercise 3.7 *)
let rec pow1 (x, n) =
  if n = 0 then 1.0
    else x *. pow1 (x, n-1)

let rec pow2 (x, n) =
  if n <= 2 then pow1 (x, n)
    else if n mod 2 = 0 then
      pow2 (pow2 (x, 2), n / 2)
    else x *. pow2 (pow2 (x, 2), (n-1) / 2)

(* Exercise 3.11(1) *)
let rec gcd (m, n) =
  if n = 0 then m
  else gcd (n, m mod n)

(* Exercise 3.11(2) *)
let rec comb (n, m) =
  if m = 0 || m = n then 1
  else comb (n-1, m) + comb (n-1, m-1)

(* Exercise 3.11(3) *)
let fib_iter n =
  let rec fib_iter_internal n curr prev =
    if n = 1 then curr
    else fib_iter_internal (n-1) (curr+prev) curr
  in
    fib_iter_internal n 1 0

(* Exercise 3.11(4) *)
let rec max_ascii str =
  let str_length = String.length str in
    if str_length = 1 then str.[0]
    else
      let now_max = max_ascii (String.sub str 1 (str_length-1)) in
      if str.[0] > now_max then str.[0]
      else now_max

(* Exercise 4.1 *)
let integral f a b =
  let delta = (b-.a) /. 10000.0 in
  let rec sum f a i d =
    if i = 1.0 then ((f a) +. (f (a +. d))) *. d /. 2.0
    else (((f (a +. (i -. 1.0) *. d)) +. (f (a +. i *. d))) *. d /. 2.0) +. (sum f a (i -. 1.0) d)
  in
    sum f a 10000.0 delta

(* Exercise 4.4 *)
let uncurry curried (x, y) =
  curried x y

(* Exercise 4.5 *)
let fib_repeat n =
  let (fibn, _) =
    let rec repeat f n x =
      if n > 0 then repeat f (n - 1) (f x) else x
    in
      if n = 1 || n = 2 then (1, 0)
      else repeat (fun (x, y) -> (x + y, x)) (n-1) (1, 0)
  in
    fibn

(* Exercise 4.7 *)
(* s k k 1 -> k 1 (k 1)
           -> k 1 [1を返す定数関数]
           -> 1                     *)
let k x y = x
let s x y z = x z (y z)
let second x y = s k k y

(* Exercise 5.3(1) *)
let rec downto0 n =
  if n = 0 then [0]
  else n :: downto0 (n-1)

(* Exercise 5.3(4) *)

(* Exercise 5.6 *)

(* Exercise 6.2 *)
type nat = Zero | OneMoreThan of nat

let rec int_of_nat n =
  match n with
    Zero -> 0
  | OneMoreThan n'-> 1 + (int_of_nat n')

let rec mul n m =
  match n with
    Zero -> 0
  | OneMoreThan n' -> (int_of_nat m) + (mul n' m)

let rec monus n m =
  match n with
    Zero -> 0
  | OneMoreThan n' ->
     (match m with
        Zero -> (int_of_nat n)
      | OneMoreThan m' -> monus n' m')

