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
  let n = 1000000.0 in
  let delta = (b-.a) /. n in
  let rec sum f a i d s =
    if i = 1.0 then ((f a) +. (f (a +. d))) *. d /. 2.0 +. s
    else sum f a (i -. 1.0) d ((((f (a +. (i -. 1.0) *. d)) +. (f (a +. i *. d))) *. d /. 2.0) +. s)
  in
    sum f a n delta 0.0

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
           -> [1を返す定数関数] (k 1)
           -> [1を返す定数関数] [1を返す定数関数]
           -> 1                                    *)
let k x y = x
let s x y z = x z (y z)
let second x y = k (s k k) x y

(* Exercise 5.3(1) *)
let rec downto0 n =
  if n = 0 then [0]
  else n :: downto0 (n-1)

(* Exercise 5.3(3) *)
let rec concat l =
  match l with
    [] -> []
  | head :: tail -> head @ (concat tail)

(* Exercise 5.3(4) *)
let rec zip a b =
  match a with
    [] -> []
  | a_head :: a_tail ->
      (match b with
         [] -> []
       | b_head :: b_tail -> (a_head, b_head) :: (zip a_tail b_tail))

(* Exercise 5.3(5) *)
let rec filter cond l =
  match l with
    [] -> []
  | head :: tail ->
      if (cond head) then head :: (filter cond tail)
      else filter cond tail

(* Exercise 5.6 *)
let rec quicker l sorted =
  match l with
    [] -> sorted
  | [x] -> x :: sorted
  | pivot :: tail ->
      let rec partition left right = function
        [] -> quicker left (pivot ::  (quicker right sorted))
      | head :: tail -> if pivot <= head then partition left (head :: right) tail
                        else partition (head :: left) right tail
      in
        partition [] [] tail

let quick l = quicker l []

(* Exercise 6.2 *)
type nat = Zero | OneMoreThan of nat

let rec int_of_nat n =
  match n with
    Zero -> 0
  | OneMoreThan n'-> 1 + (int_of_nat n')

let rec add n m =
  match n with
    Zero -> m
  | OneMoreThan n' -> OneMoreThan (add n' m)

let rec mul n m =
  match n with
    Zero -> Zero
  | OneMoreThan n' -> add m (mul n' m)

let rec monus n m =
  match n with
    Zero -> Zero
  | OneMoreThan n' ->
     (match m with
        Zero -> n
      | OneMoreThan m' -> monus n' m')

(* Exercise 6.6 *)
type 'a tree = Lf | Br of 'a * 'a tree * 'a tree

let rec reflect t =
  match t with
    Lf -> Lf
  | Br (v, l, r) -> Br (v, reflect r, reflect l)

(* Exercise 6.9 *)
type 'a seq = Cons of 'a * (unit -> 'a seq)

let rec from n = Cons (n, fun () -> from (n + 1))

let head (Cons (x, _)) = x

let tail (Cons (_, f)) = f ()

let rec sift n seq =
  match seq with
    Cons (x, f) ->
      if x mod n = 0 then
        let next = f () in
          Cons (head next, fun () -> sift n (tail next))
      else
        Cons (x, fun () -> sift n (f ()))

let rec sieve (Cons (x, f)) = Cons (x, fun () -> sieve (sift x (f ())))

let primes = sieve (from 2)

let rec nthseq n (Cons (x, f)) =
  if n = 1 then x else nthseq (n - 1) (f ())

type ('a, 'b) sum = Left of 'a | Right of 'b
(* Exercise 6.10(1) *)
let f1 (x, s) =
  match s with
    Left l -> Left (x, l)
  | Right r -> Right (x, r)

(* Exercise 6.10(2) *)
let f2 (s1, s2) =
  match s1 with
    Left l1 ->
     (match s2 with
        Left l2 -> Left (Left (l1, l2))
      | Right r2 -> Right (Left (l1, r2)))
  | Right r1 ->
     (match s2 with
        Left l2 -> Right (Right (r1, l2))
      | Right r2 -> Left (Right (r1, r2)))

(* Exercise 7.2 *)
let incr x =
  x := !x + 1

(* Exercise 7.4 *)
let fact_imp n =
  let i = ref n and res = ref 1 in
    while !i <> 0 do
      res := !res * !i;
      i := !i - 1
    done;
    !res

(* Exercise 7.6 *)
(* let x = ref []　と入力すると、インタプリタは val x : '_a list ref = {contents=[]}　と表示した。つまり、変数xが参照しているリストの型が一度具体化されてしまうと、それ以降はその型のリストへの参照となる。よって、 x := [1] とした時点でxの型は int list となっているので true :: !x は型エラーとなる。なお、 (2 :: !x, true :: !x) 型エラーとなる。 2 :: !x の時点でxの型は int list となるので、 true :: !x は行えないからである。 *)

(* Exercise 7.8 *)
let rec change = function
    (_, 0) -> []
  | ((c :: rest) as coins, total) ->
      if c > total then change (rest, total)
      else
        (try
          c :: change (coins, total - c)
         with Failure "change" -> change (rest, total))
  | _ -> failwith "change"

(* changetotalが0場合は空リストを返す。そうでなくて、coinsが１つ以上の要素を持つ場 合は、先頭のコインがtotalよりも大きいならば、先頭のコインを用いてtotalは崩せないので先頭のコインを取り除いてchangeを呼ぶ。先頭のコインがtotal以下ならば、先頭のコインをリストに加え、残りの金額、すなわちtotal-（先頭のコイン)を崩す。このとき、total-(先頭のコイン)がcoinsの最小の要素より小さいなら崩せないので、どんどんコインが取り除かれて([], total)の形になる。こうなれば例外を投げてtotal-(先頭のコイン)がcoinsの最小の要素より小さくなる直前に戻って、先頭のコインを取り除いたcoinsでtotalを崩す。*)
