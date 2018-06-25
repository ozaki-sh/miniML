(* パターン１ 実行結果は 25 *)
let fact = fun n -> n + 1 in
let fact = fun n -> if n < 1 then 1 else n * fact (n + -1) in
  fact 5;;

(* パターン２ 実行結果は 25 *)
let fact = dfun n -> n + 1 in
let fact = fun n -> if n < 1 then 1 else n * fact (n + -1) in
  fact 5;;

(* パターン３ 実行結果は 120 *)
let fact = fun n -> n + 1 in
let fact = dfun n -> if n < 1 then 1 else n * fact (n + -1) in
  fact 5;;

(* パターン４ 実行結果は 120 *)
let fact = dfun n -> n + 1 in
let fact = dfun n -> if n < 1 then 1 else n * fact (n + -1) in
  fact 5;;

(* 説明上、一つ目のfactをfact1、二つ目のfactをfact2と呼ぶことにする。
どのパターンにおいても fact 5 で呼び出されるfactは後に定義されているfact2の方である。そして、5 < 1 はfalseであるから 5 * fact (5 + -1) を評価することになる。このfactがfact1かfact2なのかが問題となる。
パターン１とパターン２の場合は、fact2がfunで定義されているので、問題となるfactはfact2の定義時に見えているfactなのでfact1となる。したがって、5 * (4 + 1) となって結果は25となる。
パターン３とパターン４の場合は、fact2がdfunで定義されているので、問題となるfactはfact2の呼び出し時(各パターン中の4行目)に見えているfactなのでfact2となる。したがって、5 * (4 * fact (4 + -1))となって、このfactも同様にfact2なのでこれを繰り返して 5 * (4 * (3 * (2 * (1 * 1)))) となって結果は120となる。
なお、fact1は自由変数を持たないのでfunとdfunのどちらで定義しても同じである。 *)