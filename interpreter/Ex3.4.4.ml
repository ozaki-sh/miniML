let makemult = fun maker -> fun x ->
if x < 1 then 1 else x * maker maker (x + -1) in
let fact = fun x -> makemult makemult x in
fact 4;;

(* ���̃v���O������"4 +"��x��J��Ԃ��čŌ��"0"������悤�ɂȂ��Ă���B
   ������K��ɂ���ɂ́A�܂��Ō��"0"��"1"�ɂ���K�v������(�|���Z������)�B
   �����āA"4 +"��"x *"�ɕς���΁Ax��1�������Ă����̂Ŏ��R�ƊK��ɂȂ�B
   �Ō�ɂ��̃v���O������24��Ԃ��l�q�������B
   fact 4
-> makemult makemult 4
-> 4 * makemult makemult (4-1)
-> 4 * (3 * makemult makemult (3-1))
-> 4 * (3 * (2 * makemult makemult (2-1)))
-> 4 * (3 * (2 * (1 * makemult makemult (1-1))))
-> 4 * (3 * (2 * (1 * 1)))
-> 24 *)
