(* �p�^�[���P ���s���ʂ� 25 *)
let fact = fun n -> n + 1 in
let fact = fun n -> if n < 1 then 1 else n * fact (n + -1) in
  fact 5;;

(* �p�^�[���Q ���s���ʂ� 25 *)
let fact = dfun n -> n + 1 in
let fact = fun n -> if n < 1 then 1 else n * fact (n + -1) in
  fact 5;;

(* �p�^�[���R ���s���ʂ� 120 *)
let fact = fun n -> n + 1 in
let fact = dfun n -> if n < 1 then 1 else n * fact (n + -1) in
  fact 5;;

(* �p�^�[���S ���s���ʂ� 120 *)
let fact = dfun n -> n + 1 in
let fact = dfun n -> if n < 1 then 1 else n * fact (n + -1) in
  fact 5;;

(* ������A��ڂ�fact��fact1�A��ڂ�fact��fact2�ƌĂԂ��Ƃɂ���B
�ǂ̃p�^�[���ɂ����Ă� fact 5 �ŌĂяo�����fact�͌�ɒ�`����Ă���fact2�̕��ł���B�����āA5 < 1 ��false�ł��邩�� 5 * fact (5 + -1) ��]�����邱�ƂɂȂ�B����fact��fact1��fact2�Ȃ̂������ƂȂ�B
�p�^�[���P�ƃp�^�[���Q�̏ꍇ�́Afact2��fun�Œ�`����Ă���̂ŁA���ƂȂ�fact��fact2�̒�`���Ɍ����Ă���fact�Ȃ̂�fact1�ƂȂ�B���������āA5 * (4 + 1) �ƂȂ��Č��ʂ�25�ƂȂ�B
�p�^�[���R�ƃp�^�[���S�̏ꍇ�́Afact2��dfun�Œ�`����Ă���̂ŁA���ƂȂ�fact��fact2�̌Ăяo����(�e�p�^�[������4�s��)�Ɍ����Ă���fact�Ȃ̂�fact2�ƂȂ�B���������āA5 * (4 * fact (4 + -1))�ƂȂ��āA����fact�����l��fact2�Ȃ̂ł�����J��Ԃ��� 5 * (4 * (3 * (2 * (1 * 1)))) �ƂȂ��Č��ʂ�120�ƂȂ�B
�Ȃ��Afact1�͎��R�ϐ��������Ȃ��̂�fun��dfun�̂ǂ���Œ�`���Ă������ł���B *)