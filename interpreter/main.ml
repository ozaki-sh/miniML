open Syntax
open Eval

let rec read_eval_print env =
  print_string "# ";
  flush stdout;
  let print_error_and_go s = 
    print_string s;
    print_newline();
    read_eval_print env
  in
    try
      let decl = Parser.toplevel Lexer.main (Lexing.from_channel stdin) in
      let (id, newenv, v) = eval_decl env decl in
        Printf.printf "val %s = " id;
        pp_val v;
        print_newline();
        read_eval_print newenv
    with 
      Eval.Error s -> print_error_and_go ("Error! " ^ s)
    | Parser.Error -> print_error_and_go "Syntax Error! at parser"
    | Failure s -> print_error_and_go ("Syntax Error! at " ^ s)
    | _ -> print_error_and_go "Syntax Error! at unknown"



let initial_env = 
  Environment.extend "i" (IntV 1)
    (Environment.extend "v" (IntV 5) 
       (Environment.extend "x" (IntV 10) Environment.empty))

let _ = read_eval_print initial_env
