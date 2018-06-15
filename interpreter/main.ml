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
      let decls = eval_decl env decl in
      let rec list_process l env =        
        match l with
          [] -> read_eval_print env
        | head :: outer_rest ->
            let rec list_list_process l env =
              match l with
                [] -> list_process outer_rest env
              | (id, newenv, v) :: inner_rest ->
                  Printf.printf "val %s = " id;
                  pp_val v;
                  print_newline();
                  list_list_process inner_rest newenv
            in 
              list_list_process head env
      in
        list_process decls env
    with   
      Eval.Error s -> print_error_and_go ("Error! " ^ s)
    | Parser.Error -> print_error_and_go "Syntax Error! at parser"
    | Failure s -> print_error_and_go ("Syntax Error! at " ^ s)
    | Sys_error s -> print_error_and_go ("File Error! " ^ s)
    | _ -> print_error_and_go "Syntax Error! at unknown"


(*let read_eval_print_from_file env filename =
  flush stdout;
  let file = open_in filename in
    let rec inner_loop env =    
      let print_error_and_go s = 
        print_string s;
        print_newline();
        inner_loop env
      in
        try
          let decl = Parser.toplevel Lexer.main (Lexing.from_string (input_line file)) in
          let (id, newenv, v) = eval_decl env decl in
            Printf.printf "val %s = " id;
            pp_val v;
            print_newline();
            inner_loop newenv 
        with 
          Eval.Error s -> print_error_and_go ("Error! " ^ s)
        | Parser.Error -> print_error_and_go "Syntax Error! at parser"
        | Failure s -> print_error_and_go ("Syntax Error! at " ^ s)
        | Sys_error s -> print_error_and_go ("File Error! " ^ s)
        | End_of_file -> close_in file;
                         read_eval_print env 
        | _ -> print_error_and_go "Syntax Error! at unknown"
  in
    inner_loop env*)


let initial_env = 
  Environment.extend "i" (IntV 1)
    (Environment.extend "v" (IntV 5) 
       (Environment.extend "x" (IntV 10) Environment.empty))

(*let _ = 
  try let filename = Sys.argv.(1) in
        read_eval_print_from_file initial_env filename
  with
    Invalid_argument _ -> read_eval_print initial_env*)

let _ = read_eval_print initial_env
