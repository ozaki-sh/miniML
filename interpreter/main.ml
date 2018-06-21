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
      let result_list = [] in
      let rec list_process l env r_list=        
        match l with
          [] -> (env, r_list)
        | head :: outer_rest ->
            let rec list_list_process l env r_list=
              match l with
                [] -> list_process outer_rest env r_list
              | (id, newenv, v) as set:: inner_rest -> list_list_process inner_rest newenv (set :: r_list)
            in 
              list_list_process head env r_list
      in
        let (newenv, returned_result_list) = list_process decls env result_list in
        let rec remove_duplication l id_l=
          match l with
            [] -> []
          | (id, newenv, v) as head :: tail ->
              if List.exists (fun x -> x = id) id_l then
                remove_duplication tail id_l
              else
                head :: (remove_duplication tail (id :: id_l))
        in
          let once_list = remove_duplication returned_result_list [] in
          let rec display l = 
            match l with
              [] -> read_eval_print newenv
            | (id, newenv, v) :: rest ->
                Printf.printf "val %s = " id;
                pp_val v;
                print_newline();
                display rest
          in
            display (List.rev once_list)

          
    with   
      Eval.Error s -> print_error_and_go ("Error! " ^ s)
    | Parser.Error -> print_error_and_go "Syntax Error! at parser"
    | Failure s -> print_error_and_go ("Syntax Error! at " ^ s)
    | Sys_error s -> print_error_and_go ("File Error! " ^ s)
    | _ -> print_error_and_go "Syntax Error! at unknown"


let read_eval_print_from_file env filename =
  flush stdout;
  let file = open_in filename in
  let str = ref "" in
  try while true do str := !str ^ (input_line file) ^ " " done
  with End_of_file -> 
    close_in file;
    let rec get_str_list_by_semisemi left right start l =
      try
        let left_char = String.get !str left in
        let right_char = String.get !str right in
        if left_char = ';' && right_char = ';' then
          get_str_list_by_semisemi (left + 2) (right + 2) (right + 1) 
                                   (String.sub !str start (right-start+1) :: l)
        else if right_char = ';' then
           get_str_list_by_semisemi (left + 1) (right + 1) start l 
        else
           get_str_list_by_semisemi (left + 2) (right + 2) start l 
      with
        Invalid_argument _ -> l
    in
      let rec inner_loop env str_list =
        match str_list with
          [] -> print_string "---end of file---";
                print_newline();
                read_eval_print env
        | str :: str_rest ->
          let print_error_and_go s = 
            print_string s;
            print_newline();
            inner_loop env str_rest
          in
            try
              let decl = Parser.toplevel Lexer.main (Lexing.from_string str) in
              let decls = eval_decl env decl in
              let rec list_process l env =        
                match l with
                  [] -> inner_loop env str_rest
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
            | _ -> print_error_and_go "Syntax Error! cause is unknown"
      in
        inner_loop env (List.rev (get_str_list_by_semisemi 0 1 0 []))


let initial_env = Environment.empty
  (*Environment.extend "i" (IntV 1)
    (Environment.extend "v" (IntV 5) 
       (Environment.extend "x" (IntV 10) Environment.empty))*)

let _ = 
  try let filename = Sys.argv.(1) in
        read_eval_print_from_file initial_env filename
  with
    Invalid_argument _ -> read_eval_print initial_env

(*let _ = read_eval_print initial_env*)
