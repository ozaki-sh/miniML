open Syntax
open Eval
open Typing
open Define

let debug = ref false

let rec read_eval_print env tyenv defenv rev_defenv =
  print_string "# ";
  flush stdout;
  let print_error_and_go s =
    print_string s;
    print_newline();
    read_eval_print env tyenv
  in
  try
    let decl = Parser.toplevel Lexer.main (Lexing.from_channel stdin) in
    if !debug then
      (print_string (Debug.string_of_decl decl);
       print_newline());
    match decl with
      TypeDecls l ->
       let (newdefenv, newrev_defenv) = def_decl defenv decl in
       let rec inner_display l is_first =
         match l with
           [] -> ()
         | (name, body) :: rest ->
            let pref = if is_first then "type" else "and" in
            Printf.printf "%s %s = " pref name;
            pp_def body;
            print_newline();
            inner_display rest false
       and outer_display l =
         match l with
           [] -> read_eval_print env tyenv newdefenv newrev_defenv
         | head :: rest ->
            inner_display head true;
            outer_display rest
       in
       outer_display l
    | _ ->
       let tys = ty_decl tyenv decl in
       let decls = eval_decl env decl in
       let rec list_process exp_l ty_l env tyenv res_l =
         match exp_l, ty_l with
           [], [] -> (env, tyenv, res_l)
         | ((_, newenv, _) as exp_set :: exp_rest), ((newtyenv, _) as ty_set :: ty_rest) ->
            list_process exp_rest ty_rest newenv newtyenv ((exp_set, ty_set) :: res_l)
         | _ -> (env, tyenv, res_l) (* this line cannot be done *)
       in
       let (newenv, newtyenv, returned_result_list) = list_process decls tys env tyenv [] in
       let rec remove_duplication l id_l =
         match l with
           [] -> []
         | ((id, _, _) as exp_h, ty_h) :: rest ->
            if List.exists (fun x -> x = id) id_l then
              remove_duplication rest id_l
            else
              (exp_h, ty_h) :: (remove_duplication rest (id :: id_l))
       in
       let once_list = remove_duplication returned_result_list [] in
       let rec display l =
         match l with
           [] -> read_eval_print newenv newtyenv defenv rev_defenv
         | ((id, _, v), (_, t)) :: rest ->
            Printf.printf "val %s : " id;
            pp_ty t;
            print_string " = ";
            pp_val v;
            print_newline();
            display rest
       in
       display (List.rev once_list)
  with
    Eval.Error s -> print_error_and_go ("Error! " ^ s)
  | Parser.Error -> print_error_and_go "Syntax Error! at parser"
  | Failure s -> print_error_and_go ("Syntax Error! at " ^ s)
  | Typing.Error s -> print_error_and_go ("Error! " ^ s)
  | Define.Error s -> print_error_and_go ("Error! " ^ s)
  | _ -> print_error_and_go "Error! cause is unknown"


let read_eval_print_from_file env tyenv filename =
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
    let rec inner_loop env tyenv str_list =
      match str_list with
        [] -> print_string "---end of file---";
              print_newline();
              read_eval_print env tyenv
      | str :: str_rest ->
         let print_error_and_go s =
           print_string s;
           print_newline();
           inner_loop env tyenv str_rest
         in
         try
           let decl = Parser.toplevel Lexer.main (Lexing.from_string str) in
           if !debug then
             (print_string (Debug.string_of_decl decl);
              print_newline());
           let tys = ty_decl tyenv decl in
           let decls = eval_decl env decl in
           let rec list_process exp_l ty_l env tyenv res_l =
             match exp_l, ty_l with
               [], [] -> (env, tyenv, res_l)
             | ((_, newenv, _) as exp_set :: exp_rest), ((newtyenv, _) as ty_set :: ty_rest) ->
                list_process exp_rest ty_rest newenv newtyenv ((exp_set, ty_set) :: res_l)
             | _ -> (env, tyenv, res_l) (* this line cannot be done *)
           in
           let (newenv, newtyenv, returned_result_list) = list_process decls tys env tyenv [] in
           let rec remove_duplication l id_l =
             match l with
               [] -> []
             | ((id, _, _) as exp_h, ty_h) :: rest ->
                if List.exists (fun x -> x = id) id_l then
                  remove_duplication rest id_l
                else
                  (exp_h, ty_h) :: (remove_duplication rest (id :: id_l))
           in
           let once_list = remove_duplication returned_result_list [] in
           let rec display l =
             match l with
               [] -> inner_loop newenv newtyenv str_rest
             | ((id, _, v), (_, t)) :: rest ->
                Printf.printf "val %s : " id;
                pp_ty t;
                print_string " = ";
                pp_val v;
                print_newline();
                display rest in
           display (List.rev once_list)
         with
           Eval.Error s -> print_error_and_go ("Error! " ^ s)
         | Parser.Error -> print_error_and_go "Syntax Error! at parser"
         | Failure s -> print_error_and_go ("Syntax Error! at " ^ s)
         | Sys_error s -> print_error_and_go ("File Error! " ^ s)
         | _ -> print_error_and_go "Error! cause is unknown"
    in
    inner_loop env tyenv (List.rev (get_str_list_by_semisemi 0 1 0 []))


let initial_env =
  Environment.extend "i" (IntV 1)
    (Environment.extend "v" (IntV 5)
      (Environment.extend "x" (IntV 10) Environment.empty))

let initial_tyenv =
  Environment.extend "i" (TyScheme ([], TyInt))
    (Environment.extend "v" (TyScheme ([], TyInt))
      (Environment.extend "x" (TyScheme ([], TyInt)) Environment.empty))

let initial_defenv = Environment.empty

let initial_rev_defenv = Rev_environment.empty

let _ =
  try
    let str  = Sys.argv.(1) in
    if str = "-d" then
      (debug := true;
       let filename = Sys.argv.(2) in
       read_eval_print_from_file initial_env initial_tyenv filename)
    else
      let filename = str in
      read_eval_print_from_file initial_env initial_tyenv filename
  with
    Invalid_argument _ -> read_eval_print initial_env initial_tyenv
