open Syntax
open Eval
open Typing
open Define

let debug = ref false

let rec read_eval_print env tyenv defenv rev_defenv store =
  print_string "# ";
  flush stdout;
  let print_error_and_go s =
    print_string s;
    print_newline();
    read_eval_print env tyenv defenv rev_defenv store
  in
  try
    let decl = Parser.toplevel Lexer.main (Lexing.from_channel stdin) in
    if !debug then
      (print_string (Debug.string_of_decl decl);
       print_newline());
    match decl with
      TypeDecls l ->
       let (newdefenv, newrev_defenv) = def_decl defenv rev_defenv decl in
       let rec inner_display l is_first =
         match l with
           [] -> ()
         | (id, param, body) :: rest ->
            let pref = if is_first then "type " else "and " in
            let str_param = string_of_param_decl param in
            let str = pref ^ str_param ^ id ^ " = " in
            print_string str;
            pp_defs body;
            print_newline();
            inner_display rest false
       and outer_display l =
         match l with
           [] -> read_eval_print env tyenv newdefenv newrev_defenv store
         | head :: rest ->
            inner_display head true;
            outer_display rest
       in
       outer_display l
    | _ ->
       let (vardefenv, recdefenv) = Environment.partition (fun (_, _, body_l) -> match List.hd body_l with Constructor _ -> true | _ -> false) defenv in
       let tys = ty_decl tyenv defenv vardefenv recdefenv rev_defenv decl in
       let decls = eval_decl env store decl in
       let rec list_process exp_l ty_l env tyenv store res_l =
         match exp_l, ty_l with
           [], [] -> (env, tyenv, store, res_l)
         | ((_, newenv, newstore, _) as exp_set :: exp_rest), ((newtyenv, _) as ty_set :: ty_rest) ->
            list_process exp_rest ty_rest newenv newtyenv newstore ((exp_set, ty_set) :: res_l)
         | _ -> (env, tyenv, store, res_l) (* this line cannot be done *)
       in
       let (newenv, newtyenv, newstore, returned_result_list) = list_process decls tys env tyenv store [] in
       let rec remove_duplication l id_l =
         match l with
           [] -> []
         | ((id, _, _, _) as exp_h, ty_h) :: rest ->
            if List.exists (fun x -> x = id) id_l then
              remove_duplication rest id_l
            else
              (exp_h, ty_h) :: (remove_duplication rest (id :: id_l))
       in
       let once_list = remove_duplication returned_result_list [] in
       let rec display l =
         match l with
           [] -> read_eval_print newenv newtyenv defenv rev_defenv newstore
         | ((id, _, _, v), (_, t)) :: rest ->
            Printf.printf "val %s : " id;
            pp_ty t;
            print_string " = ";
            pp_val v t defenv newstore;
            print_newline();
            display rest
       in
       display (List.rev once_list)
  with
    Eval.Error s -> print_error_and_go ("Error! " ^ s)
  | Parser.Error -> print_error_and_go "Syntax Error! at parser"
  | Failure s -> print_error_and_go ("Syntax Error! at " ^ s)
  | Typing.Error s -> print_error_and_go ("Error! " ^ s)
  | Typing.TypeError (s, ty1, ty2) ->
     if String.length s = 0 then
       print_error_and_go ("Error! Type Error: " ^ string_of_ty ty1 ^ " is not equal to " ^ string_of_ty ty2)
     else
       print_error_and_go ("Error! Type Error: " ^ s)
  | Define.Error s -> print_error_and_go ("Error! " ^ s)
  | Syntax.Error s -> print_error_and_go ("Error! " ^ s)
(*  | _ -> print_error_and_go "Error! cause is unknown"*)


let read_eval_print_from_file env tyenv defenv rev_defenv store filename =
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
    let rec inner_loop env tyenv defenv rev_defenv store str_list =
      match str_list with
        [] -> print_string "---end of file---";
              print_newline();
              read_eval_print env tyenv defenv rev_defenv store
      | str :: str_rest ->
         let print_error_and_go s =
           print_string s;
           print_newline();
           inner_loop env tyenv defenv rev_defenv store str_rest
         in
         try
           let decl = Parser.toplevel Lexer.main (Lexing.from_string str) in
           if !debug then
             (print_string (Debug.string_of_decl decl);
              print_newline());
           (match decl with
              TypeDecls l ->
              let (newdefenv, newrev_defenv) = def_decl defenv rev_defenv decl in
              let rec inner_display l is_first =
                match l with
                  [] -> ()
                | (id, param, body) :: rest ->
                   let pref = if is_first then "type " else "and " in
                   let str_param = string_of_param_decl param in
                   let str = pref ^ str_param ^ id ^ " = " in
                   print_string str;
                   pp_defs body;
                   print_newline();
                   inner_display rest false
              and outer_display l =
                match l with
                  [] -> inner_loop env tyenv newdefenv newrev_defenv store str_rest
                | head :: rest ->
                   inner_display head true;
                   outer_display rest
              in
              outer_display l
            | _ ->
               let (vardefenv, recdefenv) = Environment.partition (fun (_, _, body_l) -> match List.hd body_l with Constructor _ -> true | _ -> false) defenv in
               let tys = ty_decl tyenv defenv vardefenv recdefenv rev_defenv decl in
               let decls = eval_decl env store decl in
               let rec list_process exp_l ty_l env tyenv store res_l =
                 match exp_l, ty_l with
                   [], [] -> (env, tyenv, store, res_l)
                 | ((_, newenv, newstore, _) as exp_set :: exp_rest), ((newtyenv, _) as ty_set :: ty_rest) ->
                    list_process exp_rest ty_rest newenv newtyenv newstore ((exp_set, ty_set) :: res_l)
                 | _ -> (env, tyenv, store, res_l) (* this line cannot be done *)
               in
               let (newenv, newtyenv, newstore, returned_result_list) = list_process decls tys env tyenv store [] in
               let rec remove_duplication l id_l =
                 match l with
                   [] -> []
                 | ((id, _, _, _) as exp_h, ty_h) :: rest ->
                    if List.exists (fun x -> x = id) id_l then
                      remove_duplication rest id_l
                    else
                      (exp_h, ty_h) :: (remove_duplication rest (id :: id_l))
               in
               let once_list = remove_duplication returned_result_list [] in
               let rec display l =
                 match l with
                   [] -> inner_loop newenv newtyenv defenv rev_defenv newstore str_rest
                 | ((id, _, _, v), (_, t)) :: rest ->
                    Printf.printf "val %s : " id;
                    pp_ty t;
                    print_string " = ";
                    pp_val v t defenv newstore;
                    print_newline();
                    display rest in
               display (List.rev once_list))
         with
           Eval.Error s -> print_error_and_go ("Error! " ^ s)
         | Parser.Error -> print_error_and_go "Syntax Error! at parser"
         | Failure s -> print_error_and_go ("Syntax Error! at " ^ s)
         | Sys_error s -> print_error_and_go ("File Error! " ^ s)
         | Typing.Error s -> print_error_and_go ("Error! " ^ s)
         | Typing.TypeError (s, ty1, ty2) ->
            if String.length s = 0 then
              print_error_and_go ("Error! Type Error: " ^ string_of_ty ty1 ^ " is not equal to " ^ string_of_ty ty2)
            else
              print_error_and_go ("Error! Type Error: " ^ s)
         | Define.Error s -> print_error_and_go ("Error! " ^ s)
         | Syntax.Error s -> print_error_and_go ("Error! " ^ s)
         | _ -> print_error_and_go "Error! cause is unknown"
    in
    inner_loop env tyenv defenv rev_defenv store (List.rev (get_str_list_by_semisemi 0 1 0 []))



let _ =
  try
    let str  = Sys.argv.(1) in
    if str = "-d" then
      (debug := true;
       let filename = Sys.argv.(2) in
       read_eval_print_from_file Initial.env Initial.tyenv Initial.defenv Initial.rev_defenv Initial.store filename)
    else
      let filename = str in
      read_eval_print_from_file Initial.env Initial.tyenv Initial.defenv Initial.rev_defenv Initial.store filename
  with
    Invalid_argument _ -> read_eval_print Initial.env Initial.tyenv Initial.defenv Initial.rev_defenv Initial.store
