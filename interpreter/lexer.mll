{
let reservedWords = [
  (* Keywords *)
  ("and", Parser.LETAND);
  ("dfun", Parser.DFUN);
  ("else", Parser.ELSE);
  ("false", Parser.FALSE);
  ("fun", Parser.FUN);
  ("if", Parser.IF);
  ("in", Parser.IN);
  ("let", Parser.LET);
  ("match", Parser.MATCH);
  ("rec", Parser.REC);
  ("then", Parser.THEN);
  ("true", Parser.TRUE);
  ("with", Parser.WITH);
] 
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\009' '\012' '\n']+     { main lexbuf }

| "(*" { comment 0 lexbuf }

| "-"? ['0'-'9']+
    { Parser.INTV (int_of_string (Lexing.lexeme lexbuf)) }

| "(" { Parser.LPAREN }
| ")" { Parser.RPAREN }
| ";;" { Parser.SEMISEMI }
| "+" { Parser.PLUS }
| "-" { Parser.MINUS }
| "*" { Parser.MULT }
| "<" { Parser.LT }
| "=" { Parser.EQ }
| "->" { Parser.RARROW }
| "&&" { Parser.AND }
| "||" { Parser.OR }
| "[" { Parser.LSTLPRN }
| "]" { Parser.LSTRPRN }
| "::" { Parser.CONS }
| "|" { Parser.BAR }
| ";" { Parser.SEMI }

| ['a'-'z'] ['a'-'z' '0'-'9' '_' '\'']*
    { let id = Lexing.lexeme lexbuf in
      try 
        List.assoc id reservedWords
      with
      _ -> Parser.ID id
     }
| eof { exit 0 }

and comment i = parse
  "(*" { comment (i+1) lexbuf }
| "*)" 
  { if i = 0 then main lexbuf
    else comment (i-1) lexbuf 
  }
| _ { comment i lexbuf }


