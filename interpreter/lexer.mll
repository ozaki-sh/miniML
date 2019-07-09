{
let reservedWords = [
  (* Keywords *)
  ("and", Parser.METAAND);
  ("bool", Parser.BOOL);
  ("dfun", Parser.DFUN);
  ("else", Parser.ELSE);
  ("false", Parser.FALSE);
  ("fun", Parser.FUN);
  ("if", Parser.IF);
  ("in", Parser.IN);
  ("int", Parser.INT);
  ("let", Parser.LET);
  ("list", Parser.LIST);
  ("match", Parser.MATCH);
  ("mutable", Parser.MUTABLE);
  ("of", Parser.OF);
  ("rec", Parser.REC);
  ("ref", Parser.REF);
  ("string", Parser.STRING);
  ("then", Parser.THEN);
  ("true", Parser.TRUE);
  ("type", Parser.TYPE);
  ("unit", Parser.UNIT);
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
| "[" { Parser.LBOXBRA }
| "]" { Parser.RBOXBRA }
| "::" { Parser.CONS }
| "|" { Parser.BAR }
| ";" { Parser.SEMI }
| "," { Parser.COMMA }
| "_" { Parser.UNDERSCORE }
| ":" { Parser.COLON }
| "^" { Parser.HAT }
| ">" { Parser.MT }
| "**" { Parser.EXPO }
| "!" { Parser.EXCLM }
| ":=" { Parser.COLONEQ }
| "{" { Parser.LCLYBRA }
| "}" { Parser.RCLYBRA }
| "." { Parser.DOT }
| "<-" { Parser.LARROW }

| ['a'-'z'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*
    { let id = Lexing.lexeme lexbuf in
      try
        List.assoc id reservedWords
      with
      _ -> Parser.ID id
     }

| ['"'] ['!' '#'-'~' ]* ['"']
    { let str = Lexing.lexeme lexbuf in
      let len = String.length str in
      Parser.STRINGV (String.sub str 1 (len - 2)) }

| ['''] ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
    { let tyvar = Lexing.lexeme lexbuf in Parser.TYVAR tyvar }

| ['A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*
    { let c = Lexing.lexeme lexbuf in
      Parser.CNSTR c
     }

| eof { exit 0 }

and comment i = parse
  "(*" { comment (i+1) lexbuf }
| "*)"
    { if i = 0 then main lexbuf
      else comment (i-1) lexbuf
    }
| _ { comment i lexbuf }


