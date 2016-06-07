{
  open Parser

  let keyword_tbl = Hashtbl.create 31
  let _ = List.iter (fun (keyword, tok) -> Hashtbl.add keyword_tbl keyword tok)
    [("if", IF);
     ("repeat", REPEAT);
     ("readInt", READINT);
    ]
}

let id = ['a'-'z' 'A'-'Z'](['a'-'z' 'A'-'Z' '\'' '0'-'9' '_'])*

rule token = parse
| [' ' '\t' '\n' '\r'] {token lexbuf }
| ['0'-'9']+ as lxm { INT (int_of_string lxm) }
| "/*" { token_comment 0 lexbuf }
| "(" { LPAREN }
| ")" { RPAREN }
| ":=" { ASSIGN }
| "*" { STAR }
| ";" { SEMICOLON }
| "+" { PLUS }
| "-" { MINUS }
| "&" { AMPER }
| id { let id = Lexing.lexeme lexbuf in
       (*let _ = print_endline id in*)
       try Hashtbl.find keyword_tbl id
       with _ -> ID id
     }
| eof { EOF }
and token_comment n = parse
    | "/*" { token_comment (n+1) lexbuf }
	| "*/" {
      if n=0
      then token lexbuf
	  else token_comment (n-1) lexbuf
    }
	| _ { token_comment n lexbuf }
