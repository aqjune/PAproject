%{
%}
%token <int> INT
%token <string> ID
%token ASSIGN STAR SEMICOLON IF REPEAT PLUS MINUS AMPER EOF READINT
%token LPAREN RPAREN
%start main
%type <Program.cmd> main
%type <Program.cmd> cmd
%type <Program.exp> expr
%left PLUS SEMICOLON
%nonassoc IF WHILE
%nonassoc MINUS
%%

main:
cmd EOF { $1 }

cmd:
| LPAREN cmd RPAREN { $2 }
| ID ASSIGN expr { Program.ASSIGN($1, $3) }
| STAR ID ASSIGN expr { Program.PTRASSIGN($2, $4) }
| cmd SEMICOLON cmd { Program.SEQ($1, $3) }
| IF expr cmd cmd { Program.IF($2, $3, $4) }
| REPEAT cmd expr { Program.REPEAT($2, $3) }

expr:
| INT { Program.NUM $1 }
| LPAREN expr RPAREN { $2 }
| expr PLUS expr { Program.ADD($1, $3) }
| MINUS expr { Program.NEG($2) }
| ID { Program.VAR $1 }
| STAR ID { Program.DEREF $2 }
| AMPER ID { Program.LOC $2 }
| READINT { Program.READINT }
