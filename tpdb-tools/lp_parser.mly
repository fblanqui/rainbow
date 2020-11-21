%{

  open Lp_ast

%}

%token EOF
%token LPAR RPAR COMMA COLONMINUS DOT SEMICOLON 
%token AT COLON BACKQUOTE
%token RSQBRACKET LSQBRACKET BAR
%token <Lexing.position * string> ID VAR IS MOD
%token <Lexing.position * string> PLUS MINUS STAR EQUAL BANG CARET
%token <Lexing.position * string> SLASH BACKSLASH NEQ LT GT EQLT GTEQ
%token <Lexing.position * string> STRING

%type < Lp_ast.decl list > spec
%start spec
%%

spec:
| decl spec   { $1::$2 }
| EOF         { [] }
;

decl:
| lit DOT                    { Clause($1,[]) }
| lit COLONMINUS litlist DOT { Clause($1,$3) }
| COLONMINUS lit DOT         { Query($2) }
;

lit:
| BANG                       { Pred($1,[]) }
| ident                     { Pred($1,[]) } 
| ident LPAR termlist RPAR  { Pred($1,$3) }
| term EQUAL term           { Pred($2,[$1;$3]) }
| term GT term           { Pred($2,[$1;$3]) }
| term LT term           { Pred($2,[$1;$3]) }
| term NEQ term           { Pred($2,[$1;$3]) }
| term EQLT term           { Pred($2,[$1;$3]) }
| term GTEQ term           { Pred($2,[$1;$3]) }
| term IS term              { Pred($2,[$1;$3]) }
;

litlist:
| lit                 { [$1] }
| lit COMMA litlist   { $1::$3 }
;

termlist:
| term                { [$1] }
| term COMMA termlist { $1::$3 }
;

term:
| listnotation          { $1 }
| VAR                   { Var($1) }
| STRING                { Term($1,[]) }
| ident                    { Term($1,[]) }
| ident LPAR termlist RPAR { Term($1,$3) }
| term PLUS term           { Term($2,[$1;$3]) }
| term MINUS term           { Term($2,[$1;$3]) }
| term STAR term           { Term($2,[$1;$3]) }
| term MOD term           { Term($2,[$1;$3]) }
| term CARET term           { Term($2,[$1;$3]) }
| term SLASH term           { Term($2,[$1;$3]) }
| term BACKSLASH term           { Term($2,[$1;$3]) }
| term EQUAL term           { Term($2,[$1;$3]) }
| MINUS term               { Term($1,[$2]) }
| LPAR termlist RPAR    { Term((Lexing.dummy_pos,"tuple"),$2) }
;

listnotation:
| LSQBRACKET RSQBRACKET { Term((Lexing.dummy_pos,"[]"),[]) }
| LSQBRACKET conslist RSQBRACKET { $2 }
;

conslist:
| term                { Term((Lexing.dummy_pos,"|"),[$1]) }
| term COMMA conslist { Term((Lexing.dummy_pos,"|"),[$1;$3]) }
| term BAR term       { Term((Lexing.dummy_pos,"|"),[$1;$3]) }
;

ident:
| ID { $1 }
| IS { $1 }
;






