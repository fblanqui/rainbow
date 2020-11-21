%{

  open Srs_ast

%}

%token EOF
%token LPAR RPAR COMMA ARROW ARROWEQ
%token <Lexing.position * string> ID
%token <string> STRING
%token <Lexing.position> LEFTMOST RIGHTMOST RULES STRATEGY  

%type < Srs_ast.decl list > spec
%start spec
%%

spec:
| LPAR decl RPAR spec   { $2::$4 }
| EOF         { [] }
;

decl:
| RULES listofrules     { RulesDecl($2) }
| STRATEGY strategydecl { StrategyDecl($2) }
| ID anylist            { OtherDecl($2) }
;

anylist:
| /* epsilon */             { [] }
| id anylist                { (snd $1)::$2 }
| STRING anylist            { $1::$2 }
| LPAR anylist RPAR anylist { ("("::$2) @ (")"::$4) }
| COMMA anylist             { ","::$2 }
| ARROW anylist             { "->"::$2 }
;

id:
| ID               { $1 }
| LEFTMOST         { $1,"LEFTMOST" }
| RIGHTMOST        { $1,"RIGHTMOST" }
| RULES            { $1,"RULES" }
| STRATEGY         { $1,"STRATEGY" }
;


listofrules:
| /* epsilon */            { [] }
| rule                     { [$1] }
| rule COMMA listofrules   { $1::$3 }
;

rule:
| word ARROW word      { Rew($1,$3) }
/*
| word ARROW           { Rew($1,[]) }
*/
| word ARROWEQ word    { RelRew($1,$3) }
/*
| word ARROWEQ         { RelRew($1,[]) }
|      ARROWEQ word    { RelRew([],$2) }
*/
;

word:
| /* epsilon */      { [] }
| id word            { $1::$2 }
;

strategydecl:
| LEFTMOST                    { Leftmost }
| RIGHTMOST                    { Rightmost }
;




