%{

  open Trs_ast

%}

%token EOF
%token LPAR RPAR COMMA BAR ARROW DARROW EQUAL ARROWEQ
%token <Lexing.position * string> ID
%token <string> STRING OTHER
%token <Lexing.position> CONTEXTSENSITIVE EQUATIONS INNERMOST RULES STRATEGY THEORY VAR OUTERMOST

%type < Trs_ast.decl list > spec
%start spec
%%

spec:
| LPAR decl RPAR spec   { $2::$4 }
| EOF         { [] }
;

decl:
| VAR idlist            { VarDecl($2) }
| THEORY listofthdecl   { TheoryDecl($2) }
| RULES listofrules     { RulesDecl($2) }
| STRATEGY strategydecl { StrategyDecl($2) }
| ID anylist            { OtherDecl($1,$2) }
;

anylist:
| /* epsilon */             { [] }
| id anylist                { (snd $1)::$2 }
| STRING anylist            { $1::$2 }
| OTHER anylist             { $1::$2 }
| LPAR anylist RPAR anylist { ("("::$2) @ (")"::$4) }
| COMMA anylist             { ","::$2 }
| EQUAL anylist             { "="::$2 }
| ARROW anylist             { "->"::$2 }
| ARROWEQ anylist             { "->="::$2 }
| BAR anylist               { "|"::$2 }
;

idlist:
| /* epsilon */ { [] }
| id idlist     { $1::$2 }
;

id:
| ID               { $1 }
| CONTEXTSENSITIVE { $1,"CONTEXTSENSITIVE" }
| EQUATIONS        { $1,"EQUATIONS" }
| INNERMOST        { $1,"INNERMOST" }
| OUTERMOST        { $1,"OUTERMOST" }
| RULES            { $1,"RULES" }
| STRATEGY         { $1,"STRATEGY" }
| THEORY           { $1,"THEORY" }
| VAR              { $1,"VAR" }
;


listofthdecl:
| /* epsilon */                 { [] }
| LPAR thdecl RPAR listofthdecl { $2::$4 }
;

thdecl:
| ID idlist { Builtin($1,$2) } 
| EQUATIONS eqlist { Equations($2) } 
;

eqlist:
| /* epsilon */      { [] }
| equation eqlist    { $1::$2 }
;

equation:
| term EQUAL term    { ($1,$3) }
;

listofrules:
| /* epsilon */      { [] }
| rule listofrules   { $1::$2 }
;

rule:
| term ARROW term                  { Rew([],$1,$3) }
| term ARROW term BAR condlist     { Rew($5,$1,$3) }
| term ARROWEQ term                  { RelRew([],$1,$3) }
/*
| term ARROWEQ term BAR condlist     { RelRew($5,$1,$3) }
*/
;

condlist:
| cond                   { [$1] }
| cond COMMA condlist    { $1::$3 }
;

cond:
| term ARROW term   { Arrow($1,$3) }
| term DARROW term  { Darrow($1,$3) }
;

term:
| id                      { Term($1,[]) }
| id LPAR RPAR            { Term($1,[]) }
| id LPAR termlist RPAR   { Term($1,$3) }
;

termlist:
| term                    { [$1] }
| term COMMA termlist     { $1::$3 }
;

strategydecl:
| INNERMOST                    { Innermost }
| OUTERMOST                    { Outermost }
| CONTEXTSENSITIVE csstratlist { ContextSensitive($2) }
;

csstratlist:
| /* epsilon */      { [] }
| LPAR id intlist RPAR csstratlist { ($2,$3)::$5 }
;

intlist:
| /* epsilon */      { [] }
| id intlist { 
    let (loc,id) = $1 in
    try let n = int_of_string id in (loc,n)::$2 
    with Failure "int_of_string" -> raise Parsing.Parse_error 
}
;
