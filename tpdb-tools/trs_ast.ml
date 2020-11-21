 
type ident = Lexing.position * string

type term = Term of ident * (term list)

type cond = Arrow of term * term | Darrow of term * term

type rule = Rew of cond list * term * term | RelRew of cond list * term * term

type theory =
  | Builtin of ident * ident list
  | Equations of (term * term) list

type strategy = 
  | Innermost
  | Outermost
  | ContextSensitive of (ident * (Lexing.position * int) list) list

type decl =
  | VarDecl of ident list
  | TheoryDecl of theory list
  | RulesDecl of rule list
  | StrategyDecl of strategy
  | OtherDecl of ident * string list

open Format
open Lexing

let print_loc fmt loc =
  fprintf fmt "File \"%s\", line %d, character %d" 
    loc.pos_fname loc.pos_lnum (loc.pos_cnum - loc.pos_bol + 1)
  
