
{

  open Lexing
  open Trs_parser

let key_list = [
  "CONTEXTSENSITIVE",(fun p -> CONTEXTSENSITIVE p);
  "EQUATIONS",(fun p -> EQUATIONS p);
  "INNERMOST",(fun p -> INNERMOST p);
  "OUTERMOST",(fun p -> OUTERMOST p);
  "RULES",(fun p -> RULES p);
  "STRATEGY",(fun p -> STRATEGY p);
  "THEORY",(fun p -> THEORY p);
  "VAR",(fun p -> VAR p);
]

let key_sym = Hashtbl.create 17 

let _ = List.iter (fun (a,b) -> Hashtbl.add key_sym a b) key_list

let ident pos s =
  try (Hashtbl.find key_sym s) pos
  with Not_found -> ID(pos,s)

exception Lexing_error of string

}

let letter = ['a'-'z' 'A'-'Z' '0'-'9' '\'']
let symbol = ['#' '+' '-' '*' '/' '.' '\\' ':' '=' '<' '>' '_' '@']

rule token = parse
  | [' ' '\r' '\t'] 
      {  token lexbuf }
  | '\n'
      { let ln = lexbuf.lex_curr_p.pos_lnum
	and off = lexbuf.lex_curr_p.pos_cnum
	in
	lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
				 pos_lnum = ln+1; pos_bol = off};
	token lexbuf }
  | "=="                
      { EQUAL }
  | "->"                
      { ARROW }
  | "->="                
      { ARROWEQ }
  | "-><-"           
      { DARROW } 
  | "("
      { LPAR }
  | ")"
      { RPAR }
  | "|"
      { BAR }
  | ","
      { COMMA }
  | (letter | symbol)+
      { ident (Lexing.lexeme_start_p lexbuf) (Lexing.lexeme lexbuf) }
  | _ 
      { OTHER(Lexing.lexeme lexbuf) }
  | eof 
      { EOF }



