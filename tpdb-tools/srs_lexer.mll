
{

  open Lexing
  open Srs_parser

let key_list = [
  "LEFTMOST",(fun p -> LEFTMOST p);
  "RIGHTMOST",(fun p -> RIGHTMOST p);
  "RULES",(fun p -> RULES p);
  "STRATEGY",(fun p -> STRATEGY p) ;
]

let key_sym = Hashtbl.create 17 

let _ = List.iter (fun (a,b) -> Hashtbl.add key_sym a b) key_list

let ident pos s =
  try (Hashtbl.find key_sym s) pos
  with Not_found -> ID(pos,s)

}

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
  | "->"                
      { ARROW }
  | "->="                
      { ARROWEQ }
  | "("
      { LPAR }
  | ")"
      { RPAR }
  | ","
      { COMMA }
  | [^ ' ' '\n' '\r' '\t' '(' ')' ',']+ 
      { ident (Lexing.lexeme_start_p lexbuf) (Lexing.lexeme lexbuf) }
  | eof 
      { EOF }



