
{

  open Lexing
  open Lp_parser

  let ident (loc,id) =
    match id with
      | "is" -> IS(loc,id) 
      | "mod" -> MOD(loc,id)
      | _ -> ID(loc,id)
}

let letter = ['a'-'z' 'A'-'Z' '0'-'9' '\'' '_']

rule token = parse
  | [' ' '\r' '\t'] 
      {  token lexbuf }
  | '\n' | '%' [^'\n']* '\n'
      { let ln = lexbuf.lex_curr_p.pos_lnum
	and off = lexbuf.lex_curr_p.pos_cnum
	in
	lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
				 pos_lnum = ln+1; pos_bol = off};
	token lexbuf }
  | "/*"
      { comment lexbuf }
  | ":-"                
      { COLONMINUS }
  | "("
      { LPAR }
  | ")"
      { RPAR }
  | ","
      { COMMA }
  | ";"
      { SEMICOLON }
  | ":"
      { COLON }
  | "@"
      { AT }
  | "`"
      { BACKQUOTE }
  | "."
      { DOT }
  | '['
      { LSQBRACKET }
  | ']'
      { RSQBRACKET }
  | '|'
      { BAR }
  | '-'
      { MINUS (Lexing.lexeme_start_p lexbuf, Lexing.lexeme lexbuf) }
  | '+'
      { PLUS (Lexing.lexeme_start_p lexbuf, Lexing.lexeme lexbuf) }
  | '*'
      { STAR (Lexing.lexeme_start_p lexbuf, Lexing.lexeme lexbuf) }
  | '^'
      { CARET (Lexing.lexeme_start_p lexbuf, Lexing.lexeme lexbuf) }
  | '/'
      { SLASH (Lexing.lexeme_start_p lexbuf, Lexing.lexeme lexbuf) }
  | '\\'
      { BACKSLASH (Lexing.lexeme_start_p lexbuf, Lexing.lexeme lexbuf) }
  | '='
      { EQUAL (Lexing.lexeme_start_p lexbuf, Lexing.lexeme lexbuf) }
  | '<'
      { LT (Lexing.lexeme_start_p lexbuf, Lexing.lexeme lexbuf) }
  | '>'
      { GT (Lexing.lexeme_start_p lexbuf, Lexing.lexeme lexbuf) }
  | "=<"
      { EQLT (Lexing.lexeme_start_p lexbuf, Lexing.lexeme lexbuf) }
  | ">="
      { GTEQ (Lexing.lexeme_start_p lexbuf, Lexing.lexeme lexbuf) }
  | "=\\=" | "\\=="
      { NEQ (Lexing.lexeme_start_p lexbuf, Lexing.lexeme lexbuf) }
  | "!"
      { BANG (Lexing.lexeme_start_p lexbuf, Lexing.lexeme lexbuf) }
  | '\'' [^'\'']* '\''
      { STRING (Lexing.lexeme_start_p lexbuf, Lexing.lexeme lexbuf) }
  | ['A'-'Z' '_'] letter* 
      { VAR (Lexing.lexeme_start_p lexbuf, Lexing.lexeme lexbuf) }
  | ['a'-'z' '0'-'9'] letter*
      { ident (Lexing.lexeme_start_p lexbuf, Lexing.lexeme lexbuf) }
  | _ 
      { failwith ("Unrecognized character " ^ (Lexing.lexeme lexbuf)) }
  | ('%' [^'\n']*)? eof 
      { EOF }

and comment = parse
  | "*/" 
      { token lexbuf }
  | '\n' 
      { let ln = lexbuf.lex_curr_p.pos_lnum
	and off = lexbuf.lex_curr_p.pos_cnum
	in
	lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
				 pos_lnum = ln+1; pos_bol = off};
	comment lexbuf }
  | [^ '\n']
      { comment lexbuf }
  | eof
      { failwith "Unterminated comment" }



