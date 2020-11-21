
{

  open Format

  let comment = ref ""

  let fmt = ref std_formatter

}

rule tes = parse
  | '#' ([^ '\n' '\r'] * as com ) ('\r')? '\n'
      { fprintf !fmt "(%s%s)@." !comment com; tes lexbuf }
  | "(*"
      { fprintf !fmt "(COMMENT "; camlcomment lexbuf }
  | '\r' 
      { tes lexbuf }
  | [' ' '\t' '\n']+ as s 
      { fprintf !fmt "%s" s ; tes lexbuf }
  | '[' 
      { fprintf !fmt "(VAR " ; vars lexbuf }
  | ( [^ '\r' '[' '#' ] + ) as s
      { fprintf !fmt "(RULES@.%s" s ; rules lexbuf }
  | eof 
      { failwith "file ended without finding any rule" }

and camlcomment = parse
  | '\r' 
      { camlcomment lexbuf }
  | "*)"
      { fprintf !fmt ")"; tes lexbuf }
  | "*"
      { fprintf !fmt "*"; camlcomment lexbuf }
  | [^ '*' '\r']+ as s
      { fprintf !fmt "%s" s ; camlcomment lexbuf }
  | eof
      { failwith "file ended in (* .. *) comment" }

and vars = parse
  | ',' 
      { fprintf !fmt " "; vars lexbuf }
  | '\r' 
      { vars lexbuf }
  | ']' 
      { fprintf !fmt ")@.(RULES"; rules lexbuf }
  | ( [^ '\r' ',' ']'] + ) as s
      { fprintf !fmt "%s" s ; vars lexbuf}
  | eof 
      { failwith "eof in vars" }

and rules = parse
  | '\r' 
      { rules lexbuf }
  | '\n' 
      { fprintf !fmt "@."; rules lexbuf }
  | "->" ([^ ' '] as c)
      { fprintf !fmt "-> %c" c; rules lexbuf }
  | "-> " 
      { fprintf !fmt "-> "; rules lexbuf }
  | '-' 
      { fprintf !fmt "-"; rules lexbuf }
  | ';' 
      { rules lexbuf }
  | '.' '\r'
      { rules lexbuf }
  | '.' '\n'
      { fprintf !fmt "@."; rules lexbuf }
  | '.' 
      { fprintf !fmt "."; rules lexbuf }
  | ( [^ ';' '-' '\r' '\n' '.' ] + ) as s
      { fprintf !fmt "%s" s ; rules lexbuf }
  | eof 
      { fprintf !fmt ")@."  }

{

  let main () =
    try
      if Array.length Sys.argv <> 3
      then (printf "Usage: testotrs <comment> <file>"; exit 2);
      comment := Sys.argv.(1);
      let file = Sys.argv.(2) in
      let out = (Filename.chop_extension file) ^ ".trs" in
      let cin = open_in file in
      let cout = open_out out in
      let lb = Lexing.from_channel cin in
      fmt := formatter_of_out_channel cout;
      tes lb;
      close_in cin;
      close_out cout;
      exit 0
    with
      | Sys_error msg ->
	  eprintf "System error: %s.@." msg;
	  exit 1

  let _ = Printexc.catch main ()

}
	     



