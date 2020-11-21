(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

convert a tpdb file into a problem
******************************************************************************)

open Problem;;

val parse_trs : in_channel -> Trs_ast.decl list;;

val pb_of_trs : Trs_ast.decl list -> problem;;

val parse_srs : in_channel -> Srs_ast.decl list;;

val pb_of_srs : Srs_ast.decl list -> problem;;
