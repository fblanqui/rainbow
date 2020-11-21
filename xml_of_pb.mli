(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

from the internal representation of problems to xml
******************************************************************************)

open Problem;;
open Xml;;

val fun_symbol : symbol -> xml;;

val term : term -> xml;;

val word : word -> xml list;;

val trs_rule : trs_rule -> xml;;

val srs_rule : srs_rule -> xml;;

val problem : problem -> xml;;
