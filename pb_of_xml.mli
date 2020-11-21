(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Ducas Leo, 2007-08-10
- Frederic Blanqui, 2006-05-31

from xml to the internal representation of termination problems
******************************************************************************)

open Xml;;
open Problem;;

val symbol : xml -> symbol;;
val fun_symbol : xml -> symbol;;
val term : xml -> term;;
val word : xml list -> word;;
val trsRule : xml -> trs_rule;;
val srsRule : xml -> srs_rule;;
val trsRules : xml list -> trs_rule list;;
val problem : xml -> problem;;
