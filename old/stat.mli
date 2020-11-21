(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-05-29

computing statistics from a log file
******************************************************************************)

open Printf;;
open Log;;

val add_stat : data -> unit;;

val compute_total : unit -> unit;;

val print_stats : unit -> unit;;
