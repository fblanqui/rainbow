(*****************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

warnings and errors
******************************************************************************)

open Xml;;

val pos_of_xml : xml -> pos;;

(*****************************************************************************)
(* warnings *)
(*****************************************************************************)

val warning : string -> unit;;
val ignored : string -> unit;;

(*****************************************************************************)
(* errors *)
(*****************************************************************************)

type error;;

exception Error of error;;

val not_supported : string -> 'a;;
val error_xml : xml -> string -> 'a;;
val error_fmt : string -> 'a;;

val print_error : out_channel -> error -> unit;;

val run : (unit -> unit) -> unit;;
