(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

XML parsing and generation
******************************************************************************)

open Xml;;

type tag = string;;

(*****************************************************************************)
(* xml parsing and writing *)
(*****************************************************************************)

val xml_version : string;;
val output_xml : out_channel -> xml -> unit;;
val parse_xml : in_channel -> xml;;

(*****************************************************************************)
(* xml generation *)
(*****************************************************************************)

val elt : string -> Xml.xml list -> Xml.xml
val pc : string -> Xml.xml
val pc_int : int -> Xml.xml
val pc_int64 : int64 -> Xml.xml
val elt_int : string -> int -> Xml.xml

(*****************************************************************************)
(* xml matching *)
(*****************************************************************************)

val height : xml -> int;;

val get_pc : Xml.xml -> string
val string : Xml.xml -> string
val boolean : xml -> bool;;

(* Old code *)
val get_int : Xml.xml -> int
val get_nonNegativeInteger : Xml.xml -> int
val get_positiveInteger : Xml.xml -> int
val integer : Xml.xml -> int
val nonNegativeInteger : Xml.xml -> int
val positiveInteger : Xml.xml -> int

(*****************************************************************************)
(* xml parsing *)
(*****************************************************************************)

val get_first_son : string -> (Xml.xml -> 'a) -> Xml.xml -> 'a
val get_sons : string -> (Xml.xml list -> 'a) -> Xml.xml -> 'a

val try_parse : ('a -> 'b) -> 'a -> 'b option
val parse_list : ('a -> 'b) -> 'a list -> 'b list * 'a list
val parse_first_elt : ('a -> 'b) -> 'a list -> 'b * 'a list
val parse_option : ('a -> 'b) -> 'a list -> 'b option * 'a list
val check_emptyness : Xml.xml list -> unit
