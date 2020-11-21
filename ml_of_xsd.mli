(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2010-10-20

generate an OCaml type and parser from an xsd value
******************************************************************************)

(*val todo : Buffer.t -> unit
val keywords : string -> string
val a_an : string -> string
val undefine : string -> string
val chop : string -> string
val parser_of : string -> Buffer.t -> Xsd.xsd -> unit
val parser_sequences : string -> string -> Xsd.xsd Util.bprint
val parser_choice_sequences : string -> string -> Xsd.xsd Util.bprint
val parser_choice : string -> Buffer.t -> Xsd.xsd -> unit
val parser_choice_sequences_2 : 'a -> string -> Buffer.t -> Xsd.xsd -> unit
val parser_choices : string -> Buffer.t -> Xsd.xsd -> unit
val group_parser_choices : string -> Buffer.t -> Xsd.xsd -> unit
val genr_parser : Buffer.t -> Xsd.xsd -> unit
val genr_and_parsers : Buffer.t -> unit
val genr_parsers : Buffer.t -> Xsd.xsd list -> unit
val genr_ml : Buffer.t -> Xsd.xsd list -> unit*)


val todo : Buffer.t -> unit
val keywords : string -> string
val a_an : string -> string
val undefine : string -> string
val chop : string -> string
val parser_of : string -> Buffer.t -> Xsd.xsd -> unit
val type_sequences : 'a -> string -> Xsd.xsd Util.bprint
val sequence_in_choice : string -> string -> Xsd.xsd Util.bprint
val genr_elem_simpl : Buffer.t -> string -> string -> unit
val genr_elem_sequence : Buffer.t -> string -> Xsd.xsd -> unit
val elem_choice_one_child_type : string -> Buffer.t -> Xsd.xsd -> unit
val elem_choice_one_child : Buffer.t -> string -> Xsd.xsd -> unit
val elem_choice_more_child_type : string -> Buffer.t -> Xsd.xsd -> unit
val elem_choice_more_child : Buffer.t -> string -> Xsd.xsd list -> unit
val genr_elem_choice : Buffer.t -> string -> Xsd.xsd list -> unit
val genr_type_elem : Buffer.t -> string -> Xsd.xsd -> unit
val genr_group_sequence : Buffer.t -> string -> Xsd.xsd -> unit
val group_choice_one_child_type : string -> Buffer.t -> Xsd.xsd -> unit
val group_choice_one_child : Buffer.t -> string -> Xsd.xsd -> unit
val group_choice_sequence_child : Buffer.t -> string -> Xsd.xsd list -> unit
val group_choice_elem_child : Buffer.t -> string -> string -> Xsd.xsd -> unit
val group_choice_more_child_type : string -> Buffer.t -> Xsd.xsd -> unit
val group_choice_more_child : Buffer.t -> string -> Xsd.xsd list -> unit
val genr_group_choice : Buffer.t -> string -> Xsd.xsd list -> unit
val genr_type_group : Buffer.t -> Xsd.xsd -> string -> unit
val genr_type : Buffer.t -> Xsd.xsd -> unit
val genr_and_parsers : Buffer.t -> unit
val genr_types : Buffer.t -> Xsd.xsd list -> unit
val genr_ml : Buffer.t -> Xsd.xsd list -> unit
