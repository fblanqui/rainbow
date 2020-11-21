
val todo : Buffer.t -> unit
val type_sequences : string -> Buffer.t -> Xsd.xsd -> unit
val par_of_sequence : string -> Buffer.t -> Xsd.xsd -> unit
val type_sequence : string -> Buffer.t -> Xsd.xsd -> unit
val sequence_in_choice : string -> Buffer.t -> Xsd.xsd -> unit
val type_in_choice : string -> Buffer.t -> Xsd.xsd -> unit
val type_choices : string -> Buffer.t -> Xsd.xsd -> unit
val type_choice : string -> Buffer.t -> Xsd.xsd -> unit
val elt_type_choice : string -> Buffer.t -> Xsd.xsd -> unit
val genr_type : Buffer.t -> Xsd.xsd -> unit
val print_types : Buffer.t -> Xsd.xsd list list -> unit
val genr_types : Buffer.t -> Xsd.xsd list list -> unit
val num_of_name : string list -> string list -> int -> string -> int option
val name_of_num : 'a list -> 'a list -> int -> int -> 'a
val coq_xsd_types : (string * string) list
val undefined : string list
val len_undefined : int
val builtin_undefined_types : Xsd.xsd list
val defined : Xsd.xsd list -> string list
val matrix : Xsd.xsd list -> bool array array
val closure_matrix : Xsd.xsd list -> bool array array
val line_matrix : Xsd.xsd list -> bool array array
val equivalence : Xsd.xsd list -> int list list
val sort_equivalence : Xsd.xsd list -> int list
val xsds_of_int : Xsd.xsd list -> int list list -> Xsd.xsd list list
val xsds_sorted : Xsd.xsd list -> Xsd.xsd list list
val genr_coq : Buffer.t -> Xsd.xsd list -> unit
