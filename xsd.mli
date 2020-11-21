(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-10-20

internal representation of XSD files
******************************************************************************)

type bound = Bound of int | Unbounded;;

type xsd =
  | Elt of string * xsd option * int * bound
  | Group of string * xsd option * int * bound
  | GroupRef of string * int * bound
  | Choice of xsd list
  | Sequence of xsd list
  | SimpleType of string;;

val xsd : xsd Util.bprint;;

(*****************************************************************************)
(* xsds *)
(*****************************************************************************)

val name_of_elt : xsd -> string
val name_eq : string -> xsd -> bool

val init_types : xsd list -> unit
val _is_group : Util.StrSet.elt -> bool
val next_type : unit -> xsd
val add_type : string option -> xsd -> string * bool

(*
(*val new_type_id : unit -> int;;*)
val init_types : Xsd.xsd list -> unit;;
val _is_group : Util.StrSet.elt -> bool;;
val next_type : unit -> Xsd.xsd;;
val add_type : string option -> Xsd.xsd -> string * bool;;*)

(*****************************************************************************)
(* flattening replace inner choice to groupref and generate Group *)
(*****************************************************************************)

val flatten_innerchoice_xsd : string option -> xsd -> xsd * xsd list
val flatten_innerchoice_xsds : xsd list -> xsd list * xsd list
val flatten_top_innerchoice_xsd : xsd -> xsd * xsd list
val flatten_innerchoice_def : xsd -> xsd list
val flatten_innerchoice : xsd list -> xsd list

(*****************************************************************************)
(* flattening replace inner sequence to groupref and generate Group *)
(*****************************************************************************)
(*
val flatten_innersequence_xsd :
  string -> string option -> xsd -> xsd * xsd list
val flatten_innersequence_xsds : string -> xsd list -> xsd list * xsd list
val flatten_top_innersequence_xsd : string -> xsd -> xsd * xsd list
val flatten_innersequence_def : xsd -> xsd list
val flatten_innersequence : xsd list -> xsd list*)

(*****************************************************************************)
(* Flattening replace <SimpleType> by <GroupRef> *)
(*****************************************************************************)
(*
val flatten_simpl_to_groupref_xsd : string option -> xsd -> xsd * xsd list
val flatten_simpl_to_groupref_xsds : xsd list -> xsd list * xsd list
val flatten_top_simpl_to_groupref : xsd -> xsd * xsd list
val flatten_def_simpl_to_groupref : xsd -> xsd list
val flatten_simpl_to_groupref : xsd list -> xsd list*)

(*****************************************************************************)
(* split xsds *)
(*****************************************************************************)

val get_name_sequence : xsd -> string list
val get_par_name_sequence : xsd -> string list
val get_name_choice : xsd -> string list
val get_name_lists : xsd list -> string list
val get_list_name : xsd -> string list
val get_pair_name : xsd -> string * string list
val get_list_xsds : xsd list -> (string * string list) list

val constructor_name : string -> string -> string;;
