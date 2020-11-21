(*****************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

representation of problems in color
******************************************************************************)

open Problem;;
open Util;;

val bool : bool bprint;;
val coq_list : 'a bprint -> 'a list bprint;;
val vector : 'a bprint -> 'a list bprint;;
val option : 'a bprint -> 'a option bprint;;

type sig_kind = A | V;;

val string_of_sig_kind : sig_kind -> string;;

val new_sig_id : int -> arity_map -> int;;
val parent_sig : int -> int;;

val get_amap : int -> arity_map;;
val arity : int -> symbol -> int;;

val symbol_sig : int -> symbol bprint;;
val symbol_pat : int -> symbol bprint;;

val fun_def_symb :
  string (* function name *) -> string (* output type *) ->
  string (* return statement *) -> 'a bprint -> int ->
  string (* default case *) -> (symbol * 'a) list bprint;;

val term : sig_kind -> int -> term bprint;;
val word : word bprint;;

val rule : sig_kind -> int -> trs_rule bprint;;
val srs_rule : srs_rule bprint;;

val sig_module : Buffer.t ->
  sig_kind -> int -> string -> 'a bprint -> 'a -> arity_map -> unit;;
val sig_module_of_amap : Buffer.t ->
  sig_kind -> int -> string -> arity_map -> unit;;
val sig_include : Buffer.t ->
  sig_kind -> int -> string -> arity_map -> unit;;

val genr_problem : problem bprint;;
