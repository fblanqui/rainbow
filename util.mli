(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

modules and functions on basic data structures
******************************************************************************)

(*****************************************************************************)
(* XML positions *)
(*****************************************************************************)

val dummy_pos : int * int * int * int;;
val error_pos : int * int * int * int -> string;;

(*****************************************************************************)
(* Lexing positions *)
(*****************************************************************************)

val lex_pos : out_channel -> Lexing.position -> unit;;

(*****************************************************************************)
(* file parsing *)
(*****************************************************************************)

val extension : string -> string option;;

val parse_file : (in_channel -> 'a) -> string -> 'a;;

(*****************************************************************************)
(** exit function *)
(*****************************************************************************)

val error : string -> 'a;;

(*****************************************************************************)
(** generic functions for handling references *)
(*****************************************************************************)

val get_set : 'a -> (unit -> 'a) * ('a -> unit);;
val get_set_bool : unit -> (unit -> bool) * (unit -> unit);;
  (* default is false *)

(*****************************************************************************)
(** verbose and debug modes *)
(*****************************************************************************)

val set_verbose : unit -> unit;;
val get_verbose : unit -> bool;;

val set_debug : unit -> unit;;
val get_debug : unit -> bool;;

val set_hack : unit -> unit;;
val get_hack : unit -> bool;;

(*****************************************************************************)
(* counters *)
(*****************************************************************************)

val counter : unit -> unit -> int;;

(*****************************************************************************)
(** ordered types *)
(*****************************************************************************)

module type TYP = sig type t end;;
module type ORD = Set.OrderedType;;

module Ord : sig
  module Make (M : TYP) : ORD with type t = M.t
end;;

(*****************************************************************************)
(* integers *)
(*****************************************************************************)

module Int : TYP with type t = int;;
module IntOrd : ORD with type t = int;;
module IntSet : Set.S with type elt = int;;
module IntMap : Map.S with type key = int;;

val int_set_of_list : ('a -> IntSet.t) -> 'a list -> IntSet.t;;

(* nats_decr_lt n = [n-1; n-2; ..; 0] *)

val nats_decr_lt : int -> int list;;

(* nats_incr_lt n = [0; 1; ..; n-1] *)
val nats_incr_lt : int -> int list;;

(*****************************************************************************)
(* characters *)
(*****************************************************************************)

val is_alpha_char_code : int -> bool;;
val is_Alpha_char_code : int -> bool;;
val is_digit_char_code : int -> bool;;

val is_space : char -> bool;;
val is_digit : char -> bool;;

(*****************************************************************************)
(* printing *)
(*****************************************************************************)

type 'a bprint = Buffer.t -> 'a -> unit;;
type 'a fprint = out_channel -> 'a -> unit;;

val fprint : 'a bprint -> 'a fprint;;
val sprint : 'a bprint -> 'a -> string;;

val string : string bprint;;
val int : int bprint;;
val int64 : int64 bprint;;
val bool : bool bprint;;
val option : 'a bprint -> 'a option bprint;;
val pair : 'a bprint -> string -> 'b bprint -> ('a * 'b) bprint;;
val first : 'a bprint -> ('a * 'b) bprint;;
val second : 'b bprint -> ('a * 'b) bprint;;

(* add parentheses around *)
val par : 'a bprint -> 'a bprint;;

val prefix : string -> 'a bprint -> 'a bprint;;
val postfix : string -> 'a bprint -> 'a bprint;;
val endline : 'a bprint -> 'a bprint;;

(*****************************************************************************)
(* lists *)
(*****************************************************************************)

(* append_map f l1 l2 = rev_map f l1 @ l2 *)
val append_map : ('a -> 'b) -> 'a list -> 'b list -> 'b list;;

(* iteri f [x1;..;xn] = f 1 x1; ..; f n xn *)
val iteri : (int -> 'a -> unit) -> 'a list -> unit;;

(* [position x xs] returns the position in xs of the first element
   equal to x. raise Not_found if there is none. *)
val position : 'a -> 'a list -> int;;

val flat_map : ('a -> 'b list) -> 'a list -> 'b list;;

val clist : 'a -> int -> 'a list;;

(* split_last x1 [x2;..;xn;xn+1] = [x1;..;xn], xn+1 *)
val split_last : 'a -> 'a list -> 'a list * 'a;;
val map_split_last : ('a -> 'b) -> 'a -> 'a list -> 'b list * 'b;;

val repeat : int -> 'a -> 'a list;;
val last : 'a -> 'a list -> 'a;;
val remove_last : 'a list -> 'a list;;
val remove_first : 'a list -> 'a -> 'a list;;
val remove_firsts : 'a list -> 'a list -> 'a list;;

(* print nothing for empty list *)
val list : string -> 'a bprint -> 'a list bprint;;

(* [list_nil nil sep elt] prints [nil] for empty list *)
val list_nil : string -> string -> 'a bprint -> 'a list bprint;;

(* add parenthesis around if the list is not empty *)
val plist : 'a list bprint -> 'a list bprint;;

(*****************************************************************************)
(** strings *)
(*****************************************************************************)

(* may raise Scanf.Scan_failure *)
val int_of_string : string -> int;;
val int64_of_string : string -> int64;;
val float_of_string : string -> float;;
val bool_of_string : string -> bool;;

module Str : TYP with type t = string;;
module StrOrd : ORD with type t = string;;
module StrSet : Set.S with type elt = string;;
module StrMap : Map.S with type key = string;;

type renaming = string StrMap.t;;

val renaming_map : (string -> 'a) -> StrSet.t -> 'a StrMap.t;;

(* fails if element/key already in the set/map *)
val set_add_chk : string -> StrSet.t -> StrSet.t;;
val add_chk : string -> 'a -> 'a StrMap.t -> 'a StrMap.t;;
val merge_chk : 'a StrMap.t -> 'a StrMap.t -> 'a StrMap.t;;

val set : string -> StrSet.t bprint;;
val pset : string -> StrSet.t bprint;;
val map : string -> 'a bprint -> string -> 'a StrMap.t bprint;;
val pmap : string -> 'a bprint -> string -> 'a StrMap.t bprint;;

(*****************************************************************************)
(* variable map *)
(*****************************************************************************)

(* initialize the variable map *)
val init_var_map : unit -> unit;;

(* [var s] returns the variable associated to [s] or a new variable *)
val var : string -> int;;
