(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Kim Quyen Ly, 2011-11-28

Strongly connected component
******************************************************************************)

val transClosure : bool array array -> bool array array
exception Incomparable
val linearize : bool array array -> bool array array
val eq_class : bool array array -> int -> int list
val eq_classes : bool array array -> int list list
val cmp_classes : bool array array -> int -> int -> int
val sort_eq_classes : bool array array -> int list -> int list
val closure_matrix : 'a -> ('a -> bool array array) -> bool array array
val line_matrix : 'a -> ('a -> bool array array) -> bool array array
val equivalence : 'a -> ('a -> bool array array) -> int list list
val sort_equivalence : 'a -> ('a -> bool array array) -> int list
val position : string -> string list -> int
val num_of_name : string list -> string -> int option
val name_of_num : 'a list -> int -> 'a
val defined : Xsd.xsd list -> string list
val matrix : Xsd.xsd list -> bool array array
val xsds_of_int_fun : 'a list -> int list list -> 'a list list
val xsds_sorted_fun : Xsd.xsd list -> Xsd.xsd list list
