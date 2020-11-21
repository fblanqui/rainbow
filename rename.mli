(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-10-20

replace tpdb identifiers by valid coq identifiers
******************************************************************************)

open Problem;;
open Proof;;
open Util;;

val renaming_of_problem : problem -> renaming;;

val rename_problem : renaming -> problem -> problem;;

val rename_certificate : renaming -> certificate -> certificate;;
