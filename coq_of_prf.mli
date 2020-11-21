(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

from the internal representation of termination proofs to color
******************************************************************************)

open Proof;;
open Util;;
open Problem;;

val genr_certif : problem -> Buffer.t -> certificate bprint;;
