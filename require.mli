(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-05-29

manage modules to import
******************************************************************************)

val require : string list -> unit;;
val import : string list -> unit;;
val require_import_modules : Buffer.t -> unit;;
