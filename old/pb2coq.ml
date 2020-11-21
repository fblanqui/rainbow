(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

convert a Rainbow problem file into a Coq file
******************************************************************************)

open Util;;
open Libxml;;
open Error;;

let main () =
  let xml = parse_xml stdin in
  let pb = Pb_of_xml.problem xml in
  let rmap = Rename.renaming_of_problem pb in
  let pb = Rename.rename_problem rmap pb in
  let bi = Buffer.create 1000 and bp = Buffer.create 1000 in
    Coq_of_pb.genr_problem bp pb;
    Require.require_import_modules bi;
    Buffer.output_buffer stdout bi;
    Buffer.output_buffer stdout bp;;

let _ = run main;;
