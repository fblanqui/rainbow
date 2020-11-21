(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-09-02

convert a CPF file into a Coq file
******************************************************************************)

open Util;;
open Libxml
open Error;;

let main () =
  let pb = Pb_of_xtc.parse_xtc stdin in
  let xml = Xml_of_pb.problem pb in
    output_xml xml;;

let _ = run main;;
