(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

convert a TPDB trs file into a Rainbow problem file
******************************************************************************)

open Util;;
open Libxml;;
open Error;;

let main () =
  let pb = Pb_of_tpdb.parse_trs stdin in
  let xml = Xml_of_pb.problem pb in
    output_xml xml;;

let _ = run main;;
