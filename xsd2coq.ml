(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-10-20

generate an Coq type from XSD
******************************************************************************)

open Libxml;;
open Error;;

  
let main () =
  (* DEBUG by OCaml debug. *)
  (*let xml = parse_xml (let ic = open_in_bin Sys.argv.(1) in ic) in*)
  
  let xml  = parse_xml stdin           in
  let xsds = Xsd_of_xml.xsd_of_xml xml in
  let b    = Buffer.create 10000       in

  Coq_of_xsd.genr_coq b xsds;
  Buffer.output_buffer stdout b;;

let _ = run main;;
