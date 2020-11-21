(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-10-20

generate an OCaml type and parser from an XSD file
******************************************************************************)

open Libxml;;
open Error;;
(*open Xsd;;
open Util;;*)

let main () =
  (* This line use for DEBUG*)
  (*let xml = parse_xml (let ic = open_in_bin Sys.argv.(1) in ic) in*)
  (*DEBUG*)
  (*Printf.bprintf b "(*%a*)\n\n" (list "\n\n" xsd)
    (flatten_innersequence (flatten_simpl_to_groupref (flatten_innerchoice xsds)));*)

  let xml  = parse_xml stdin           in
  let xsds = Xsd_of_xml.xsd_of_xml xml in 
  let b    = Buffer.create 10000       in

  Ml_of_xsd.genr_ml b xsds;
  Buffer.output_buffer stdout b;;

let _ = run main;;



