
open Printf;;
open Libxml;;
open Error;;

let main () = ignore (Newcpf.certificationProblem (Libxml.parse_xml stdin));;

let _ = run main;;
