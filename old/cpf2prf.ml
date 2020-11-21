(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-09-02

produce file.prf from file.pb and file.cpf
******************************************************************************)

open Util;;
open Libxml;;
open Error;;

let parse_args () =
  match Sys.argv with
    | [| _; pb_fn; cpf_fn |] -> pb_fn, cpf_fn
    | [| cmd; _ |] | [| cmd |] ->
	prerr_endline ("usage: " ^ cmd ^ " file.pb file.cpf");
	exit 1
    | _ -> invalid_arg "Sys.argv";;

let main () =
  let pb_fn, cpf_fn = parse_args () in
  (* get renaming map from problem *)
  let pb = Pb_of_xml.problem (parse_file parse_xml pb_fn) in
  let rmap = Rename.renaming_of_problem pb in
  (* convert and rename certificate *)
  let cpf = Cpf_of_xml.certificationProblem (parse_file parse_xml cpf_fn) in
  let prf = Prf_of_cpf.certificate cpf in
  let prf = Rename.rename_certificate rmap prf in
  let xml = Xml_of_prf.certificate prf in
    output_xml xml;;

let _ = run main;;
