(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

produce file.v from file.pb and file.prf
******************************************************************************)

open Util;;
open Rename;;
open Libxml;;
open Error;;

let parse_args () =
  match Sys.argv with
    | [| _; pb_fn; prf_fn |] -> pb_fn, prf_fn
    | [| cmd; _ |] | [| cmd |] ->
	prerr_endline ("usage: " ^ cmd ^ " file.pb file.prf");
	exit 1
    | _ -> invalid_arg "Sys.argv";;

let main () =
  let pb_fn, prf_fn = parse_args () in
  (* get renaming map from problem *)
  let pb = Pb_of_xml.problem (parse_file parse_xml pb_fn) in
  let rmap = renaming_of_problem pb in
  let pb = rename_problem rmap pb in
  (* get and rename proof *)
  let prf = Prf_of_xml.certificate (parse_file parse_xml prf_fn) in
  let prf = rename_certificate rmap prf in
  (* generate coq output *)
  let br = Buffer.create 10000
  and bi = Buffer.create 1000
  and bp = Buffer.create 1000 in
    Coq_of_pb.genr_problem bi pb;
    Coq_of_prf.genr_certif pb bi bp prf;
    Require.require_import_modules br;
    Buffer.output_buffer stdout br;
    Buffer.output_buffer stdout bi;
    Buffer.output_buffer stdout bp;;

let _ = run main;;
