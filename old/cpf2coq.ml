(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-09-02

produce file.v from file.pb and file.cpf
******************************************************************************)

open Util;;
open Rename;;
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
  let rmap = renaming_of_problem pb in
  let pb = rename_problem rmap pb in
  (* convert and rename proof *)
  let cpf = Cpf_of_xml.certificationProblem (parse_file parse_xml cpf_fn) in
  let prf = Prf_of_cpf.certificate cpf in
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
