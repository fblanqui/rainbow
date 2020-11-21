(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2010-06-15

procedures for managing command line options
and converting a file from one format to another
******************************************************************************)

open Arg;;
open Printf;;
open Util;;
open Libxml;;

(*****************************************************************************)
(* input file types *)
(*****************************************************************************)

type problem = Trs | Srs | Pb | Xtc;;
type proof = Cpf | Prf;;

type input = Problem of problem | Proof of proof;;

(* in get_inputs(), the problem always come first *)
let add_input, get_inputs =
  let i = ref [] in
    (fun t s ->
       match t, !i with
	 | _, _::_::_
	 | Proof _, [Proof _,_]
	 | Problem _, [Problem _,_] -> error "too many input files"
	 | Problem _, _ -> i := (t,s) :: !i
	 | _ -> i := !i @ [t,s]),
    (fun () -> if !i = [] then error "no input file provided" else !i);;

let add_problem p = add_input (Problem p);;
let add_proof p = add_input (Proof p);;
 
(*****************************************************************************)
(* output file types *)
(*****************************************************************************)

type output = OutCoq | OutPrf | OutPb | OutXtc;;

let set_output, get_output =
  let o = ref None in
    (fun t () ->
       if !o = None then o := Some t else error "output type already set"),
    (fun () -> !o);;

(*****************************************************************************)
(* command line options parsing *)
(*****************************************************************************)

let set_usage_msg, get_usage_msg =
  let m = ref "" in
    (fun s -> m := s),
    (fun () -> !m);;

let rec options() =
  List.sort (fun (x,_,_) (y,_,_) -> Pervasives.compare x y) (Arg.align
[
  "-h", Unit print_help,
  " Display this list of options";
  "-itrs", String (add_problem Trs),
  " Take a .trs file as input";
  "-isrs", String (add_problem Srs),
  " Take a .srs file as input";
  "-ipb", String (add_problem Pb),
  " Take a .pb file as input";
  "-ixtc", String (add_problem Xtc),
  " Take a .xtc file as input";
  "-iprf", String (add_proof Prf),
  " Take a .prf file as input";
  "-icpf", String (add_proof Cpf),
  " Take a .cpf file as input";
  "-opb", Unit (set_output OutPb),
  " Generate a .pb file on stdout";
  "-oprf", Unit (set_output OutPrf),
  " Generate a .prf file on stdout";
  "-ocoq", Unit (set_output OutCoq),
  " Generate a .v file on stdout";
  "-oxtc", Unit (set_output OutXtc),
  " Generate a .xtc file on stdout";
  "-hack", Unit set_hack,
  " Ignore usable rules and monotony requirements and enforce some conditions";
])

and print_options oc =
  List.iter (fun (k, _, d) -> fprintf oc "%s: %s\n" k d) (options())

and print_help() =
  print_endline (get_usage_msg()); print_options stdout; exit 0;;

let options = options();;

let anon_fun _ = error "invalid option";;

let parse_args() = Arg.parse options anon_fun (get_usage_msg());;

(*****************************************************************************)
(* input file parsing functions *)
(*****************************************************************************)

let pb_of_problem = function
  | Trs -> fun ic -> Pb_of_tpdb.pb_of_trs (Pb_of_tpdb.parse_trs ic)
  | Srs -> fun ic -> Pb_of_tpdb.pb_of_srs (Pb_of_tpdb.parse_srs ic)
  | Xtc -> fun ic -> Pb_of_xtc.problem (Xtc_of_xml.problem (parse_xml ic))
  | Pb -> fun ic -> Pb_of_xml.problem (parse_xml ic);;

let parse_cpf ic = Cpf_of_xml.certificationProblem (parse_xml ic);;

let prf_of_proof = function
  | Prf -> fun ic -> Prf_of_xml.certificate (parse_xml ic)
  | Cpf -> fun ic -> Prf_of_cpf.certificate (parse_cpf ic);;

let pb_of_problem_file t s = parse_file (pb_of_problem t) s;;
let prf_of_proof_file t s = parse_file (prf_of_proof t) s;;

let pb_of_cpf_file s = Pb_of_cpf.problem (parse_file parse_cpf s);;

(*****************************************************************************)
(* generate coq from pb *)
(*****************************************************************************)

let coq_of_pb pb =
  let rmap = Rename.renaming_of_problem pb in
  let pb = Rename.rename_problem rmap pb
  and b = Buffer.create 10000 and br = Buffer.create 1000 in
    Coq_of_pb.genr_problem b pb;
    Require.require_import_modules br;
    Buffer.output_buffer stdout br;
    Buffer.output_buffer stdout b;;

(*****************************************************************************)
(* generate coq from prf *)
(*****************************************************************************)

let coq_of_prf pb prf =
  let rmap = Rename.renaming_of_problem pb in
  let pb = Rename.rename_problem rmap pb
  and prf = Rename.rename_certificate rmap prf
  and b = Buffer.create 50000 and br = Buffer.create 1000
			      and bp = Buffer.create 10000 in
    Coq_of_pb.genr_problem b pb;
    Coq_of_prf.genr_certif pb b bp prf;
    Require.require_import_modules br;
    Buffer.output_buffer stdout br;
    Buffer.output_buffer stdout b;
    Buffer.output_buffer stdout bp;;

(*****************************************************************************)
(* conversion procedure *)
(*****************************************************************************)

let convert o is =
  match o, is with
    | (OutPb|OutPrf), _::_::_ -> error "too many input files"
    | OutPb, [Problem t, s] ->
	output_xml stdout (Xml_of_pb.problem (pb_of_problem_file t s))
    | OutPb, [Proof Cpf, s] ->
	output_xml stdout (Xml_of_pb.problem (pb_of_cpf_file s))
    | OutXtc, [Problem t, s] ->
	output_xml stdout (Xml_of_xtc.problem
		      (Xtc_of_pb.problem (pb_of_problem_file t s)))
    | OutXtc, [Proof Cpf, s] ->
	output_xml stdout (Xml_of_xtc.problem
		      (Xtc_of_pb.problem (pb_of_cpf_file s)))
    | OutPrf, [Proof t, s] ->
	output_xml stdout (Xml_of_prf.certificate (prf_of_proof_file t s))
    | OutCoq, [Problem t, s] -> coq_of_pb (pb_of_problem_file t s)
    | OutCoq, [Problem tpb, spb; Proof tprf, sprf] ->
	coq_of_prf (pb_of_problem_file tpb spb) (prf_of_proof_file tprf sprf)
    | OutCoq, [Proof Cpf, s] ->
	let cpf = parse_file parse_cpf s in
	  coq_of_prf (Pb_of_cpf.problem cpf) (Prf_of_cpf.certificate cpf)
    | _, _ -> error "invalid combination of options";;
