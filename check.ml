(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2010-11-11

main procedure for converting a file from one format to another
and checking the correctness of a proof using CoLoR extracted code
******************************************************************************)

open Error;;
open Main;;
open ProofChecker;;
open Util;;

set_usage_msg ("usage: " ^ Sys.argv.(0) ^
  " [-h] -i<ifmt> file1 [-i<ifmt> file2] [-o<ofmt>]\n\n  \
  where <ifmt> is either: trs, srs, pb, xtc, prf, cpf\n    \
    and <ofmt> is either: pb, prf, coq\n\n\
  If no output format is given, then it checks the correctness of the proof\n\
  given as input. Otherwise, it converts the input file into the output \
  format\nand sends the result on stdout.\n");;

let check pb prf =
  let s, r = Color.problem pb in
  let c = Color.certificate prf in
    match check_proof s r c with
      | TerminationEstablished -> print_endline "YES"
      | Error -> print_endline "NO";;

let main() =
  parse_args();
  ignore (get_inputs());
  match get_output() with
    | Some o -> convert o (get_inputs())
    | None ->
	match get_inputs() with
	  | [Problem tpb, spb; Proof tprf, sprf] ->
	      check (pb_of_problem_file tpb spb) (prf_of_proof_file tprf sprf)
	  | [Proof Cpf, s] ->
	      let cpf = parse_file parse_cpf s in
		check (Pb_of_cpf.problem cpf) (Prf_of_cpf.certificate cpf)
	  | _ -> error "invalid combination of options";;

let _ = run main;;
