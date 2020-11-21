(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2010-11-11

procedures for managing command line options
and converting a file from one format to another
******************************************************************************)

val set_usage_msg : string -> unit;;

type problem = Trs | Srs | Pb | Xtc;;
type proof = Cpf | Prf;;

type input = Problem of problem | Proof of proof;;

val get_inputs : unit -> (input * string) list;;

type output = OutCoq | OutPrf | OutPb | OutXtc;;

val get_output : unit -> output option;;

val parse_args : unit -> unit;;

val pb_of_problem_file : problem -> string -> Problem.problem;;

val prf_of_proof_file : proof -> string -> Proof.certificate;;

val parse_cpf : in_channel -> Cpf.certificationProblem;;

val convert : output -> (input * string) list -> unit;;
