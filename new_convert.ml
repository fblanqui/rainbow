(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2010-11-11

main procedure for converting a file from one format to another
******************************************************************************)

open Error;;
open New_main;;
open Util;;

set_usage_msg ("usage: " ^ Sys.argv.(0) ^
  " [-h] -i<ifmt> file1 [-i<ifmt> file2] -o<ofmt>\n\n  \
  where <ifmt> is either: trs, srs, pb, xtc, prf, cpf\n    \
    and <ofmt> is either: pb, prf, coq\n\n\
  Converts the input file into the output format and sends the result on \
  stdout.\n");;

let main() =
  parse_args();
  ignore (get_inputs());
  match get_output() with
    | None -> error "no output type provided"
    | Some o -> convert o (get_inputs());; 

let _ =
  try main()
  with Error e -> print_error stderr e; exit 0;;
