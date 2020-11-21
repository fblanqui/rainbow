(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-05-29

computes statistics from a log file
******************************************************************************)

open Printf;;
open Stat;;
open Log;;
open Sys;;

(* read log data from stdin *)
let rec compute_stats_from_logfile () =
  try add_stat (read_data ()); compute_stats_from_logfile ()
  with End_of_file -> ();;

let main compute_stats =
  compute_stats ();
  compute_total ();
  print_stats ();;

main compute_stats_from_logfile;;
