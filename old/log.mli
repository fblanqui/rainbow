(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-05-29

reading and printing of log files
******************************************************************************)

open Scanf;;
open Printf;;
open Filename;;
open Sys;;

(*****************************************************************************)
(* data structure of a log file *)
(*****************************************************************************)

type sort = Term | String;;

type kind = Std | Rel | AC;;

type strat = Full | In | Out | CS;;

type prover_result = Yes | Maybe | No | Killed | Anomaly;;

type coq_result = Ok | Error | Timeout;;

type data = {
  d_file_name : string;
  d_sort : sort;
  d_kind : kind;
  d_strat : strat;
  d_prover_result : prover_result;
  d_prover_time : float;
  d_prf : bool;
  d_v : bool;
  d_coq_result : coq_result;
  d_coq_time : float };;

val print_data : data -> unit;;

val read_data : unit -> data;;

val directory : string -> (data -> unit) -> string -> unit;;
