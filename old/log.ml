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
open Problem;;

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

let mk_data f p k s pr pt x v cr ct = {
  d_file_name = f;
  d_sort = p;
  d_kind = k;
  d_strat = s;
  d_prover_result = pr;
  d_prover_time = pt;
  d_prf = x;
  d_v = v;
  d_coq_result = cr;
  d_coq_time = ct };;

(*****************************************************************************)
(* printing and scanning functions *)
(*****************************************************************************)

let char_of_sort = function
  | Term -> 'T'
  | String -> 'S';;

let sort_of_char = function
  | 'T' -> Term
  | 'S' -> String
  | c -> raise (Scan_failure (sprintf "'%c' is not a problem" c));;

let char_of_kind = function
  | Std -> 'S'
  | Rel -> 'R'
  | AC -> 'A';;

let kind_of_char = function
  | 'S' -> Std
  | 'R' -> Rel
  | 'A' -> AC
  | c -> raise (Scan_failure (sprintf "'%c' is not a kind" c));;

let char_of_strat = function
  | Full -> 'F'
  | In -> 'I'
  | Out -> 'O'
  | CS -> 'C';;

let strat_of_char = function
  | 'F' -> Full
  | 'I' -> In
  | 'O' -> Out
  | 'C' -> CS
  | c -> raise (Scan_failure (sprintf "'%c' is not a strategy" c));;

let char_of_prover_result = function
  | Yes -> 'Y'
  | Maybe -> 'M'
  | No -> 'N'
  | Killed -> 'K'
  | Anomaly -> 'E';;

let prover_result_of_char = function
  | 'Y' -> Yes
  | 'M' -> Maybe
  | 'N' -> No
  | 'K' -> Killed
  | 'E' -> Anomaly
  | c -> raise (Scan_failure (sprintf "'%c' is not a prover result" c));;

let string_of_prover_result = function
  | Yes -> "YES"
  | Maybe -> "MAYBE"
  | No -> "NO"
  | Killed -> "KILLED"
  | Anomaly -> "ERROR";;

let prover_result_of_string = function
  | "YES" -> Yes
  | "MAYBE" -> Maybe
  | "NO" -> No
  | "KILLED" -> Killed
  | "ERROR" -> Anomaly
  | s -> raise (Scan_failure (sprintf "'%s' is not a prover result" s));;

let char_of_coq_result = function
  | Ok -> 'O'
  | Error -> 'E'
  | Timeout -> 'T';;

let coq_result_of_char = function
  | 'O' -> Ok
  | 'E' -> Error
  | 'T' -> Timeout
  | c -> raise (Scan_failure (sprintf "'%c' is not a coq result" c));;

let char_of_bool = function
  | true -> 'Y'
  | false -> 'N';;

let bool_of_char = function
  | 'Y' -> true
  | 'N' -> false
  | c -> raise (Scan_failure (sprintf "'%c' is not a bool" c));;

let print_data d =
  printf "%s %c %c %c %s %.2f %c %c %c %.2f\n"
    d.d_file_name (char_of_sort d.d_sort) (char_of_kind d.d_kind)
    (char_of_strat d.d_strat) (string_of_prover_result d.d_prover_result)
    d.d_prover_time (char_of_bool d.d_prf) (char_of_bool d.d_v)
    (char_of_coq_result d.d_coq_result) d.d_coq_time;;

let error s = prerr_endline s; exit 1;;

let read_data () =
  let s = read_line () in
    try sscanf s "%s %c %c %c %s %f %c %c %c %f"
      (fun fn sort kind strat pr pt prf v cr ct ->
	 mk_data fn (sort_of_char sort) (kind_of_char kind)
	   (strat_of_char strat) (prover_result_of_string pr) pt
	   (bool_of_char prf) (bool_of_char v) (coq_result_of_char cr) ct)
    with Scan_failure f ->
      error ("parse error in \"" ^ s ^ "\":\n" ^ f ^ "\n");;

(*****************************************************************************)
(* function generating datas by exploring a directory *)
(*****************************************************************************)

type file_type = F_trs | F_srs | F_xtc;;

let file_type_of_string = function
  | "trs" -> Some F_trs
  | "srs" -> Some F_srs
  | "xtc" -> Some F_xtc
  | _ -> None;;

let file_type s =
  try file_type_of_string (Util.get_extension s)
  with Not_found -> None;;

let parser_of_file_type = function
  | F_xtc -> Pb_of_xtc.parse_xtc
  | F_trs -> Pb_of_tpdb.parse_trs
  | F_srs -> Pb_of_tpdb.parse_srs;;

let problem_of_file t s = Util.parse_file (parser_of_file_type t) s;;

exception Is_not_unary;;

let sort_of_trs s =
  match s.trs_algebra with
    | Varyadic -> Term
    | Signature amap ->
	try SymbMap.iter (fun _ n -> if n<>1 then raise Is_not_unary) amap;
	  String
	with Is_not_unary -> Term;;

let sort_of_problem = function
  | Trs s -> sort_of_trs s
  | Srs _ -> String

let strat_of_trs s =
  match s.trs_strategy with
    | None -> Full
    | Some Innermost -> In
    | Some Outermost -> Out
    | Some (ContextSensitive _) -> CS;;

let kind_of_trs s =
  if s.trs_axioms <> [] then AC
  else if s.trs_le_rules <> [] then Rel
  else Std;;

let kind_of_srs s = if s.srs_le_rules <> [] then Rel else Std;;

let sks_of_problem = function
  | Trs t -> let k = kind_of_trs t in
      begin match sort_of_trs t, strat_of_trs t with
	| String, Full -> String, k, Full
	| (String|Term), ((Full|In|Out|CS) as s) -> Term, k, s
      end
  | Srs t -> String, kind_of_srs t, Full;;

let sks_of_file t s = sks_of_problem (problem_of_file t s);;

let result_of_file s ext =
  try
    let s = chop_extension s ^ ext in
    let c = open_in s in
    let r = fscanf c "%s" (fun x -> x) in
      close_in c;
      r
  with End_of_file -> error ("premature end of file: " ^ s)
    | Scan_failure m -> error ("scan failure in " ^ s ^ ":\n" ^ m);;

let do_try f s =
  try f s with Scan_failure m -> error ("scan failure in " ^ s ^ ":\n" ^ m);;

let prover_result_of_file s =
  do_try prover_result_of_string (result_of_file s ".out");;

let prover_time_of_file s =
  do_try float_of_string (result_of_file s ".time");;

let coq_time_of_file s =
  try do_try float_of_string (result_of_file s ".coq")
  with Sys_error _ -> 0.0;;

let coq_result_of_file s =
  let s = chop_extension s in
    if file_exists (s ^ ".vo") then Ok
    else if file_exists (s ^ ".err") then Error
    else Timeout;;

let data_of_file ext t f =
  let sort, kind, strat = sks_of_file t f in
  let mk = mk_data f sort kind strat in
  let r = prover_result_of_file f in
    match r with
      | Yes | No ->
	  let g = chop_extension f in
	  let prf = file_exists (g ^ "." ^ ext)
	  and v = file_exists (g ^ ".v") in
	  let mk = mk r (prover_time_of_file f) prf v in
	    if v then mk (coq_result_of_file f) (coq_time_of_file f)
	    else mk Timeout 0.0
      | Maybe | Killed | Anomaly ->
	  mk r (prover_time_of_file f) false false Timeout 0.0;;

let rec directory ext use_data d =
  Array.iter (file ext use_data d) (readdir d)

and file ext use_data d s =
  let f = concat d s in
    match file_type f with
      | Some t -> if t = F_xtc then use_data (data_of_file ext t f)
      | None -> if is_directory f then directory ext use_data f;;
