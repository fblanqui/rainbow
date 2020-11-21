(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-05-29

computing statistics from a log file
******************************************************************************)

open Printf;;
open Log;;

(*****************************************************************************)
(* data structure for computing statistics *)
(*****************************************************************************)

type stat = {
  mutable s_nb : int;
  mutable s_prover_yes : int;
  mutable s_prover_yes_time : float;
  mutable s_prover_maybe : int;
  mutable s_prover_no : int;
  mutable s_prover_no_time : float;
  mutable s_prover_killed : int;
  mutable s_prover_error : int;
  mutable s_prover_errors : string list;
  mutable s_prover_time : float;
  mutable s_prf : int;
  mutable s_v : int;
  mutable s_coq_ok : int;
  mutable s_coq_error : int;
  mutable s_coq_timeout : int;
  mutable s_coq_yes_time : float;
  mutable s_coq_no_time : float;
  mutable s_coq_time : float;
  mutable s_prf_errors : string list;
  mutable s_v_errors : string list;
  mutable s_coq_errors : string list;
  mutable s_coq_timeouts : string list };;

let make_new_stat0 () = {
  s_nb = 0;
  s_prover_yes = 0;
  s_prover_yes_time = 0.0;
  s_prover_maybe = 0;
  s_prover_no = 0;
  s_prover_no_time = 0.0;
  s_prover_killed = 0;
  s_prover_error = 0;
  s_prover_errors = [];
  s_prover_time = 0.0;
  s_prf = 0;
  s_v = 0;
  s_coq_ok = 0;
  s_coq_error = 0;
  s_coq_timeout = 0;
  s_coq_yes_time = 0.0;
  s_coq_no_time = 0.0;
  s_coq_time = 0.0;
  s_prf_errors = [];
  s_v_errors = [];
  s_coq_timeouts = [];
  s_coq_errors = [] };;

let percent x y = float_of_int (100 * x) /. float_of_int y;;

let div x y = x /. float_of_int y;;

let files _oc =
  let rec aux = function
    | [] -> ()
    | f :: fs -> print_string (" " ^ f); aux fs
  in function
    | [] -> ()
    | fs -> print_string "\n\nfiles:"; aux fs; print_string "\n";;

let print_stat s =
  let n = s.s_nb
  and p = s.s_prover_yes + s.s_prover_no
  and v = s.s_v
  and r = s.s_coq_ok in
  printf "\n\
    number of problems: %n\n\
    \n\
    number of ERROR   : %n (%.2f%%)%a\n\
    number of MAYBE   : %n (%.2f%%)\n\
    number of KILLED  : %n (%.2f%%)\n\
    \n\
    prover score      : %n (%.2f%%) average time : %.2f\n\
    number of YES     : %n (%.2f%%)                %.2f\n\
    number of NO      : %n (%.2f%%)                %.2f\n\
    \n\
    prf/cpf score     : %n (%.2f%%) (%.2f%%)%a\n\
    \n\
    coq gen score     : %n (%.2f%%) (%.2f%%)%a\n\
    \n\
    number of coq TIMEOUT : %n (%.2f%%) (%.2f%%)%a\n\
    \n\
    checker score     : %n (%.2f%%) (%.2f%%) average time : %.2f\n\
    number of YES     :                                     %.2f\n\
    number of NO      :                                     %.2f\n\
    \n\
    number of ERROR   : %n (%.2f%%) (%.2f%%)%a\n\n" n
    s.s_prover_error (percent s.s_prover_error n) files s.s_prover_errors
    s.s_prover_maybe (percent s.s_prover_maybe n)
    s.s_prover_killed (percent s.s_prover_killed n)
    p (percent p n) (div s.s_prover_time n)
    s.s_prover_yes (percent s.s_prover_yes n)
      (div s.s_prover_yes_time s.s_prover_yes)
    s.s_prover_no (percent s.s_prover_no n)
      (div s.s_prover_no_time s.s_prover_no)
    s.s_prf (percent s.s_prf p) (percent s.s_prf n) files s.s_prf_errors
    s.s_v (percent s.s_v p) (percent s.s_v n) files s.s_v_errors
    s.s_coq_timeout (percent s.s_coq_timeout v) (percent s.s_coq_timeout n)
      files s.s_coq_timeouts
    s.s_coq_ok (percent r v) (percent r n) (div s.s_coq_time r)
    (div s.s_coq_yes_time r) (div s.s_coq_no_time r)
    s.s_coq_error (percent s.s_coq_error v) (percent s.s_coq_error n)
    files s.s_coq_errors;;

(*****************************************************************************)
(* functions for computing statistics *)
(*****************************************************************************)

let int_of_sort = function
  | Term -> 0
  | String -> 1;;

let nb_sort = 1;;

let sort_of_int = function
  | 0 -> Term
  | _ -> String;;

let int_of_kind = function
  | Std -> 0
  | Rel -> 1
  | AC -> 2;;

let nb_kind = 2;;

let kind_of_int = function
  | 0 -> Std
  | 1 -> Rel
  | _ -> AC;;

let int_of_strat = function
  | Full -> 0
  | In -> 1
  | Out -> 2
  | CS -> 3;;

let nb_strat = 3;;

let strat_of_int = function
  | 0 -> Full
  | 1 -> In
  | 2 -> Out
  | _ -> CS;;

(* the function index : [0,1] * [0,2] * [0,3] -> [0,23] is bijective *)
let index p k s = p + 2 * k + 6 * s;;

let index_of p k s = index (int_of_sort p) (int_of_kind k) (int_of_strat s);;

let n = 2*3*4 + 1 (* for the total *);;

let t = Array.init n (fun _ -> make_new_stat0 ());;

(*REMOVE: let debug_print_stat s =
  if s.s_nb <> 0 then
    printf "%d %d %d %d %d %d %d %d %d %d\n"
      s.s_nb s.s_prover_yes s.s_prover_maybe s.s_prover_no s.s_prover_killed
      s.s_prf s.s_v s.s_coq_ok s.s_coq_error s.s_coq_timeout;;
 
let debug_print () =
  Array.iter debug_print_stat t; print_endline "===================";;*)

let add_stat d =
  let i = index_of d.d_sort d.d_kind d.d_strat in
  let ti = t.(i) in
  let aux () =
    if d.d_prf then begin
      ti.s_prf <- ti.s_prf + 1;
      if d.d_v then begin
	ti.s_v <- ti.s_v + 1;
	ti.s_coq_time <- ti.s_coq_time +. d.d_coq_time;
	match d.d_coq_result with
	  | Ok -> ti.s_coq_ok <- ti.s_coq_ok + 1;
	      begin match d.d_prover_result with
		| Yes -> ti.s_coq_yes_time <- ti.s_coq_yes_time +. d.d_coq_time
		| No -> ti.s_coq_no_time <- ti.s_coq_no_time +. d.d_coq_time
		| Maybe | Killed | Anomaly -> ()
	      end
	  | Error -> ti.s_coq_error <- ti.s_coq_error + 1;
	      ti.s_coq_errors <- d.d_file_name :: ti.s_coq_errors 
	  | Timeout -> ti.s_coq_timeout <- ti.s_coq_timeout + 1;
	      ti.s_coq_timeouts <- d.d_file_name :: ti.s_coq_timeouts
      end else ti.s_v_errors <- d.d_file_name :: ti.s_v_errors
    end else ti.s_prf_errors <- d.d_file_name :: ti.s_prf_errors
  in
    ti.s_nb <- ti.s_nb + 1;
    ti.s_prover_time <- ti.s_prover_time +. d.d_prover_time;
    begin match d.d_prover_result with
      | Yes -> ti.s_prover_yes <- ti.s_prover_yes + 1;
	  ti.s_prover_yes_time <- ti.s_prover_yes_time +. d.d_prover_time;
	  aux ()
      | No -> ti.s_prover_no <- ti.s_prover_no + 1;
	  ti.s_prover_no_time <- ti.s_prover_no_time +. d.d_prover_time;
	  aux ()
      | Maybe -> ti.s_prover_maybe <- ti.s_prover_maybe + 1
      | Killed -> ti.s_prover_killed <- ti.s_prover_killed + 1
      | Anomaly -> ti.s_prover_error <- ti.s_prover_error + 1;
	  ti.s_prover_errors <- d.d_file_name :: ti.s_prover_errors
    end;
    t.(i) <- ti;;

let compute_total () =
  let s = t.(n-1) in
  for i = 0 to n-2 do
    let ti = t.(i) in
    if ti.s_nb <> 0 then begin
      s.s_nb <- s.s_nb + ti.s_nb;
      s.s_prover_time <- s.s_prover_time +. ti.s_prover_time;
      s.s_prover_yes <- s.s_prover_yes + ti.s_prover_yes;
      s.s_prover_yes_time <- s.s_prover_yes_time +. ti.s_prover_yes_time;
      s.s_prover_maybe <- s.s_prover_maybe + ti.s_prover_maybe;
      s.s_prover_no <- s.s_prover_no + ti.s_prover_no;
      s.s_prover_no_time <- s.s_prover_no_time +. ti.s_prover_no_time;
      s.s_prover_killed <- s.s_prover_killed + ti.s_prover_killed;
      s.s_prover_error <- s.s_prover_error + ti.s_prover_error;
      s.s_prf <- s.s_prf + ti.s_prf;
      s.s_v <- s.s_v + ti.s_v;
      s.s_coq_ok <- s.s_coq_ok + ti.s_coq_ok;
      s.s_coq_error <- s.s_coq_error + ti.s_coq_error;
      s.s_coq_timeout <- s.s_coq_timeout + ti.s_coq_timeout;
      s.s_coq_yes_time <- s.s_coq_yes_time +. ti.s_coq_yes_time;
      s.s_coq_no_time <- s.s_coq_no_time +. ti.s_coq_no_time;
      s.s_coq_time <- s.s_coq_time +. ti.s_coq_time;
    end
  done;;

(*****************************************************************************)
(* compute and print stats from a log file *)
(*****************************************************************************)

let string_of_sort = function
  | Term -> "Trs"
  | String -> "Srs";;

let string_of_kind = function
  | Std -> "Standard"
  | Rel -> "Relative"
  | AC -> "Modulo AC";;

let string_of_strat = function
  | Full -> "Full"
  | In -> "Innermost"
  | Out -> "Outermost"
  | CS -> "Context sensitive";;

let string_of_stat p k s =
  string_of_sort (sort_of_int p)
  ^ " " ^ string_of_kind (kind_of_int k)
  ^ " " ^ string_of_strat (strat_of_int s);;

let cat_nb () =
  let aux k s = if s.s_nb <> 0 then k+1 else k in
    Array.fold_left aux 0 t - 1;;

let print_stats () =
  for p = 0 to 1 do
    for k = 0 to 2 do
      for s = 0 to 3 do
	let i = index p k s in
	  if t.(i).s_nb <> 0 then begin
	    print_endline "-------------------------------------------------";
	    print_endline ("Category: " ^ string_of_stat p k s);
	    print_stat t.(i);
	  end
      done
    done
  done;
  if cat_nb () > 1 then begin
    print_endline "-------------------------------------------------";
    print_endline "All categories";
    print_stat t.(n-1)
  end;;
