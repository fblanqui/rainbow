(******************************************************************************
Author: Frederic Blanqui
Date: 2 May 2003
Copyright: INRIA (http://www.inria.fr)
Licence: CeCILL v2 (http://www.cecill.info)

usage: order_deps name1 name2 ...

read from stdin a set of dependencies in "make" format, that is,
lines of the form:

   name1: name2 ... namek (with k >= 0)

print on stdout all dependencies for name1 name2 ...
in compilation order (from the less dependent to the most dependent)

detect cycles
******************************************************************************)

let pr_name s = print_string (s ^ " ");;

module StrSet = Set.Make(String);;

let add set s = StrSet.add s set;;

(*DEBUG:
let pr_set = StrSet.iter pr_name;;

let pr_depth = function
  | Some d -> print_int d
  | None -> print_string "?";;

let pr_elt s (dopt, set) =
  pr_depth dopt; print_string " "; pr_name s; pr_set set; print_newline();;

let pr_tbl tbl = print_endline "table:"; Hashtbl.iter pr_elt tbl;;*)

let get_line () =
  let res = ref "" in
    try
      while !res = "" do res := read_line() done;
      while Str.last_chars !res 1 = "\\" do
	!res.[String.length !res - 1] <- ' ';
	res := !res ^ (read_line())
      done; !res
    with End_of_file ->
      if !res = "" then raise End_of_file else !res;;

let depth tbl s =
  try fst (Hashtbl.find tbl s) with Not_found -> Some 0;;

let dependancies tbl s =
  try snd (Hashtbl.find tbl s) with Not_found -> StrSet.empty;;

let build_table () =
  let tbl = Hashtbl.create 117 in
    try
      while true do
	let s = get_line () in
	  try begin
	    match Str.split (Str.regexp "[ :\t]+") s with
	      | s :: l ->
		  let set = List.fold_left add (dependancies tbl s) l in
		    Hashtbl.replace tbl s (None, StrSet.remove s set)
	      | _ -> () end
	  with Not_found -> ()
      done; tbl
    with End_of_file -> tbl;;

exception No_max;;

let find_max tbl set =
  let v = ref 0 in
  let compute_max s =
    match depth tbl s with
      | Some d -> if d > !v then v:=d
      | _ -> raise No_max in
    try StrSet.iter compute_max set; Some (!v+1)
    with No_max -> None;;

let compare_depth tbl s1 s2 =
  match depth tbl s1, depth tbl s2 with
    | Some d1, Some d2 -> Pervasives.compare d1 d2
    | None, _ -> 1
    | _ -> -1;;

let concat_deps tbl =
  let add_deps s set = StrSet.add s (StrSet.union (dependancies tbl s) set) in
  fun set -> StrSet.fold add_deps set StrSet.empty;;

let compute_depth tbl s = function
  | None, set ->
      begin match find_max tbl set with
	| Some _ as dopt -> Hashtbl.replace tbl s (dopt, concat_deps tbl set)
	| _ -> () end
  | _ -> ();;

let none_number tbl =
  let n = ref 0 in
  let check _ = function
    | None, _ -> incr n
    | _ -> ()
  in Hashtbl.iter check tbl; !n;;

let none_number_decrease tbl n =
  let n' = none_number tbl in
    if n' < !n then (n := n'; true) else false;;

let main () =
  if Array.length Sys.argv < 2 then
    (prerr_endline ("usage: " ^ Sys.argv.(0) ^ " filename ..."); exit 1);
  let tbl = build_table ()
  and args = StrSet.remove Sys.argv.(0)
	       (Array.fold_right StrSet.add Sys.argv StrSet.empty) in
  let files = ref args and n = ref (none_number tbl) in
    Hashtbl.iter (compute_depth tbl) tbl;
    while not (StrSet.is_empty !files) & none_number_decrease tbl n do
      files := StrSet.filter (fun s -> depth tbl s = None) !files;
      Hashtbl.iter (compute_depth tbl) tbl;
    done;
    if not (StrSet.is_empty !files) then
      (prerr_endline "error: cyclic dependencies!"; exit 1);
    let l = StrSet.elements (concat_deps tbl args) in
    let l = List.sort (compare_depth tbl) l in
      List.iter pr_name l; print_newline();;

let _ = main();;
