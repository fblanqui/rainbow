(**************************************************************************)
(* Small program to test the equivalences class *)

open List;;
open Printf;;

(**************************************************************************)
(* Data information for test *)
(**************************************************************************)

let defined = ["name"; "symbol"; "label"]

let undefined = ["string"]

let len_undefined = length undefined

(* connection *)

let entries = [ ("name" , ["string"] );
		("symbol" , ["label"] );
		("label" , ["symbol"] ) ]

(**************************************************************************)
(* Function return a position taking a list and return a position of
   its. This is a polymorphic function. *)
(**************************************************************************)

let rec position (x: 'a) : 'a list -> int = function
  | [] -> raise Not_found
  | y :: xs ->
    if x = y then 0
    else 1 + position x xs

(* Compute the transitive closure of a square matrix *)

let transClosure (m: 'a array array) : 'a array array =
  let n = Array.length m in
  for k = 0 to n - 1 do
    let mk = m.(k) in
    for i = 0 to n - 1 do
      let mi = m.(i) in
      for j = 0 to n - 1 do
	mi.(j) <- max mi.(j) (min mi.(k) mk.(j))
      done;
    done;
  done;
  m

(* Compute a equivalent class of a square matrix *)

let eq_class (m: bool array array) (i: int) : int list =
  let column = m.(i) and
      set = ref [] in
  Array.iteri
    begin fun j l ->
      if j = i || column.(j) && m.(j).(i) then
	set := j :: !set
      else ignore l
    end column;
  !set

(* Compute an equivalence class from boolean matrix *)

let eq_classes (m: bool array array) : int list list =
  let set = ref [] in
  Array.iteri
    begin fun e _ ->
      if not (exists (mem e) !set) then
	set := eq_class m e :: !set
    end m;
  !set
      
(* Define a function to compare a list list *)

let cmp_set (m: bool array array) (c: int list) (c': int list) : int =
  if c = c' then 0
  else
    match c, c' with
      | i :: _, j :: _ ->
	if m.(i).(j) then 1 else -1
      | _ -> assert false

(* Define a function sort the list *)

let sort_set (m: bool array array) : int list list -> int list list =
  sort (cmp_set m)

(* Define a function return a value of its position *)

let num_of_name (defined: 'a list) (undefined: 'a list) (len_undefined: int) (s:'a)
    : int option =
  try let p = position s defined in
      Some (p + len_undefined)
  with Not_found ->
    try let p = position s undefined in
	Some p
    with Not_found -> None

(**************************************************************************)
(* Compute a matrix *)

let matrix : bool array array =
  let len = length defined + len_undefined in
  let boolmat = Array.make_matrix len len false in
  iter (fun (s, strs) ->
    match num_of_name defined undefined len_undefined s with
      | Some pos1 -> iter (fun t ->
	match num_of_name defined undefined len_undefined t with
	  | Some pos2 -> boolmat.(pos1).(pos2) <- true
	  | None -> ()) strs
      | None -> ()
  ) entries;
  boolmat;;

(**************************************************************************)
(* Print function *)
(**************************************************************************)

(* Define a function print a matrix *)

let print_mat (m: bool array array): unit =
  for i = 0 to Array.length m - 1 do
    for j = 0 to Array.length m.(0) - 1 do
      print_string "Print a matrix: \n";
      print_string (string_of_bool m.(i).(j));
      printf " ";
    done;
    printf " \n"; (* print new row) *)
  done

(* Define a print function of entries, print each type as [->] *)

let defn_of_entries (x: string) : string =
  try let (_, xs) = find (fun (y, ys) -> y = x) entries in
      String.concat "->" xs
  with Not_found -> ""

(* Print function in the case of Definition *)

let print_one_function (x: string) : unit =
  printf "\nDefinition %s := %s." x (defn_of_entries x)

(* Main function print *)

let print_xsd_list (xs: string list) : unit =
  match xs with
    | [] -> ()
    | [x] -> print_one_function x
    | _ ->
      let ys = String.concat "\nwith "
	(map (fun x ->
	  sprintf "%s := %s" x (defn_of_entries x)) xs) in
      printf "\nInductive %s." ys

(**************************************************************************)
(* Compute with real data and print *)
(**************************************************************************)

(* compute the transitive closure matrix *)

let sort_eq = sort_set (transClosure matrix) (eq_classes (transClosure matrix))

(* Convert an int list list to string list list *)

let name_of_num (xsds: 'a list) (undefined: 'a list) (len_undefined: int) (k: int) : 'a =
  if k < len_undefined then
    List.nth undefined k else
    List.nth xsds (k - len_undefined)

let string_of_int : int list list -> string list list =
  map (map (name_of_num defined undefined len_undefined))

let sort_eq_string : string list list = string_of_int sort_eq

(* remove undefine in the sorted equivalence class *)

let newordered : string list list =
  filter (function 
    | [x] -> for_all ((<>) x) undefined
    | _ -> true) sort_eq_string

(* Main function to print matrix with data *)

let print_matrix_data =
  iter (fun eq -> print_xsd_list eq) newordered






    
























(* FIXME: old code *)

(**************************************************************************)
(* small example *)
(*
let entries = [("name", ["string"]);
	       ("label", ["symbol"]);
	       ("symbol", ["label"])
              ]

let undefined = ["string"]

let defined = ["name"; "label"; "symbol"]


(* example with connect to one element *)
(*
let entries = [("a", ["b"]);
	       ("b", ["a"]);
	       ("e", ["a"; "b"; "c"; "d"]);
	       ("c", ["d"]);
	       ("d", ["c"]);
              ]

let undefined = [""]
  *)

(* example with another way *)
(*

let defined = ["a"; "b"; "c"; "d"; "e"]

let entries = [("a", ["b"]);
	       ("b", ["a"]);
	       ("c", ["e"]);
	       ("d", ["e"]);
	       ("e", ["a"]);
	      ]*)
 

(***************************************************************************)
(*
let entries = [("1", ["2"]);
	       ("5", ["6"; "7"]);
	       ("3", ["2"]);
	       ("6", ["3"; "7"]);
	       ("8", ["7"]);
	       ("4", ["3"; "1"])
	      ]
	       
let defined = ["2"; "3"; "4"; "5"; "6"; "7"; "8"]
let undefined = ["1"]
*)

(****************************************************************************)
(*example 1 *)
(*
let entries = [
 ("input", ["dpsInput"; "trsInput"; "order"]);
  ("dpInput", ["trs"; "dps"; "strategy"]);
  ("trsInput", ["trs"; "strategy"; "rules"]);
  ("trs", ["rules"]);
  ("dps", ["rules"]);
  ("order", ["mono"; "arg"; "rule"]);
  ("rules", ["rule"]);
  ("rule", ["term"]);
  ("term", ["var"; "symbol"]);
  ("symbol", ["name"; "label"]);
  ("label", ["symbol"]);
  ("arg", ["arity"; "symbol"; "t3"])
]

let undefined = [""]

let defined =
  ["input"; "dpInput"; "trsInput"; "order"; "trs"; "dps"; "strategy"; "rules";
   "mono"; "arg"; "rule"; "term"; "var"; "symbol"; "label"; "name"; "arity"
   ; "t3"]*)

(**********************************************************************)
(* Test a part of xsds 1 *)

(*
let entries = 
[ ("label", ["nonNegativeInteger"; "symbol"]);
("symbol", ["name"; "symbol"; "symbol"; "label"]); 
("coefficient",["number"; "minusInfinity"; "plusInfinity"; "vector"; "matrix"]);
("vector", ["coefficient"]); ("matrix", ["vector"])]

let defined = [ "label"; "symbol"; "coefficient"; "vector"; 
	       "matrix"]

let undefined = [ "nonNegativeInteger"; "minusInfinity"; "plusInfinity"]*)


(**********************************************************************)
(*example 3*)
(*
let entries = 
[("label", ["nonNegativeInteger"; "symbol"]);
("symbol", ["name"; "symbol"; "symbol"; "label"])]

let defined = ["label"; "symbol"]
let undefined = [""] *)


(*****************************************************************************)
(* Test the entries xsds *)
(* FIXME: this example is not return an correct order *)
(*let entries = 
[("name", ["string"]); ("label", ["nonNegativeInteger"; "symbol"]);
   ("symbol", ["name"; "symbol"; "symbol"; "label"]); ("var", ["string"]);
   ("term", ["var"; "symbol"; "term"]); ("rule", ["term"; "term"]);
   ("rules", ["rule"]); ("dps", ["rules"]); ("trs", ["rules"]);
   ("usableRules", ["rules"]);
   ("number", ["integer"; "integer"; "positiveInteger"]);
   ("coefficient",
    ["number"; "minusInfinity"; "plusInfinity"; "vector"; "matrix"]);
   ("vector", ["coefficient"]); ("matrix", ["vector"]);
   ("polynomial",
    ["coefficient"; "positiveInteger"; "polynomial"; "polynomial";
     "polynomial"; "polynomial"]);
   ("function", ["polynomial"]); ("arity", ["nonNegativeInteger"]);
   ("dimension", ["positiveInteger"]);
   ("strictDimension", ["positiveInteger"]);
   ("degree", ["nonNegativeInteger"]); ("position", ["positiveInteger"]);
   ("argumentFilter", ["symbol"; "arity"; "t3"]);
   ("t3", ["positiveInteger"; "position"]);
   ("domain",
    ["naturals"; "integers"; "number"; "domain"; "domain"; "dimension";
     "strictDimension"; "domain"]);
   ("redPair",
    ["cpf_type"; "symbol"; "arity"; "function"; "symbol"; "arity";
     "nonNegativeInteger"; "t2"; "argumentFilter"]);
   ("cpf_type",
    ["domain"; "degree"; "domain"; "dimension"; "strictDimension"]);
   ("t2", ["lex"; "mul"]);
   ("arithFunction",
    ["nonNegativeInteger"; "positiveInteger"; "arithFunction";
     "arithFunction"; "arithFunction"; "arithFunction"]);
   ("model",
    ["positiveInteger"; "tupleOrder"; "symbol"; "arity"; "arithFunction";
     "labeling"; "rootLabeling"]);
   ("tupleOrder", ["pointWise"]);
   ("dpProof",
    ["pIsEmpty"; "dps"; "boolean"; "positiveInteger"; "dpProof";
     "orderingConstraints"; "orderingConstraintProof"; "dps"; "dpProof";
     "orderingConstraints"; "orderingConstraintProof"; "dps"; "usableRules";
     "dpProof"; "orderingConstraints"; "orderingConstraintProof"; "dps";
     "trs"; "dpProof"; "orderingConstraints"; "orderingConstraintProof";
     "dps"; "trs"; "usableRules"; "dpProof"; "argumentFilter"; "rule";
     "rewriteSequence"; "dps"; "dpProof"; "model"; "dps"; "trs"; "dpProof";
     "dps"; "trs"; "dpProof"; "t1"; "rule"; "nonNegativeInteger"; "boolean";
     "nonNegativeInteger"; "symbol"; "context"; "dps"; "trs"; "dpProof";
     "argumentFilter"; "dps"; "trs"; "dpProof"; "dpInput"]);
   ("t1",
    ["subtermCriterion"; "orderingConstraints"; "orderingConstraintProof";
     "usableRules"]);
   ("substitution", ["var"; "term"]);
   ("context", ["box"; "symbol"; "term"; "context"; "term"]);
   ("rewriteSequence", ["term"; "position"; "rule"; "relative"; "term"]);
   ("trsTerminationProof",
    ["rIsEmpty"; "orderingConstraints"; "orderingConstraintProof"; "trs";
     "trsTerminationProof"; "dps"; "boolean"; "dpProof"; "model"; "trs";
     "trsTerminationProof"; "trs"; "trsTerminationProof"; "trs";
     "trsTerminationProof"; "context"; "trs"; "trsTerminationProof";
     "trsInput"]);
   ("loop", ["rewriteSequence"; "substitution"; "context"]);
   ("trsNonterminationProof",
    ["variableConditionViolated"; "trs"; "trsNonterminationProof"; "trs";
     "trsNonterminationProof"; "loop"; "dps"; "boolean";
     "dpNonterminationProof"; "trsInput"]);
   ("relativeTerminationProof",
    ["rIsEmpty"; "trsTerminationProof"; "orderingConstraints";
     "orderingConstraintProof"; "trs"; "trs"; "relativeTerminationProof";
     "model"; "trs"; "trs"; "relativeTerminationProof"; "trs"; "trs";
     "relativeTerminationProof"; "trs"; "trs"; "relativeTerminationProof";
     "trsInput"]);
   ("dpNonterminationProof",
    ["loop"; "dps"; "trs"; "dpNonterminationProof"; "dpInput"]);
   ("relativeNonterminationProof",
    ["loop"; "trsNonterminationProof"; "variableConditionViolated"; "trs";
     "trs"; "relativeNonterminationProof"; "trsInput"]);
   ("orderingConstraints",
    ["boolean"; "boolean"; "monotonePositions"; "argumentFilter"; "rule"]);
   ("monotonePositions", ["argumentFilter"; "everySymbolAndPosition"]);
   ("orderingConstraintProof", ["redPair"; "orderingConstraints"]);
   ("proof",
    ["trsTerminationProof"; "trsNonterminationProof";
     "relativeTerminationProof"; "relativeNonterminationProof"; "dpProof";
     "dpNonterminationProof"; "orderingConstraintProof"]);
   ("url", ["string"]); ("trsInput", ["trs"; "strategy"; "rules"; "rules"]);
   ("dpInput", ["trs"; "dps"; "strategy"; "boolean"]);
   ("strategy", ["innermost"]);
   ("certificationProblem",
    ["input"; "string"; "proof"; "string"; "string"; "string"; "url";
     "string"; "string"; "url"; "tpdb-reference"; "string"]);
   ("input", ["trsInput"; "dpInput"; "orderingConstraints"])]

let defined =
["name"; "label"; "symbol"; "var"; "term"; "rule"; "rules"; "dps"; "trs"; 
   "usableRules"; "number"; "coefficient"; "vector"; "matrix"; "polynomial"; 
   "function"; "arity"; "dimension"; "strictDimension"; "degree"; "position"; 
   "argumentFilter"; "t1"; "domain"; "redPair"; "cpf_type"; "t2"; 
   "arithFunction"; "model"; "tupleOrder"; "dpProof"; "t3"; "substitution"; 
   "context"; "rewriteSequence"; "trsTerminationProof"; "loop"; 
   "trsNonterminationProof"; "relativeTerminationProof"; 
   "dpNonterminationProof"; "relativeNonterminationProof"; 
   "orderingConstraints"; "monotonePositions"; "orderingConstraintProof"; 
   "proof"; "url"; "trsInput"; "dpInput"; "strategy"; "certificationProblem"; 
   "input"]

let undefined = ["string"; "nonNegativeInteger"; "integer"; "positiveInteger";
		"boolean"
		]
*)
(*****************************************************************************)
(* main program *)

let rec position x = function
| [] -> raise Not_found
| y :: ys -> if x = y then 0 else 1 + position x ys

let len_undefined = List.length undefined 

(* funtion taking an xsds list and undefined list, return a position of xsds
   list *)

let num_of_name defined undefined len_undefined s =
  try let p = position s defined in  Some (p + len_undefined)
  with Not_found -> 
    try let p = position s undefined in Some p
    with Not_found -> None
(*
let num_of_name defined s =
  try let p = position s defined in Some p
  with Not_found -> None*)

(* funtion taking a position of xsds list and undefined list, return
   their element *)
(*
let name_of_num xsds _un len_undefined k =
  if k < len_undefined then List.nth undefined k else
    List.nth xsds (k - len_undefined) *)

let name_of_num xsds k = List.nth xsds k;;

(*
let matrix =
  let len = List.length defined in
  let boolmat = Array.make_matrix len len false in
  List.iter (fun (s, strs) ->
    match num_of_name defined s with
      | Some pos1 -> List.iter (fun t ->
        match num_of_name defined t with
          | Some pos2 -> boolmat.(pos1).(pos2) <- true
          | None -> ()) strs
      | None -> ()
  ) entries;
  boolmat*)

(* transform from xsds to boolean matrix *)

let matrix =
  let len = List.length defined + len_undefined in
  let boolmat = Array.make_matrix len len false in
  List.iter (fun (s, strs) ->
    match num_of_name defined undefined len_undefined s with
      | Some pos1 -> List.iter (fun t ->
        match num_of_name defined undefined len_undefined t with
          | Some pos2 -> boolmat.(pos1).(pos2) <- true
          | None -> ()) strs
      | None -> ()
  ) entries;
  boolmat

(* computing transitive closure of the matrix *)
let transClosure m =
  let n = Array.length m in
  for k = 0 to n - 1 do
    let mk = m.(k) in
    for i = 0 to n - 1 do
      let mi = m.(i) in
      for j = 0 to n - 1 do
	mi.(j) <- max mi.(j) (min mi.(k) mk.(j))
      done;
    done;
  done;
  m;;

(* An equivalence class is a set of elements that are all
   equivalent. We intended to instead iterate over all entries in the
   matrix column; compute an equivalence class with relations
   reflexive and check both directions *)

let eq_class m i =
  let column = m.(i)
  and set = ref [] in
  Array.iteri begin fun j _ ->
    if j = i || column.(j) && m.(j).(i) then
      set := j :: !set
  end column;
  !set;;

(* this function returns all the equivalence classes as a list of
   lists, each equivalence class being an individual list *)

let eq_classes m =
  let classes = ref [] in
  Array.iteri begin fun e _ ->
    if not (List.exists (List.mem e) !classes) then
      classes := eq_class m e :: !classes
  end m;
  !classes;;

(* define function print list of list *)
let rec my_iter f = function
  | [] -> ()
  | a :: l -> f a; print_string " "; my_iter f l;;
  
(* let print eq_classes *)

let print_eq_classes =
  print_string "eq_classes:\n"; eq_classes matrix;;

(* change connection in boolean matrix: if in the case (false, false) -> (true, false) *)
 let rec linearize m =
    let b = ref true
    and n = Array.length m in
    for i = 0 to n - 1 do
      let mi = m.(i) in
      for j = 0 to n - 1 do
	if not (mi.(j) || m.(j).(i)) then
	  (mi.(j) <- true; b := false)
      done;
    done;
    if !b then m else linearize (transClosure m)

(* print matrix *)

let print_mat m =
  for i = 0 to Array.length m - 1 do
    for j = 0 to Array.length m.(0) - 1 do
      print_string (string_of_bool m.(i).(j));
      Printf.printf " ";
    done;
    Printf.printf " \n";
  done;
;;

let print_matrix = print_mat matrix; print_newline();;

let print_linearzie = print_mat (linearize matrix);;

let cmp_classes_int m i j =
  match m.(i).(j), m.(j).(i) with
    (* same class: there is a path between i and j, and between j and i *)
    | true, true -> 0
    (* there is a path between i and j *)
    | true, false -> 1
    (* there is a path between j and i *)
    | false, true  -> -1 
    (* i and j are not compareable *)
    | false, false -> assert false

let sort_eq_classes_int m = List.sort (cmp_classes_int m);;

let sort_eq_classes_int_m = sort_eq_classes_int matrix;;

(*let print_sorted = print_string "\n\nSort_eq_classes_int";
  my_iter print_int (sort_eq_classes_int_m;;*)

let print_matrix = print_mat matrix;;

(* Compute and ordering *)

let tc = transClosure matrix;;

let print_tc = print_string "\nTC\n";
  print_mat tc;;

let line = linearize tc;;

let print_line = print_string "\nLINE\n";
  print_mat line;;

let eq = eq_classes line;; (* DEBUG *)

let eq' = eq_classes matrix;;

let print_eq = print_string "\nEQ\n"; my_iter print_int (List.flatten eq);;

let print_eq' = print_string "\nEQ'\n"; my_iter print_int (List.flatten eq');;


(* REMARK for debug use: sudo ocamldebug a.out (a.out generate by:
   sudo ocamlc draft.ml then ocamlrun a.out to execute it.
   br@draft line then 'r'
*)

(* Here is the output in ocaml debug:

   sort_eq_int : int list =
  [18; 17; 16; 15; 14; 13; 12; 11; 10; 9; 8; 7; 6; 5; 4; 3; 2; 1; 0]

   p sort_eq_string

   sort_eq_string : string list list =
  [["t3"; "arity"; "name"; "label"; "symbol"; "var"; "term"; "rule"; "arg";
    "mono"; "rules"; "strategy"; "dps"; "trs"; "order"; "trsInput";
    "dpInput"; "input"; ""]]

   newordered : string list list =
   [["t3"; "arity"; "name"; "label"; "symbol"; "var"; "term"; "rule"; "arg";
   "mono"; "rules"; "strategy"; "dps"; "trs"; "order"; "trsInput";
   "dpInput"; "input"; ""]]
*)

let sort_eq_int = sort_eq_classes_int line (List.flatten eq);;

let sort_eq_int' = sort_eq_classes_int matrix (List.flatten eq');;

let print_sort_eq_int = print_string "\nSort_eq_int\n";
  my_iter print_int sort_eq_int;;

let print_sort_eq_int' = print_string "\nSort_eq_int'\n";
  my_iter print_int sort_eq_int';;

(*let string_of_int =
  List.map(List.map (name_of_num defined defined len_undefined));;*)

let string_of_int =
  List.map(List.map (name_of_num defined));;

let sort_eq_string = string_of_int [sort_eq_int'];; (* DEBUG *)

let print_sort_eq_string = print_string "\nSORT_EQ_STRING\n";
  my_iter print_string (List.flatten sort_eq_string);;

(* remove all elements of undefined on the sorted equivalence classes*)

(*let newordered = List.filter (function  (* DEBUG *)
  | [x] -> List.for_all ((<>) x) undefined
  | _ -> true) sort_eq_string *)

let newordered = List.filter (function  (* DEBUG *)
  | [x] -> List.for_all ((<>) x) (List.flatten sort_eq_string)
  | _ -> true) sort_eq_string


let print_newordered = print_string "\n new_ordered\n";
  my_iter print_string (List.flatten newordered);;

(************************************************************)
(*return the right hand side of a list pair string * string list *)

let defn_of label =
    try
       let (_, xs) = List.find (fun (l, ys) -> l = label) entries in
       String.concat "->" xs
    with
        Not_found -> "";;

(*******************************************)
(* print coq type *)

let print_defined x = 
  Printf.printf "\nDefinition %s := %s." x (defn_of x)

let print_defined_equivalence xs =
  match xs with
    | [] -> ()
    | [x] -> print_defined x
    | _ ->
      let ys = String.concat "\nwith " 
	(List.map (fun x -> 
	  Printf.sprintf "%s := %s" x (defn_of x)) 
	   xs) in
      Printf.printf "\nInductive %s." ys

let print =
List.iter (fun eqvclass -> print_defined_equivalence eqvclass)
  newordered

let rec sort lst =
   match lst with
     [] -> []
   | head :: tail -> insert head (sort tail)
 and insert elt lst =
   match lst with
     [] -> [elt]
   | head :: tail -> if elt <= head then elt :: lst else head :: insert elt tail;;


let print_sort = my_iter print_int (sort [ 1 ; 3 ; 9 ; 2 ; 5 ; 4; 4; 8 ; 4 ]) ;;
*)
