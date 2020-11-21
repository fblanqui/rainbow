(************************************************************************)
(* Author: Ly Kim Quyen
 * Date: 18 Oct 2011
 * Topological sort and transitive closure
 *)

(* Topological sort *)

(* Given a directed graph G (V, E), topological sort find an ordering of
 * vertices in a directed acyclic (no directed cycle) graph, so that if 
 * edge u -> v then v precedes u in ordering.
 * 
 * Graph represented as a pair of list 
 *  (vertex, list of vertices they depend on/edges)
 *
 * For example:
 * input a graph: a -> b; a -> c;
 * output the ordering: c b a or b c a
 * An exception will raise when the graph un-orderable;
 * for example the graph above 'a' occurs in the list of dependeces on 'c': 
 * input : a -> b -> c;  c -> a -> d
 * output : raise an exception 'un-orderable data'
 *)

open List
open Printf

(* remove an seft dependency from a graph *)
let remove_self graph =
  let f (vertex, edges) = (vertex, filter (fun v -> v <> vertex) edges) in 
  map f graph

(* The function rev_unique returns a reverse unique vertices in a list of
   vertices *)
let rev_unique : 'a list -> 'a list =
  fold_left (fun acc v -> if mem v acc then acc else v::acc) []

(* list vertices, each being unique *)
let vertices graph : 'a list =
  rev_unique (flatten(map (fun (vertex, edges) -> vertex::edges)graph))

(* The function returns of the vertex in a graph.
   If the vertex does not exists, a Not_found exception is raise *)
let get_edges (vertex: 'a) graph: 'a list = 
  try (assoc vertex graph)
  with Not_found -> []

(* topological sort *)
let topo graph =
  let rec explore acc path start_vertex edges =
  match start_vertex, path with
    | [], [] -> rev acc
    | [], _ ->
      if edges
      then explore acc [] path false
      else invalid_arg "un-orderable data"
    | v :: vs, _ ->
      let vertices = get_edges v in
      let visited =
	for_all (fun vertex -> mem vertex acc) (vertices graph)
      in
      if visited
      then explore (v :: acc) path vs true
      else explore acc (v :: path) vs edges
  in
  (* return a list of start vertex, vertices don't have any dependent *)
  let starts, start_vertex =
    partition (fun vertex -> get_edges vertex graph = [])(vertices graph)
  in explore starts [] start_vertex false
;;


(* Test *)
let graph_0 = [
  ("a", ["b"; "c"]);
  ]

(* un-orderable data *)
let graph_1 = [
  ("a", ["b"; "c"]);
  ("c", ["b"; "d"]);
  ]

(* graph of graph_2 *)
(* a     b
   |  \  |
   v   v v
   c --> d
   |
   v
   e <- f
    \   |
     \  v
      \ g
       \|
        v
        h
*)

let graph_2 = [
  ("a", ["c"; "d"]);
  ("b", ["d"]);
  ("c", ["d"; "e"]);
  ("e", ["h"]);
  ("f", ["e"; "g"]);
  ("g", ["h"]);
  ("h", []);
]

(* Graph of graph_3 *)
(*
  a --> b --> d --> h --> k --> m
  |     |                 ^     ^
  v     v                 |     |
  c     e --> i-----------|     |
  |\    |                       |
  v v   v                       |
  g  f->j                       |
  \    /                        | 
   v v                          |
    l --------------------------|
*)
let graph_3 = [
  ("a", ["b"; "c"]);
  ("b", ["d"; "e"]);
  ("c", ["f"; "g"]);
  ("d", ["h"]);
  ("e", ["i"; "j"]);
  ("f", ["j"]);
  ("g", ["l"]);
  ("h", ["k"]);
  ("i", ["k"]);
  ("j", ["l"]);
  ("k", ["m"]);
  ("l", ["m"]);
]

(* graph 4 *)
let graph_4 = [
  ("a", ["b"; "d"]);
  ("b", ["c"; "d"; "e"]);
  ("c", ["d"]);
  ("d", []);
  ("e", ["e"]);
  ("f", ["c"; "e"]);
]

(* main *)

let topo oc g = fprintf oc "%s" (String.concat ", " (topo (remove_self g)));;

let () =
  fprintf stdout "\
********************\n\
Topological Sort \n\
********************\n\
Result graph 0: \n\
%a\n\
Result graph 1: \n\
%a\n\
Result graph 2: \n\
%a\n\
Result graph 3: \n\
%a\n\
Result graph 4: \n\
%a\n" topo graph_0 topo graph_1 topo graph_2 topo graph_3 topo graph_4;;

(******************************************************************************)
(* Convert *)

open Array

let to_list (m: 'a array array) : 'a list list =
  List.map to_list (to_list m);;

let array_list_map (l: 'a list list) : 'a array array =
  Array.map Array.of_list (Array.of_list l);;

let list_of_list_array la = Array.to_list (Array.map Array.of_list la);;

let list_to_list_array al = Array.of_list (List.map Array.to_list al);;

(* Iterators on list of arrays. *)

let maplist f al = Array.map f (list_to_list_array al);;

(* convert list of array to array of arrays *)
let of_arraylist = function
   | [] -> [||]
   | a :: _ as al ->
     let ni = Array.length a in
     List.iter
       (fun b ->
         if Array.length b <> ni then invalid_arg "Umatrix.of_arraylist")
       al;
     Array.of_list al;;
 
(******************************************************************************
 * Transitive Closure - Strongly Connected Component - Topological ordering *)

(* Consider a directed graph G (V,E), The transitive closure of TC(G) of a graph
 * is a graph which contains an edge (i,j) whenever there is a directed path
 * from i to j.
 * The program calculates transitive closure of relation represented as an
 * adjacency matrix. Element (i,j) in the matrix is equal to true
 * if the pair (i,j) is in the relation. Otherwise, it is equal to false.
 * *)

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
m

(* A directed graph is called strongly connected if there is a path
   from each vertex in the graph to every other vertex. In particular,
   this means paths in each direction; a path from a to b and also a
   path from b to a.  The strongly connected components of a directed
   graph G are its maximal strongly connected subgraphs.
*)

let scc m =
  let n = Array.length m in
  let result = Array.make_matrix n n 0 in
  for i = 0 to n - 1 do
    let mi = m.(i)
    and result_i = result.(i) in
    for j = 0 to n - 1 do
      result_i.(j) <- min mi.(j) m.(j).(i)
    done;
  done;
  result

(* Collect the results in a list of lists, avoid generating multiple
   times the same component. Output the topological order list of
   lists from matrix *)

let topo_order (m: 'a array array) : int list list =
  let n = Array.length m in
  let marked = Array.make n false in
  let result = ref [] in
  for i = 0 to n - 1 do
    let mi = m.(i) in
    if (not marked.(i)) then
      begin
	let component = ref[i] in
	for j = i + 1 to n - 1 do
	  if mi.(j) = true && m.(j).(i) = true then
		begin
		  marked.(j) <- true;
		  component := j :: !component
		end
	done;
	result := !component :: !result
      end
  done;
  !result ;;

(* print matrix *)
let print_mat s m : unit =
  print_string s;
  for i = 0 to length m - 1 do
    for j = 0 to length m.(0) - 1 do
      print_string (string_of_bool m.(i).(j));
      printf " ";
    done;
    printf " \n";
  done;
;;

(* TODO: write the function read the matrix to graph *)

(******************************************************************************)
(* test *)

let matrix_test_0 = [|
  [|false; true; true|];
  [|true; false; false|];
  [|false; false; false|];
   |];;

let matrix_test_1 = [|
  [|false; true; false; false|];
  [|false; false; true; false|];
  [|false; false; false; true|];
  [|false; false; false; false|];
  |];;

let matrix_test_2 = [|
  [|false; false; false; true; false|];
  [|false; false; false; true; false|];
  [|false; true; false; false; false|];
  [|false; false; false; false; true|];
  [|false; true; false; false; false|];
  |];;

let matrix_test_3 = [|
  [|false; true; true|];
  [|false; false; true|];
  [|true; true; false|];
  |];;

let matrix_test_4 = [|
  [|false; true; false; true|];
  [|false; false; false; false|];
  [|true; false; false; false|];
  [|false; false; false; false|];
   |];;

let matrix_test_5 = [|
  [|false; true; false; true; false; false|];
  [|true; false; true; false; false; false|];
  [|false; true; false; false; true; true|];
  [|false; false; false; false; false; false|];
  [|false; false; false; false; false; false|];
  [|false; false; true; false; false; false|];
   |];;

let matrix_test_6 = [|
  [|false; false; true; true; false; false; false ; false|];
  [|false; false; false; true; false; false; false; false|];
  [|false; false; false; true; true; false; false; false|];
  [|false; false; false; false; false; false; false; false|];
  [|false; false; false; false; false; false; false; true|];
  [|false; false; false; false; true; false; true; false|];
  [|false; false; false; false; false; false; false; true|];
  [|false; false; false; false; false; false; false; false|];
   |];;

print_mat "\n***Matrix ***\n" matrix_test_6;;
print_mat "\n***Transitive closure 2***\n" (transClosure matrix_test_6);;
(*print_mat "\n***SCC ***\n" (scc matrix_test_2);;*)

(* print the output *)
let f elem =
  print_string "\n****List results: ";
  print_int elem ; print_newline()
in List.iter f (List.flatten (topo_order matrix_test_6));;

(******************************************************************************)
(* *)

(* print position and value of array *)
let my_array_1 = [|"1";"23";"3";"4";"5"|];;
Array.iteri (fun i x -> printf "%s at location %i\n" x i) my_array_1;;
Array.iteri (fun i x -> printf "position %i has a value %s\n" i x) my_array_1;;

(* index list which take a list and an element e and returns a
   position of that element. If e is an invalid element i.e. not in the
   list then return -1 *)
let index l e =
  let rec aux l i n =
    if n == (List.length l) then -1
    else if (List.nth l n) = e then n
    else aux l e (n + 1)
  in aux l e 0;;

(* nth list which take a list l and index n and returns the nth
   element of the list. If n is an invalid index i.e. n is negative or l
   less than (n + 1) elements raise "Not_found" *)
let rec nth l n =
  match l with
    | [] -> raise Not_found
    | h :: tl -> if n = 0 then h else nth tl (n - 1);;

printf "nth %i \n" (nth [1;2;3] 0);;

(******************************************************************************)
(* Compute strongly connected component with Tarjan's algorithm *)

(* Tarjan scc *)
let tarjan_scc = function matrix ->
  let n = Array.length matrix in
  let
      visited_at_depth = Array.make n max_int and
      scc_root = Array.make n max_int and
      open_nodes = Stack.create () and
      result = ref []
  in

  let rec unstack_until = function i ->
    match Stack.pop open_nodes with
      | n when n = i -> [i]
      | n -> n :: unstack_until i
  in
  
  let rec dfs depth = function i ->
    (* marked *)
    visited_at_depth.(i) <- depth;
    scc_root.(i) <- depth;
    Stack.push i open_nodes;
    
    for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      if matrix.(i).(j) = 1 &&  matrix.(j).(i) = 1then
	if visited_at_depth.(j) = max_int then
	  scc_root.(i) <- min scc_root.(i) (dfs (depth + 1) j) (*dive*)
	else
	  scc_root.(j) <- min scc_root.(i) visited_at_depth.(j) (*reverse-arc*)
    done;
    done;
  

    (* emit connected component if current not is root *)
    if scc_root.(i) = visited_at_depth.(i) then
      result := unstack_until i :: !result;
    scc_root.(i)
 in
  for i = 0 to n - 1 do
    if (visited_at_depth.(i) = max_int) then
      ignore (dfs 0 i)
  done;
  !result

(* print matrix *)
let print_int s m : unit =
  print_string s;
  for i = 0 to length m - 1 do
    for j = 0 to length m.(0) - 1 do
      print_string (string_of_int m.(i).(j));
      printf " ";
    done;
    printf " \n";
  done;
;;


(* Mehlhorn Gabow scc *)
let cmg_scc = function matrix ->

  let n = Array.length matrix in
  let 
      visited_at_depth = Array.make n max_int and
      roots = Stack.create () and
      open_nodes = Stack.create ()
  in

  let rec unstack_until = function i ->
    match Stack.pop open_nodes with
      | n when n = i -> [i]
      | n -> n :: unstack_until i
  in

  let rec dfs depth = function i ->

    let result = ref [] in
    
    (* mark *)
    Stack.push depth roots;
    Stack.push i open_nodes;
    visited_at_depth.(i) <- depth;
    
    (* dive *)
    for j = 0 to n - 1 do
      if (matrix.(i).(j) = 1) && (visited_at_depth.(j) = max_int) then 
	result := dfs (depth + 1) j @ !result
    done;

    (* process reverse-arcs *)
    for j = 0 to n - 1 do
      if (matrix.(i).(j) = 1)  && (visited_at_depth.(j) < depth) then 
	let scc_returns_to_depth = visited_at_depth.(j) in
	while Stack.top roots > scc_returns_to_depth do ignore (Stack.pop roots) done
    done;    
    
    (* emit connected component if current node is root *)
    if depth = Stack.top roots then
      (
	ignore (Stack.pop roots);
	unstack_until i :: !result
      )
    else
      !result
  in

  let result = ref [] in
  for i = 0 to n - 1 do 
    if (visited_at_depth.(i) = max_int)
    then result := (dfs 0 i) @ !result
  done;
  !result

 

(* test tarjan *)
let mat_test = [|
  [|0; 1; 1|];
  [|0; 0; 1|];
  [|1; 1; 0|];
  |];;

let mat_test_2 = [|
  [|0; 0; 0; 1; 0|];
  [|0; 0; 0; 1; 0|];
  [|0; 1; 0; 0; 0|];
  [|0; 0; 0; 0; 1|];
  [|0; 1; 0; 0; 0|];
  |];;

let mat_test_0 = [|
  [|0; 1; 1|];
  [|1; 0; 0|];
  [|0; 0; 0|];
   |];;

let mat_test_4 = [|
  [|0; 1; 0; 1|];
  [|0; 0; 0; 0|];
  [|1; 0; 0; 0|];
  [|0; 0; 0; 0|];
   |];;

let mat_test_5 = [|
  [|0; 1; 0; 1; 0; 0|];
  [|1; 0; 1; 0; 0; 0|];
  [|0; 1; 0; 0; 1; 1|];
  [|0; 0; 0; 0; 0; 0|];
  [|0; 0; 0; 0; 0; 0|];
  [|0; 0; 1; 0; 0; 0|];
   |];;

let mat_test_6 = [|
  [|0; 0; 1; 1; 0; 0; 0; 0|];
  [|0; 0; 0; 1; 0; 0; 0; 0|];
  [|0; 0; 0; 1; 1; 0; 0; 0|];
  [|0; 0; 0; 0; 0; 0; 0; 0|];
  [|0; 0; 0; 0; 0; 0; 0; 1|];
  [|0; 0; 0; 0; 1; 0; 1; 0|];
  [|0; 0; 0; 0; 0; 0; 0; 1|];
  [|0; 0; 0; 0; 0; 0; 0; 0|];
   |];;

(*let of_int = function
  | false -> [0]
  | _ -> [1];;

let ss i = List.map of_int i;;

let mat_test_5 =  array_list_map (ss (List.flatten (to_list matrix_test_5)));;*)

let s = array_list_map (tarjan_scc mat_test_6);;

let g = array_list_map (cmg_scc mat_test_6);;

print_int "tarjan \n " s;;
print_int "cmg \n " g;;

(* 'a list to 'a list list *)
let pack l = 
  let rec pack_2 l s e =
    match l with
      | [] -> [s]
      | h :: t ->
	if (h = e) then
	  (pack_2 t (h :: s) e)
	else s :: (pack_2 t [h] h)
  in
  match l with
    | [] -> []
    | h :: t -> pack_2 t [h] h;;

let to_matrix = function list ->
  let n = 1 + 
    List.fold_left (fun current (i, j) -> max current (max i j)) 0 list in
  let matrix = Array.make_matrix n n false in
  let rec add_arc = function
    | [] -> matrix
    | (i, j) :: tail -> matrix.(i).(j) <- true; add_arc tail
  in add_arc list;;

(**)
 (* Example built to show the open-node stack / dfs call-stack difference *)
(*let example =  to_matrix [(0, 1); (1, 2); (2, 3); (3, 4); (4, 2); (2, 1); (3, 5); (5, 6); (6, 5)]*)

(* TEST *)
let rec get_name_sequence2  = function
  | SimpleType n | GroupRef (n, _, _) -> [n]
  | Sequence xs -> get_name_lists2 xs 
  | Elt (_, Some t, _, _) -> get_par_name_sequence2 t
  | x -> get_name_sequence2 x

and get_par_name_sequence2 = function
  | SimpleType n | GroupRef (n, _, _) -> [n]
  | x -> get_name_sequence2 x

and get_name_choice2 = function
  | Elt (n, Some (Choice []), _, _) | Elt (n, None, _, _) -> [n]
  | GroupRef (n, _, _) -> [n]
  | Elt (_, Some t, _, _) -> get_name_sequence2 t
  | x -> get_name_sequence2 x

and get_name_lists2 = function
  | [] -> []
  | xsd :: xsds ->
    let xsd' = get_name_choice2 xsd in
    let xsds' = get_name_lists2 xsds in
    xsd' @ xsds' 

and get_list_name2 = function
  | Choice xs -> get_name_lists2 xs
  | x -> get_name_sequence2 x

and get_pair_name2 = function 
  | Group (n, Some t, _, _) ->
    n, get_list_name2 t
  | Elt (_, _, _, _) -> "", []
  | _ -> assert false

let get_list_xsds2 xsds = List.map get_pair_name2 xsds
