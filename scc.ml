(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Kim Quyen Ly, 2011-11-28

Strongly connected component
******************************************************************************)
(*let position (x:int) =
  let rec aux = function
    | [] -> raise Not_found
    | y :: ys -> if x = y then 0 else 1 + aux ys
  in aux;; *)
(*
let num_of_name (defined: string list) undefined len_undefined s =
  try let p = position s defined in Some (p + len_undefined)
  with Not_found -> 
    try let p = position s undefined in Some p
    with Not_found -> None
 
(* Funtion taking a position of xsds list and undefined list, return
   their element. *)

let name_of_num (xsds: Xsd.xsd list)  undefined len_undefined k =
  if k < len_undefined then List.nth undefined k else
    List.nth xsds (k - len_undefined)*)

(* Transitive closure: 
   for example: in a set of A, i, j, k in A, if we
   have a path from i -> k and k -> j we will have a path from i -> j *)

let transClosure (m: bool array array) =
  let n = Array.length m - 1 in
  for k = 0 to n do
    for i = 0 to n do
      for j = 0 to n do
        if not m.(i).(j) && m.(i).(k) && m.(k).(j) then m.(i).(j) <- true
      done;
    done;
  done;
  m;;

(* Function search a connection in boolean matrix between two nodes i
   and j. If it does not has any connection between them then add an
   edge i -> j and compute a transitive closure. Change connection in
   boolean matrix: if in the case (false, false) -> (true, false). *)

exception Incomparable;;

let rec linearize m =
  try
    let n = Array.length m - 1 in
    for i = 0 to n do
      for j = 0 to n do
	if not (m.(i).(j) || m.(j).(i)) then
	  (m.(i).(j) <- true; raise Incomparable)
      done;
    done;
    m
  with Incomparable -> linearize (transClosure m);;

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

(* To reprensent equivalence classes, we don't need a list of ints. We
   can either pick a unique representant (the smaller int of the class
   for instance) or we can pick any (as we don't really care, as we
   have the transitive closure of the relation available anyway); If
   the boolean matrix represents the transitive closure, then to
   compare two elements, we just have to check the booleans. This
   function has a purpose like [compare] function in OCaml's
   library. *)

let cmp_classes m i j =
  match m.(i).(j), m.(j).(i) with
    (* same class: there is a path between i and j, and between j and i *)
    | true, true   -> 0
    (* there is a path between i and j *)
    | true, false  -> 1
    (* there is a path between j and i *)
    | false, true  -> -1
    (* i and j are not compareable *)
    | false, false -> assert false

(* Sort a list in increasing order according to a comparison
   function. The comparison function must return 0 if its arguments
   compare as equal, a positive integer if the first is greater, and a
   negative integer if the first is smaller. For example, compare is a
   suitable comparison function. The resulting list is sorted in
   increasing order. List.sort is guaranteed to run in constant heap
   space (in addition to the size of the result list) and logarithmic
   stack space. *)

let sort_eq_classes       m = List.sort (cmp_classes m);;

let closure_matrix   xsds m = transClosure (m xsds)

let line_matrix      xsds m = linearize (closure_matrix xsds m)

let equivalence      xsds m = eq_classes (line_matrix xsds m)

let sort_equivalence xsds m = sort_eq_classes (line_matrix xsds m)
                              (List.flatten (equivalence xsds m))

(******************************************************************************)
(* Funtion taking an xsds list and undefined list, return a position of xsds
   list. Position is a tail-recursive function, and monomorphic type. *)

let position x =
  let rec aux k = function
    | []      -> raise Not_found
    | y :: ys -> if x = y then k else aux (k+1) ys
  in aux 0;; 

open Xsd;;

(* Define a function [num_of_name] and [name_of_num] without undefined
   list. *)

let num_of_name defined s =
  try let p = position s defined in Some p
  with Not_found -> None

(* Using monorphic type is effective than polymorphic type. *)

let name_of_num xsds k = List.nth xsds k

let defined     xsds   = List.map name_of_elt xsds

(* Compute matrix in the xsds. *)

let matrix xsds =
  let pair_xsds = get_list_xsds xsds              in
  let len       = List.length (defined xsds)      in
  let boolmat   = Array.make_matrix len len false in
  List.iter (fun (s, strs) ->
    match num_of_name (defined xsds) s with
      | Some pos1 -> List.iter (fun t ->
        match num_of_name (defined xsds) t with
          | Some pos2 -> boolmat.(pos1).(pos2) <- true
          | None      -> ()) strs
      | None       -> ()
  ) pair_xsds;
  boolmat

let xsds_of_int_fun xsds = List.map (List.map (name_of_num xsds))

let xsds_sorted_fun xsds = xsds_of_int_fun xsds [(sort_equivalence xsds matrix)]
