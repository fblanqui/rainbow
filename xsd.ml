(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-10-20

internal representation of XSD files
******************************************************************************)

type bound = Bound of int | Unbounded;;

type xsd =
  | Elt of string * xsd option * int * bound
  | Group of string * xsd option (*REMOVE option?*) * int * bound
  | GroupRef of string * int * bound
  | Choice of xsd list
  | Sequence of xsd list
  | SimpleType of string;;

(******************************************************************************)
(* Printing functions for debugging *)

open Printf;;
open Util;; 

let bound b = function
  | Unbounded -> bprintf b "unbounded"
  | Bound i -> bprintf b "%d" i;;

let option f b = function
  | None -> bprintf b "None"
  | Some x -> bprintf b "Some(%a)" f x;;

let rec xsd b = function
  | Elt (s, x, i, a) ->
    bprintf b "Elt(%s,%a,%d,%a)" s (option xsd) x i bound a
  | Group (s, x, i, a) ->
      bprintf b "Group(%s,%a,%d,%a)" s (option xsd) x i bound a
  | GroupRef (s, i , a) -> bprintf b "GroupRef(%s,%d,%a)" s i bound a
  | Choice xs -> bprintf b "Choice(%a)" (list "," xsd) xs
  | Sequence xs -> bprintf b "Sequence(%a)" (list "," xsd) xs
  | SimpleType s -> bprintf b "SimpleType(%s)" s;;

(*REMOVE: type xsd_elt =
  | Elt of string * xsd_type_def * int * bound
  | Grp of string * int * bound
  | Com of xsd_complex_type

and xsd_complex_type =
  | Cho of xsd_elt list
  | Seq of xsd_elt list

and xsd_type =
  | TNon
  | TRef of string
  | TCom of xsd_elt
  | TSim of string

type xsd_top_elt = bool * string * xsd_type * int * bound;;*)

(*****************************************************************************)

(* Return a name tag of xsd. *)

let name_of_elt = function
  | Elt (n, _, _, _) | Group (n, _, _, _) | GroupRef (n, _, _) -> n
  | _ -> assert false;;

(* Check the equality of name <Elt> and <Group>. *)

let name_eq n = function
  | Elt (s, _, _, _) | Group (s, _, _, _) -> n = s
  | _ -> false;;

(*****************************************************************************)
(* Functions for managing type names. *)
(*****************************************************************************)

(* in file ml_of_xsd.ml *)

let init_types, _is_group, next_type, add_type =
  let types = ref [] (* list of types to be generated *)
  and generated_types = ref [] (* list of generated types *)
  and groups = ref StrSet.empty (* set of groups *) in

  (* init_types: reset list of generated types and compute the set of groups
     from a list of xsd values *) 
  (let add_group = function
     | Group (n, _, _, _) -> groups := StrSet.add n !groups 
     | Elt _ | GroupRef _ | Choice _ | Sequence _ | SimpleType _ -> ()
   in fun xs -> types := xs; List.iter add_group xs),

  (* is_group: say if a name is a group name *)
  (fun n -> StrSet.mem n !groups),

  (* next_type: return to the next type to generate and add it to the list
     of generated types if it exists, or raise Not_found *)
  (fun () -> match !types with
     | [] -> raise Not_found
     | t :: ts -> types := ts; generated_types := t :: !generated_types; t),

  (* add_type: add a type to the list of types to be generated
     if it is a new type (not already in types or generated_types);
     generate a new name if no name is given *)

   (let new_type_id = counter() (* counter for new types *) in

    let new_type_name () = Printf.sprintf "t%d" (new_type_id())

    and add_group n x = 
      types := Group (n, Some x, 1, Bound 1) :: !types; (n, true)
    in 
     fun no x ->
      match no with
	| Some n ->
	    begin match List.filter (name_eq n) (!generated_types @ !types) with
	      | [] -> add_group n x
	      (* FIXME *)
	      | [Group (_, Some y, _, _)] | [Elt (_, Some y, _, _) ] ->
		if x = y then (n, false)
		else (*add_group n x*)
		  add_group (n ^ "_" ^ new_type_name()) x
	      (* FIXME: if they are the same name then keep it likes that. *)
	      | _ -> assert false end
	| None -> add_group (new_type_name()) x)

  
(* add_group is different in the newcpf.ml where if they are the same *)

(*****************************************************************************)
(* Flattening: replace internal choices by grouprefs and add the
   corresponding group definitions.

   Where [no] is an option name, if the xsd has no type they will
   generate a new type name. If the xsd has their type name then use
   that name.

   For example:
   + <Elt>
   ++ ....
   (++...) Choice(Elt(lex,Some(Choice()),1,1),Elt(mul,None,1,1))
   ...

   Then after the flattening:

   + <Elt>
   ++ ...
   (++...) <GroupRef (t10, 1, Bound 1)>
   ...

   and a new xsd:
   
   <Group(t10,Some(Choice(Elt(lex,Some(Choice()),1,1),
   Elt(mul,None,1,1))),1, Bound 1)>
   
   where [t10] is a new type name. *)

let rec flatten_innerchoice_xsd no = function
  | Choice (_ :: _) as x ->
    let n, b = add_type no x in
    GroupRef (n, 1, Bound 1),
    if b then
      [Group (n, Some x, 0, Unbounded)] else []
  | Sequence xs ->
    let xs', new_xsds = flatten_innerchoice_xsds xs in
    Sequence xs', new_xsds
  | Elt (n, Some xsd, i, a) ->
      let xsd', new_xsds = flatten_innerchoice_xsd (Some n) xsd in
	Elt (n, Some xsd', i, a), new_xsds
  | Group (n, Some xsd, i, a) ->
      let xsd', new_xsds = flatten_innerchoice_xsd (Some n) xsd in
      Group (n, Some xsd', i, a), new_xsds
  | Elt (_, None, _, _)
  | Group (_, None, _, _)
  | SimpleType _
  | GroupRef (_, _, _)
  | Choice [] as x -> x, [];

and flatten_innerchoice_xsds = function
  | [] -> [], []
  | xsd :: xsds ->
    let xsd', new_xsds1 = flatten_innerchoice_xsd None xsd in
    let xsds', new_xsds2 = flatten_innerchoice_xsds xsds in
    xsd' :: xsds', new_xsds1 @ new_xsds2

and flatten_top_innerchoice_xsd = function
  | Choice xs ->
    let xs', new_xsds = flatten_innerchoice_xsds xs in
    Choice xs', new_xsds
  | x -> flatten_innerchoice_xsd None x
      
and flatten_innerchoice_def = function
  | Elt (n, Some xsd, i, a) ->
      let xsd', new_xsds = flatten_top_innerchoice_xsd xsd in
	Elt (n, Some xsd', i, a) :: flatten_innerchoice new_xsds
  | Group (n, Some xsd, i, a) ->
      let xsd', new_xsds = flatten_top_innerchoice_xsd xsd in
	Group (n, Some xsd', i, a) :: flatten_innerchoice new_xsds
  | Elt (_, None, _, _) | Group (_, None, _, _) | SimpleType _
  | GroupRef _
  | Choice _ | Sequence _ as x -> [x]

and flatten_innerchoice = function
  | [] -> []
  | xsd :: xsds -> flatten_innerchoice_def xsd @ flatten_innerchoice xsds;;

(*****************************************************************************)
(* Split xsds list into a tupe (string, list of strings).
   For example: consider the xsd <label> the output will be:
   ("label", ["nonNegativeInteger"; "symbol"]) *)

let rec get_name_sequence  = function
  | SimpleType n
  | GroupRef (n, _, _) -> [n]
  | Sequence xs -> get_name_lists xs
  | Elt (_, Some t, _, _) -> get_par_name_sequence t
  | x -> get_name_sequence x

and get_par_name_sequence = function
  | SimpleType n
  | GroupRef (n, _, _) -> [n]
  | x -> get_name_sequence x

and get_name_choice = function
  | Elt (n, Some (Choice []), _, _) 
  | Elt (n, None, _, _)
  | GroupRef (n, _, _) -> [n]
  | Elt (_, Some t, _, _) -> get_name_sequence t
  | x -> get_name_sequence x

and get_name_lists = function
  | [] -> []
  | xsd :: xsds ->
    get_name_choice xsd @ get_name_lists xsds

and get_list_name = function
  | Choice xs -> get_name_lists xs
  | x -> get_name_sequence x

and get_pair_name = function
  | Elt (n, Some t, _, _) | Group (n, Some t, _, _) ->
    n, get_list_name t
  | _ -> assert false

let get_list_xsds xsds = List.map get_pair_name xsds

(* Capitalize the first character of a tag name and link with a base name 
   of element to avoid OCaml compilation errors. *)

let constructor_name tn bn = String.capitalize tn ^ "_" ^ bn;;
