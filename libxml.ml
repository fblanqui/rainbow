(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

XML parsing and generation
******************************************************************************)

open Xml;;
open Error;;
open Util;;

type tag = string;;

(*****************************************************************************)
(* xml parsing and writing *)
(*****************************************************************************)

let xml_version = "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n";;

let output_xml oc x =
  Printf.fprintf oc "%s\n%s\n" xml_version (Xml.to_string_fmt x);;

let parse_xml ic =
  try parse_in ic
  with Xml.Error e -> prerr_endline (Xml.error e); exit 1;;

(*****************************************************************************)
(* xml generation *)
(*****************************************************************************)

let elt tag xs    = Element (tag, Util.dummy_pos, [], xs);;

let pc s          = PCData (s, Util.dummy_pos);;

let pc_int k      = pc (string_of_int k);;
let pc_int64 k    = pc (Int64.to_string k);;

let elt_int tag k = elt tag [pc_int k];;

(*****************************************************************************)
(* xml matching *)
(*****************************************************************************)

let rec height = function
  | PCData _ -> 0
  | Element (_, _, _, xs) -> 1 + max_height 0 xs

and max_height acc = function
  | [] -> acc
  | x :: xs -> max_height (max acc (height x)) xs;;

(* FIXME: changed name, used in the old version of rainbow *)

let get_pc = function
  | PCData (s,_)   -> s
  | Element _ as x -> error_xml x "not a PCData";;

let string = get_pc;;

let boolean x =
  try bool_of_string (get_pc x)
  with Scanf.Scan_failure _ -> error_xml x "not a boolean";;

(*****************************************************************************)
(* Parsing functions used integer 63-bits *)
(*****************************************************************************)
(* FIXME: change name *)

(*FIXME: unsound hack for dealing with 64-bits integers*)
let get_int =
  let min = Int64.of_int min_int and max = Int64.of_int max_int in
    fun x ->
      try
	let k = int64_of_string (get_pc x) in
	  if k > max then max_int
	  else if k < min then min_int
	  else Int64.to_int k
      with Scanf.Scan_failure _ -> error_xml x "not an integer";;

let get_nonNegativeInteger x =
  let  i = get_int x in
  if   i < 0
  then error_xml x "not a nonNegativeInteger"
  else i;;

let get_positiveInteger    x =
  let  i = get_int x in
  if   i <= 0
  then error_xml x "not a PositiveInteger"
  else i;;

let integer = get_int;;

let nonNegativeInteger = get_nonNegativeInteger;;

let positiveInteger    = get_positiveInteger;;

(*****************************************************************************)
(* Parsing the head of the list does not care what is the rest of the
   list, this function used in the case of <Choice>. *)
(*****************************************************************************)

let get_first_son tag f x =
  match x with
    | Element (t, _, _, x' :: _) when t = tag -> f x'
    | _ -> error_xml x ("not a " ^ tag);;

(* Parsing the whole list, this function used in the case of
   <Sequence>, <SimpleType>. *)

let get_sons tag f x =
  match x with
    | Element (t, _, _, xs) when t = tag -> f xs     
    | _ -> error_xml x ("not a " ^ tag);;

(*****************************************************************************)
(* xml parsing *)
(*****************************************************************************)

(*****************************************************************************)
(* Given a (parse) function, try to parse an element. In case of an
   error, returns None. Otherwise, returns the value obtained. *)

let try_parse f x = try Some (f x) with Error _ -> None;;

(*****************************************************************************)
(* (parse_list parse xs) parses the biggest prefix of xs with the
   (parse) function, i.e. it returns the pair (is, xs2) such that:
   - xs = xs1 @ xs2
   - is = List.map parse xs1
   - xs1 is as big as possible *)

let parse_list f =
  let rec parse_list_aux acc xs =
    match xs with
      | [] -> List.rev acc, []
      | x :: xs' ->
	match try_parse f x with
	  | Some y -> parse_list_aux (y :: acc) xs'
	  | None     -> List.rev acc, xs
  in parse_list_aux [];;

(*****************************************************************************)
(* parse the first/head element in a list of elements, if it is an
   empty list then return an error message. *)

let parse_first_elt f xs =
  match xs with
    | x :: xs' -> f x, xs'
    (* FIXME:changed to print the error with position *)
    | [] -> error_fmt "empty sequence of elements";;

(*****************************************************************************)
(* try to parse the first element of a list of elements *)

let parse_option f xs =
  match xs with
    | [] -> None, []
    | x :: xs' as xs ->
      match try_parse f x with
	| None -> None, xs
	| some_val  -> some_val, xs';;

(*****************************************************************************)
(* check that there is nothing else to parse; raises an error
   otherwise "unexpected element" mean the element expected to parse
   is not the right one. For example: at the tag <lhs> the first
   choice is an empty tag, if there is a name tag there (even if name
   is empty) it will raise an error unexpected element. *)

let check_emptyness xs =
  match xs with
    | [] -> ()
    | x :: _ -> error_xml x "not-empty sequence of elements";;
