(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-10-20

convert an xml value to an xsd value
******************************************************************************)

open Xml;;
open Util;;
open Xsd;;
open Error;;

(* parse the value of a minOccurs attribute *)
let min x s =
  try int_of_string s
  with Scanf.Scan_failure _ -> error_xml x "invalid minOccurs value";;

(* parse the value of a maxOccurs attribute *)
let max x = function
  | "unbounded" -> Unbounded
  | s -> try Bound (int_of_string s) 
    with Scanf.Scan_failure _ -> error_xml x "invalid maxOccurs value";;

(* type for XSD attributes *)
type attribs = {
  aname : string option;
  aref : string option;
  atype : string option;
  amin : int;
  amax : bound };;

(* parse the values of XSD attributes *)
let get_values x =
  let rec aux a = function
    | [] -> a
    | ("name", s) :: l -> aux { a with aname = Some s } l
    | ("ref", s) :: l -> aux { a with aref = Some s } l
    | ("type", s) :: l -> aux { a with atype = Some s } l
    | ("minOccurs", s) :: l -> aux { a with amin = min x s } l
    | ("maxOccurs", s) :: l -> aux { a with amax = max x s } l
    | _ :: l -> aux a l
  in aux { aname = None; aref = None; atype = None; amin = 1; amax = Bound 1 };;

(* setting/getting XML name space *)
let set_ns, get_ns =
  let ns = ref "" in
    (fun s -> ns := s ^ ":"),
    (fun () -> !ns);;

(* parse element name (removing the leading name space) *)
let tag_of_string s =
  let ns = get_ns () in
  let k = String.length ns in
    try
      if String.sub s 0 k <> ns then s
      else String.sub s k (String.length s - k)
    with Invalid_argument _ -> s;;

(* main function for converting XML to XSD *)
let rec xsd x =
  match x with
    | Element (t, _, attribs, xs) ->
	begin match tag_of_string t with
	  | "element" ->
	      let a = get_values x attribs in
		begin match a.aname with
		  | Some n ->
		      begin match a.atype with
			| Some s ->
			    Elt (n, Some (SimpleType (tag_of_string s)),
				 a.amin, a.amax)
			| None -> Elt (n, first_xsd xs, a.amin, a.amax)
		      end
		  | None ->
		      begin match a.aref with
			| Some s -> let n = tag_of_string s in
			    Elt (n, Some (SimpleType n), a.amin, a.amax)
			| None -> error_xml x "no name or ref attribute"
		      end
		end
	  | "group" ->
	      let a = get_values x attribs in
		begin match a.aname with
		  | Some n ->
		      begin match a.atype with
			| Some s ->
			    Group (n, Some (SimpleType (tag_of_string s)),
				   a.amin, a.amax)
			| None -> Group (n, first_xsd xs, a.amin, a.amax)
		      end
		  | None ->
		      begin match a.aref with
			| Some n -> GroupRef (n, a.amin, a.amax)
			| None -> error_xml x "no name or ref attribute"
		      end
		end
	  | "choice" -> Choice (xsds xs)
	  | "sequence" -> Sequence (xsds xs)
	  | "complexType" ->
	      begin match first_xsd xs with
		| None -> Choice []
		| Some d -> d
	      end
	  | _ -> error_xml x "not a schema element"
	end
    | PCData _ -> error_xml x "not a schema element"

and xsds = function
  | [] -> []
  | Element (t, _, _, _) :: xs when tag_of_string t = "annotation" -> xsds xs
  | (PCData _ | Element _) as x :: xs -> xsd x :: xsds xs

and first_xsd = function
  | [] -> None
  | Element (t, _, _, _) :: xs when tag_of_string t = "annotation" ->
      first_xsd xs
  | (PCData _ | Element _) as x :: _ -> Some (xsd x);;

(* set name space from a list of attributes *)
let rec set_name_space = function
  | [] -> ()
  | (s, _) :: attribs ->
      let n = String.length s in
	if n >= 6 && String.sub s 0 6 = "xmlns:" then
	  set_ns (String.sub s 6 (n-6))
	else set_name_space attribs;;

(* set name space before starting conversion *)
let xsd_of_xml = function
  | Element (t, _, attribs, xs)
      when set_name_space attribs; tag_of_string t = "schema" -> xsds xs
  | (PCData _ | Element _) as x -> error_xml x "not a schema";;

