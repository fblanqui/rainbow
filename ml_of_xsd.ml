(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Kim-Quyen Ly, 2010-11-19
- Frederic Blanqui, 2009-10-20

Generate an parser function from a xsd value.
******************************************************************************)

(* REMARK: this is the code for cpf.xsd version 2.1 *)

open Printf;;
open Xsd;;
open Util;;
open Scc;;
open String;;

(*****************************************************************************)
(* General functions *)
(*****************************************************************************)

let todo b = string b "todo";;

(* Keywords of OCaml and Coq type. *)

let keywords = function
  | "function" | "type" as s -> "cpf_" ^ s
  | s -> s;;

let a_an s = match s.[0] with
  | 'a' | 'e' | 'i' | 'o' | 'u' -> "an"
  | _ -> "a"

(* [undefine] type use to check if the OCaml function return type of
   undefine in OCaml. *)

let undefine n =
  (match n with
      "nonNegativeInteger" | "integer" | "positiveInteger" | "boolean"
    | "long" -> n
    | _ -> "");;

(* Define a function return a string without the part of ^_t%d in new
   name. For example: interpret_t19 -> interpret. TODO: fixme *)

let chop s =
  if s = "" then s else String.sub s 0 (String.length s - 4);;

(*****************************************************************************)
(* Parsing functions *)
(*****************************************************************************)

(* - At GroupRef (, 0, Unbounded): For debug information: [before] and
   [after] type in [contex] type. *)

let parser_of tn b = function
  | GroupRef (_, 0, Unbounded) ->  bprintf b "%s" tn
  | GroupRef (n, _, _) ->
    if   n = tn
    then Util.string b (keywords tn)
    else bprintf b "(get_first_son \"%s\" %s_val)" tn n
  | SimpleType n ->
    if   n = tn
    then Util.string b (keywords n)
    else bprintf b "(get_first_son \"%s\" %s)" tn n
  | Sequence _ as x -> Util.string b (fst (add_type (Some tn) x))
  | _ -> todo b;;

(* [type_sequences] is a printing function in the case of Sequence
   constructor. This is different than the [sequence_in_choice] at the
   printing of [item] where it needs a parenthesis at a pair. 
   - At Elt (n, None, _, _): print the boolean function as an [option] type.
   - At Elt (n, Some t, 0, Bound 1):
   REMARK: CPF version 2.0 different than CPF version 2.1 at the
   [origin] tag where in 2.0 it is an [option] type but it is not
   in version 2.1. To be able to parse 2.1 change it to an non
   [option] type.

   - Unbounded -> list type
   - 0, Bound 1 -> option type

   - At GroupRef (n, _, Unbounded) -> parsing function of
   uncurriedsymbolEntry tag

   - At Sequence: REMARK: in cpf version 2.0 and 2.1 different at the
   tag [tpdb-refence] and [tppdbReference]. *)

let rec type_sequences tn sn b = function
  | Elt (n, None, _, _) ->
    bprintf b "\n        let item_%s, xs = parse_option \
               (get_first_son \"%s\" boolean) xs in" n n
  | Elt (n, Some t, 0, Bound 1) ->
    if   n = "subsumptionProof"
    then bprintf b "\n      let item_%s1, xs = parse_option %a xs in"
      n (parser_of n) t
    else bprintf b "\n        let item_%s, xs = parse_option %a xs in"
      n (parser_of n) t
  | Elt (n, Some t, 1, Bound 1) ->
    (match t with
      | GroupRef (_, 1, Unbounded) ->
	bprintf b "\n        let item_%s, xs = parse_list %a xs in"
	  n (parser_of n) t
      | GroupRef (_, 0, Unbounded) ->
	bprintf b "\n        let item_%s, xs = parse_first_elt %s xs in"
	  n n 
      | GroupRef (_, 1, Bound 1) ->
	bprintf b "\n        let item_%s, xs = parse_first_elt %a xs in"
	  n (parser_of n) t
      | _ -> bprintf b "\n        let item_%s, xs = parse_first_elt %a xs in"
	n (parser_of n) t)
  | Elt (n, Some t, _, _) ->
    bprintf b "\n        let item_%s, xs = parse_list %a xs in"
      n (parser_of n) t
  | GroupRef (n, 1, Bound 1) ->
    bprintf b "\n        let item_%s, xs = parse_first_elt %s_val xs in"
      n n
  | GroupRef (n, _, Bound 1) ->
    bprintf b "\n        let item_%s, xs = parse_list %s_val xs in"
      n n
  | GroupRef (n, _, Unbounded) ->
    bprintf b "\n      let item_%s1, xs = parse_list %s_val xs in" 
      n (keywords n)
  | Sequence xs ->
    let aux = function
      | Choice _ -> false (* If it an inner choice, then it
                             is fail because of the flattening function *)
      | _        -> true
    in
    let xs = List.filter aux xs in
    list "     " (type_sequences tn "") b xs;
    bprintf b "\n        check_emptyness xs;\n";
    let aux b = function
      (* REMARK: in CPF version 2.1 at some types OCaml *)
      | Elt (n, _, 0, Bound 1) -> (* TODO *)
	(* REMARK: at the function [equivalenceProof_val]. Similiar name. *)
	if   n = "subsumptionProof"
        then bprintf b "item_%s1" n
        else bprintf b "item_%s" n (* FIXME *)
      | Elt (n, _, _, _)
      | GroupRef (n, _, Bound 1)   -> bprintf b "item_%s"  n
      | GroupRef (n, _, Unbounded) -> bprintf b "item_%s1" n
      | _                          -> assert false
    in
    (* define [aux'] print as an unit type to be able to have a
       correct type when print the parenthesis. *)
    let aux' _ = function
      | Elt (_, _, _, _) | GroupRef (_, _, _) -> ()
      | _ -> assert false
    in
    (* Print the parenthesis at the bottom of the function. For the
       type automatically generated in OCaml from COQ use the
       parenthesis. For example: [cpf0.ml]
       type argumentFilter = ((symbol * arity) * t3) list *)
    (match xs with
      | []      -> ()
      | [x]     -> bprintf b "        %s (%a)" sn aux x
      | x :: xs -> bprintf b "        %s (%a"  sn       (list "(" aux') xs;
 	bprintf b "(%a, %a))"          aux x (list ")," aux) xs;
	bprintf b "%a"                       (list "" aux') xs)
  | _           -> bprintf b "todo type_sequences";;

(* [sequence_in_choice] is a printing function in the case of Sequence
   constructor in choice. This is different than the [type_sequences]
   at the printing of [item] where it needs a parenthesis as a
   pair.
   - At SimpleType n -> normal type in COQ type.For debug information [t3] at
       [collapsing].
   - At Elt (n, Some t, 0, Bound 1) ->
   [dpProof_val] at dpProof has type option (* FIXME *) *)

let rec sequence_in_choice tn sn b = function
  | SimpleType n ->
    bprintf b "\n        let item_%s, xs = parse_first_elt %s xs in\n       \
                          check_emptyness xs;\n       \
                          %s (item_%s)"
      n n (constructor_name sn tn) n
  | Elt (n, None, _, _) ->
    bprintf b "\n        let item_%s, xs = parse_option \
               (get_first_son \"%s\" boolean) xs in" 
      n n
  | Elt (n, Some t, 0, Bound 1) -> (* TODO *)
    if   n = "rule" || n = "dpProof"
    then bprintf b "\n      let item_%s1, xs = parse_option %a xs in"
	   n (parser_of n) t
    else bprintf b "\n        let item_%s, xs = parse_option %a xs in"
           n (parser_of n) t
  | Elt (n, Some t, 1, Bound 1) ->
    (match t with
      | GroupRef (_, 1, Unbounded) ->
	bprintf b "\n        let item_%s, xs = parse_list %a xs in"
	  n (parser_of n) t
      | GroupRef (_, 0, Unbounded) ->
	bprintf b "\n        let item_%s, xs = parse_first_elt %s xs in"
	  n n 
      | GroupRef (_, 1, Bound 1) ->
	bprintf b "\n        let item_%s, xs = parse_first_elt %a xs in"
	  n (parser_of n) t
      | _ ->
	bprintf b "\n        let item_%s, xs = parse_first_elt %a xs in"
	  n (parser_of n) t)
  | Elt (n, Some t, _, _) ->
    bprintf b "\n        let item_%s, xs = parse_list %a xs in"
      n (parser_of n) t
  | GroupRef (n, 1, Bound 1) ->
    bprintf b "\n        let item_%s, xs = parse_first_elt %s_val xs in"
      n n
  | GroupRef (n, _, Unbounded) ->
    bprintf b "\n        let item_%s, xs = parse_list %s_val xs in"
      n n
  | GroupRef (n, 0, Bound 1) ->
    bprintf b "\n        let item_%s, xs = parse_option %s_val xs in" n n
  | Sequence xs ->
    let aux = function
      (* Remove this element in xsd.*)
      | Choice _ -> false
      | _        -> true
    in
    let xs = List.filter aux xs in
    list "     " (sequence_in_choice tn "") b xs;
    bprintf b "\n        check_emptyness xs;\n";
    let aux b = function
      | Elt (n, _, 0, Bound 1) -> (* TODO *)
	if   n = "rule" || n = "dpProof"
        then bprintf b "item_%s1" n
        else bprintf b "item_%s" n
      | Elt (n, _, _, _)
      | GroupRef (n, _, _) -> bprintf b "item_%s" n
      | _                  -> assert false
    in
    (* For Sequence in Choice does not need to print the parenthesis
       as pair. *)
    bprintf b "        %s (%a)" sn (list "," aux) xs;
  | _ -> bprintf b "todo sequence_in_choice";;

(*******************************************************************)
(* Define a function generate parsing function for [Element] element *)
(*******************************************************************)

(*******************************************************************)
(* <element> has <simpleType> as children *)

let genr_elem_simpl b n sn =
  let k = keywords n in
  bprintf b "%s x = get_sons \"%s\" %s_val x \n\n\
             and %s_val xs =                           \n  \
             let item_%s, xs = parse_first_elt %s xs in   \n   \
             check_emptyness xs;                    \n    \
             (item_%s)"
    k n n n n sn n;;

(*******************************************************************)
(* <element> has <sequence> as children. 
   REMAKR: patternRule in COQ defined as an Inductive with one
   constructor, it needs a parsing function as Choice and not as
   Sequence. (* FIXME *)*)

let genr_elem_sequence b n xs =
  let k = keywords n in
  if   n = "patternRule"
  then bprintf b "%s x = match x with \n  \
               | Element (\"%s\", _, _, xs) ->\ %a\n  \
               | x -> error_xml x \"not %s %s\""
         k k (type_sequences "" (constructor_name n n)) xs (a_an n) n	  
  else bprintf b "%s xs = get_sons \"%s\" %s_val xs \n\n\
               and %s_val xs = %a"
         k n n n (type_sequences n "") xs;;

(*******************************************************************)
(* <element> has <choice> as children.
   - At simpleTye [equationalDisproof] function.
   - At Sequence: CPF version 2.1, in the case of "Lhs_symbol".
 *)

(* Return type of <choice> has one children. *)

let elem_choice_one_child_type tn b = function
  | Elt (n, Some (Choice []), _, _) | Elt (n, None, _, _) ->
    bprintf b "| Element (\"%s\", _, _, _) -> %s\n\ "
      n (constructor_name tn n)
  | Elt (n, Some t, _, _) ->
    begin match t with
      | SimpleType _ ->
	bprintf b "| Element (\"%s\", _, _, xs) ->\n        \
                     %s (%s_val xs) \n   \ "
	  n (constructor_name tn n) n
      | Sequence xs ->
	let aux = function
	  | Choice _ -> false
	  | _        -> true
	in let xs = List.filter aux xs in
	   bprintf b "| Element (\"%s\", _, _, xs) -> " tn;
	     list "      " (type_sequences tn "") b xs;
	   bprintf b "\n        check_emptyness xs;\n";
	   let aux b = function
	     | Elt (n, _, _, _)
             | GroupRef (n, _, _) -> bprintf b "item_%s" n
	     | _                  -> assert false 
	   in bprintf b "        %s (%a) \n " (constructor_name tn n)
	        (list ", " aux) xs
      | _  -> todo b
    end
  | _ -> todo b;;

(* <choice> with one children *)

let elem_choice_one_child b n x =
  let k = keywords n in
  bprintf b "%s x = get_first_son \"%s\" %s_val x \n\n\
                   and %s_val x = match x with          \n   \
                       %a  \
                   | x -> error_xml x \"not %s %s\""
    k n n n (elem_choice_one_child_type n) x (a_an n) n;;

(*******************************************************************)
(* <choice> has more than one children 
   If the name of the tag name is equal to the type and its
   constructor has one type then print [Element] of the case
   below. Otherwise print a normal case where [xs] is a list. For
   debug information: [proof; number; coefficient; polynomial;
   dpNonterminationProof; relativeNonterminationProof; proof]
   FIXME: [loop] type needs a list of [xs] at type
   [dpNonterminationProof].

   - At SimpleType sn where n = "vector", n = "matrix";
   sn = "loop", "innermostLhss", "nonLoop", "completionProof";
   tn = "equationalProof": this require a parsing function is a list of xml
   sn = n then the [Element] require an [x]. *)

let elem_choice_more_child_type tn b = function
  | Elt (n, Some (Choice []), _, _) | Elt (n, None, _, _) ->
    bprintf b "| Element (\"%s\", _, _, _) -> %s"
      n (constructor_name tn n)
  | Elt (n, Some t, _, _) ->
    (match t with
      | SimpleType sn -> (* TODO *)
	if   n = "vector"
        then bprintf b "| Element (\"%s\", _, _, xs) -> %s (%s (%s_val xs))"
	       n (constructor_name tn n) (constructor_name n n) n
	else
          if   n = "matrix"
          then bprintf b "| Element (\"%s\", _, _, xs) -> %s (%s (%s_val xs))"
	         n (constructor_name tn n) (constructor_name n n) n
	  else
            if sn = "loop"    || sn = "innermostLhss" ||
               sn = "nonLoop" || sn = "completionProof"
            then bprintf b "| Element (\"%s\", _, _, xs) -> %s (%s_val xs)"
	           sn (constructor_name tn sn) sn
	    else
              if tn = "equationalProof"
              then bprintf b "| Element (\"%s\", _, _, xs ) ->\n    \
                        %s (%s_val xs)"
  	             n (constructor_name tn n) n
	      else
                if sn = n
                then bprintf b "| Element (\"%s\", _, _, x :: _) -> %s (%s_val x)"
 	               n (constructor_name tn n) n
 	        else
                  if sn = undefine sn
                  then bprintf b "| Element (\"%s\", _, _, xs) ->\n        \
                        let item_%s, xs = parse_first_elt %s xs in \n        \
                        check_emptyness xs;\n        \
                        %s item_%s"
                         n sn sn (constructor_name tn n) sn
	          else bprintf b "| Element (\"%s\", _, _, xs) -> %a"
     	                 n (sequence_in_choice n tn) t
      | x -> bprintf b "| Element (\"%s\", _, _, xs) -> %a"
	       n (sequence_in_choice n (constructor_name tn n)) x)
  | GroupRef (n, 1, Bound 1) ->
    bprintf b "| x when is_number x -> %s (%s_val x)"
      (constructor_name tn n) n
  | _ -> todo b;;

let elem_choice_more_child b n xs =
  let k = keywords n in
  bprintf b "%s x = get_first_son \"%s\" %s_val x \n\n\
                   and %s_val x = match x with          \n   \
                       %a                                 \n   \
                   | x -> error_xml x \"not %s %s\""
    k n n n ((list "\n   ")(elem_choice_more_child_type n)) xs (a_an n) n;;

(*******************************************************************)
(* <element> has <choice> as children *)

let genr_elem_choice b n xs =
  match xs with
    | [] -> ()
    | [x] -> elem_choice_one_child b n x
    | _ :: _ as xs -> elem_choice_more_child b n xs

(*******************************************************************)
(* Parsing function for <element> *)

let genr_type_elem b n t =
  match t with
    | SimpleType sn    -> genr_elem_simpl b n sn
    | Sequence _ as xs -> genr_elem_sequence b n xs
    | Choice xs        -> genr_elem_choice b n xs
    | _                -> bprintf b "todo genr_type_elem";;

(*******************************************************************)
(* Define a function generate parsing function for [Group] element *)
(*******************************************************************)

(* <group> has <sequence> as children *)

let genr_group_sequence b n xs =
  let k = keywords n in
  if   contains n '_'
  then bprintf b "%s xs = get_sons \"%s\" %s_val xs \n\n\
               and %s_val  xs = %a"
         k (chop n) n n (type_sequences n "") xs
  else bprintf b "%s xs = get_sons \"%s\" %s_val xs \n\n\
               and %s_val  xs = %a"
         k n n n (type_sequences n "") xs;;

(*******************************************************************)
(* <group> has <choice> as children.*)
(*******************************************************************)

(*******************************************************************)
(* Return type inside a group choice has one children.
   At pattern [x]: For debug information: this is of type [strategy;
   tupleOrder].*)

let group_choice_one_child_type tn b = function
  | Elt (n, Some (Choice []), _, _) | Elt (n, None, _, _) ->
    bprintf b "| Element (\"%s\", _, _, _) -> %s\n\ "
      n (constructor_name tn n)
  | Elt (n, Some t, _, _) -> (* FIXME *)
    begin match t with
      (* [complexityClass] *)
      | SimpleType sn ->
	if   sn = undefine sn
        then bprintf b "| Element (\"%s\", _, _, xs) ->\n        \
                 let item_%s, xs = parse_first_elt %s xs in\n       \
                 check_emptyness xs;\n         \
                 item_%s\n\ "
	    n sn sn sn
	else bprintf b "| Element (\"%s\", _, _, xs) ->\n        \
                 let item_%s, xs = parse_first_elt %s_val xs in\n       \
                 check_emptyness xs;\n         \
                 item_%s\n\ "
	        n n sn n (* FIXME  ......*) (* [function] *)
      | _ -> todo b
    end
  | _ -> todo b;;

(* <choice> has one children *)

let group_choice_one_child b n x =
  let k = keywords n in
  bprintf b "%s x = get_first_son \"%s\" %s_val x \n\n\
             and %s_val x = match x with          \n   \
             %a  \
             | x -> error_xml x \"not %s %s\""
    k n n n (group_choice_one_child_type n) x (a_an n) n;;

(*******************************************************************)
(* Return type of group has more than one children *)

(* Inside a group choice, <sequence> is their children 
   CPF version 2.1, in the case of "Lhs_symbol"*)

let group_choice_sequence_child b tn xs = 
  let aux = function
    | Choice _ -> false
    | _        -> true
  in
  let xs = List.filter aux xs in
     bprintf b "| Element (\"%s\", _, _, xs) -> " tn;
       list "      " (type_sequences tn "") b xs;
     bprintf b "\n        check_emptyness xs;\n";
     let aux b = function
       | Elt (n, _, _, _)
       | GroupRef (n, _, _) -> bprintf b "item_%s" n
       | _                  -> assert false
     in bprintf b "        %s (%a)" (constructor_name tn tn) (list ", " aux) xs;;

(* Inside a group choice, <element> is their children.
   - simple type name = undefined name: For debug information: [number] type
   - In the case the tag name is equal to the type name. This is
   different than [type_choices] function the [Element]
   requires a list of [xs]. *)

let group_choice_elem_child b tn n t =
  match t with
    | SimpleType sn -> 
      if   sn = undefine n
      then bprintf b "| Element (\"%s\", _, _, xs) ->\n        \
                  let item_%s, xs = parse_first_elt %s xs in \n        \
                  check_emptyness xs;\n        \
                  %s item_%s" n sn sn (constructor_name tn n) sn
      else
        if   sn = n
        then bprintf b "| Element (\"%s\", _, _, xs) -> %s (%s_val xs)"
	       n (constructor_name tn n) n
        else bprintf b "| Element (\"%s\", _, _, xs) -> %a"
	       n (sequence_in_choice n tn) t
    | x -> bprintf b "| Element (\"%s\", _, _, xs) -> %a"
             n (sequence_in_choice n (constructor_name tn n)) x;;

(* Return type of group has more than one children *)

let group_choice_more_child_type tn b = function
  | Elt (n, Some (Choice []), _, _)
  | Elt (n, None, _, _)   -> bprintf b "| Element (\"%s\", _, _, _) -> %s"
      n (constructor_name tn n)
  | Elt (n, Some t, _, _) -> group_choice_elem_child b tn n t
  | Sequence xs           -> group_choice_sequence_child b tn xs
  | _                     -> bprintf b "group choices todo";;

(* <choice> has more than one children *)

let group_choice_more_child b n xs =
  let k = keywords n in
  bprintf b "%s x = get_first_son \"%s\" %s_val x \n\n\
             and %s_val x = match x with          \n   \
             %a                                 \n   \
             | x -> error_xml x \"not %s %s\""
    k n n n ((list "\n   ")(group_choice_more_child_type n)) xs (a_an n) n;;

(*******************************************************************)
(* <group> has <choice> as children *)

let genr_group_choice b n xs =
  match xs with
    | []           -> ()
    | [x]          -> group_choice_one_child b n x
    | xs -> group_choice_more_child b n xs

(*******************************************************************)
(* generate parsing function for <group> *)

let genr_type_group b t n =
  match t with
    | Sequence _ as xs -> genr_group_sequence b n xs
    | Choice xs        -> genr_group_choice b n xs
    | _                -> bprintf b "group todo";;

(*******************************************************************)
(* Generate parsing function *)
(*******************************************************************)

let genr_type b = function
  | Elt (n, Some t, _, _)   -> genr_type_elem b n t
  | Group (n, Some t, _, _) -> genr_type_group b t n
  | _                       -> todo b;;

(*****************************************************************************)
(* Print function *)

let rec genr_and_parsers b =
  try bprintf b "\n\nand %a"
      genr_type (next_type());
      genr_and_parsers b
  with Not_found -> ();;

let genr_types b xsds =
  init_types xsds;
  try  bprintf b "let rec %a"
       genr_type (next_type());
       genr_and_parsers b
  with Not_found -> ();;

(*****************************************************************************)
(* Main function generate XSD data to OCaml function. *)

let genr_ml b xsds =
  let xsds         = flatten_innerchoice xsds            in
  let xsds_sorted  = List.flatten (xsds_sorted_fun xsds) in
  bprintf b
    "(* DO NOT MODIFY THIS FILE. IT HAS BEEN AUTOMATICALLY GENERATED *)\n\n\
     open Xml;;\n\
     open Error;;\n\
     open Libxml;;\n\
     open Cpf0;;\n\n\
     (**************************************************************)\n\
     (* functions converting an XML value into a CPF value *)\n\
     (**************************************************************)\n\n\
     (**************************************************************)\n\
     (* check that an element's tag satisfies f *)\n\
     let is_elt f = function\n\
       | Element (t, _, _, _) -> f t\n\
       | PCData _ -> false;;\n\n\
     let is_number_tag = function\n\
       | \"integer\" | \"rational\" -> true\n\
       | _ -> false;;\n\n\
     let is_number = is_elt is_number_tag;;\n\n\
     let long = get_int;;\n\n\
     %a\n\n\
     and before xs = get_sons \"before\" before_val xs \n\n\
     and before_val xs =\n      \
     let item_term, xs = parse_list term_val xs in\n        \
     check_emptyness xs;\n       \
     (item_term)\n\n\
     and after xs = get_sons \"after\" after_val xs \n\n\
     and after_val xs =\n      \
     let item_term, xs = parse_list term_val xs in\n        \
     check_emptyness xs;\n       \
     (item_term);;\n\ "
    genr_types xsds_sorted;;

