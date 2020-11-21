(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-10-20

Generate an Coq type from an xsd value.
******************************************************************************)

(* REMARK: The code below for cpf.xsd version 2.1. *)

open Util;;
open Xsd;;
open Printf;;
open Scc;;

let todo b = string b "todo";;

(******************************************************************************)
(* [2] In the case the leaf is a [Sequence], then it has two cases: 
   [A]: In the branch has only one element. [type_sequence].
   [B]: In the branch has a list of elements. [type_sequences] *)

let rec type_sequences _ b = function
  | SimpleType n
  | GroupRef (n, 1, Bound 1)      -> Util.string b                          n
  | GroupRef (n, 0, Bound 1)      -> bprintf b "option %s"                  n
  | GroupRef (n, _, _)            -> bprintf b "list %s"                    n
  | Elt (_, None, _, _)           -> bprintf b "option boolean"
  | Elt (n, Some t, _, Unbounded) -> bprintf b "list %a"   (par_of_sequence n) t
  | Elt (n, Some t, 0, Bound 1)   -> bprintf b "option %a" (par_of_sequence n) t
  | Elt (n, Some t, 1, Bound 1)   -> bprintf b "%a"        (par_of_sequence n) t
  | Sequence xs ->
    let aux = function
      | Choice _ -> false
      | _        -> true
    in
    list " * " (fun b x -> type_sequences (name_of_elt x) b x) b
      (List.filter aux xs)
  | _ -> todo b

and par_of_sequence tn b = function
  | SimpleType n
  | GroupRef (n, 1, Bound 1) -> Util. string b n
  | x                        -> bprintf b "(%a)" (type_sequences tn) x;;

(* [type_sequence] is the print function in the case of [Sequence]
   where it has one element in the list. This is in the case of
   [matrix] and [vector] where I need to print [matrix] and [vector]
   and [coefficient] as an [Inductive... with] type. *)
 
let type_sequence tn b = function
  | Elt (_, Some t, 1, Unbounded) ->
    (match t with
      | Sequence _ as x -> bprintf b "Definition %s := list (%a)."
                             tn (type_sequences tn) x
      (* For debug information: argumentFilter; subsitution type. *)
      | SimpleType sn -> (* TODO *)
	(* This is the case of [matrix-vector-coefficient]. Other
	   type also has the same constructor but need to print as a
	   [Definition] (usableRules; trs; dps). *)
	if tn = "matrix"
        then bprintf b "Inductive %s :=\n\
                        | %s : list (list coefficient) -> %s\
                        "
               tn (constructor_name tn tn) tn
	else
          if   tn = "vector"
          then bprintf b "with %s :=\n\
                          | %s : list %s -> %s\
                         "
                 tn (constructor_name tn tn) sn tn
	  else bprintf b "Definition %s := %a. "
                 tn (type_sequences tn) t
      | _ -> todo b)
  | x -> bprintf b "Definition %s := %a." tn (type_sequences tn) x;;
        (* For debug information: this is in the case of [rules] type. *)

(******************************************************************************)
(* [3] The leaf is a [Choice], then it has two cases:

   [a] First one is only one element in this leaf. Corresponding to
   the function [type_choice].

   [b] Second case is a list of choices. Function [type_choices]. In
   this case each branch will become an constructor in COQ type. *)

let rec sequence_in_choice _ b = function
  | SimpleType n
  | GroupRef (n, 1, Bound 1)      -> Util.string b                          n
  | GroupRef (n, 0, Bound 1)      -> bprintf b "option %s"                  n
  | GroupRef (n, _, _)            -> bprintf b "list %s"                    n
  | Elt (_, None, _, _)           -> bprintf b "option boolean"
  | Elt (n, Some t, _, Unbounded) -> bprintf b "list %a"   (par_of_sequence n) t 
  | Elt (n, Some t, 0, Bound 1)   -> bprintf b "option %a" (par_of_sequence n) t
  | Elt (n, Some t, 1, Bound 1)   -> bprintf b "%a"        (par_of_sequence n) t
  | Sequence xs ->
    let aux = function
      | Choice _ -> false
      | _        -> true
    in
    list " -> "
      (fun b x -> sequence_in_choice (name_of_elt x) b x) b (List.filter aux xs)
  | _ -> todo b

let type_in_choice tn b = function
  | Elt (n, Some (Choice []), _, _)
  | Elt (n, None, _, _)   -> bprintf b "\n| %s"            
   (constructor_name tn n)
  | GroupRef (n, _, _)    -> bprintf b "\n| %s : %s -> %s"
    (constructor_name tn n) n tn
  | Elt (n, Some t, _, _) -> bprintf b "\n| %s : %a -> %s"
    (constructor_name tn n) (sequence_in_choice n) t tn
  | Sequence xs -> (* REMARK *)
    (* CPF version 2.1, in the case of "Lhs_symbol" *)
    let aux = function
      | Choice _ -> false
      | _        -> true
    in
    bprintf b  "\n| %s: " (constructor_name tn tn);
      list "-> " (fun b x -> type_sequences (name_of_elt x) b x) b
	(List.filter aux xs);
      bprintf b "-> %s" tn
  | _ -> todo b;;
    
(* [b] A list of choices *)

let type_choices tn b = function
  | Choice xs -> list "" (type_in_choice tn) b xs
  | _         -> todo b;; (* TODO? in type_def *)

(* [A] Only one element *)

let type_choice tn b = function
  | Elt (n, Some (Choice []), _, _)
  | Elt (n, None, _, _)   -> bprintf b "Inductive %s : Set := %s."
                               tn (constructor_name tn n)
  | Elt (n, Some t, _, _) ->
    begin match t with
      | SimpleType sn ->
	(* [function], [complexityClass] *)
	bprintf b "Definition %s := %s. " tn sn
      | Sequence xs   ->
	(* REMARK: CPF version 2.1 is the branch [quasiReductionProof]. *)
	let aux = function
	  | Choice _ -> false
	  | _        -> true
	in
	bprintf b "Inductive %s := \n   \
                    | %s : " tn (constructor_name tn n);
   	 list " -> " (fun b x -> type_sequences (name_of_elt x) b x) b
           (List.filter aux xs);
	bprintf b " -> %s." tn
      | _ -> todo b
    end
  | _ -> todo b;;

(* Choice with one constructor where it roots is an Elt. *)

let elt_type_choice tn b = function
  | Elt (n, Some (Choice []), _, _)
  | Elt (n, None, _, _)   -> bprintf b "Inductive %s : Set := %s."
                               tn (constructor_name tn n)
  | Elt (n, Some t, _, _) ->
    begin match t with
      | SimpleType _ -> bprintf b "Inductive %s := \n | %s : %s -> %s."
 	                  tn (constructor_name tn n) n tn
      | Sequence xs  ->
	let aux = function
	  | Choice _ -> false
	  | _        -> true
	in
	bprintf b "Inductive %s := \n   \
                    | %s : " tn (constructor_name tn n);
	  list " -> "
           (fun b x -> type_sequences (name_of_elt x) b x) b
	    (List.filter aux xs);
	bprintf b " -> %s." tn
      | _ -> todo b
    end
  | _ -> todo b;;

(* SimpleType: COQ definition [Definition]. 
   Sequence  : COQ definition [Definition].
   Choice    : COQ definition [Inductive]. *)

let genr_type b = function
  | Elt (n, Some t, _, _) ->
    begin match t with
      | SimpleType sn     -> bprintf b "Definition %s := %s." n sn
      | Sequence xs       ->
	(match xs with
	  | []      -> ()
	  | [x]     ->
	  (* In the case it is a sequence and it has one element, print
	     it as a [Definition] call to the function [type_sequence]. *)
	    type_sequence n b x
	  | _ :: _ -> (* TODO *)
	    (* TODO: Version 2.1 patternRule: t5 calls patternRule
	       and patternRule calls t5 *)
	    if   n = "patternRule"
            then bprintf b
	      "with patternRule :=\n  \
                | PatternRule_patternRule : (patternTerm * patternTerm * t5) ->\
                 patternRule."
       	    else
	      (* In the case it is a list, then print [Definition] and
		 call to the function to generate type for this
		 [Definition] type [type_sequences].
		 Remark: print '.' at the end. *)
	      bprintf b "Definition %s := %a." n (type_sequences n) t)
      | Choice xs   ->
	(match xs with
	  | []     -> ()
	  | [x]    ->
	  (* In the case it is a choice and it has one element, print
	     it as a [Definition] instead of [Inductive] with one
	     constructor. Call to the function [type_choice] *)
	    elt_type_choice n b x
	  | _ :: _ -> (* TODO *)
	    (* In the case it is a list, then print [Inductive] and call
	       to the function to generate type for this [Inductive]
	       type [type_choices].
	       Remark: print '.' at the end.*)
	    (* REMARK: because of [coefficient] type depend on the type
	       of [matrix - vector] and this is a special case to print. *)
	    if   n = "coefficient"
            then bprintf b "with %s := %a."      n (type_choices n) t
	    else bprintf b "Inductive %s := %a." n (type_choices n) t)
      | _ -> assert false
    end
  | Group (n, Some t, _, _) ->
    begin match t with
      | Choice xs ->
	(match xs with
	  | []     -> ()
	  | [x]    ->
	  (* In the case it is a choice and it has one element, print
	     it as a [Definition] instead of [Inductive] with one
	     constructor. Call to the function [type_choice] *)
	    type_choice n b x
	  | _ :: _ -> (* TODO *)
	      (* REMARK: this is a type of [symbol - label] these two
		 types are depend to each others. It needs a special
		 print in COQ type as [Inductive ... with]. (For debug
		 information: in XSD the top level is [Group...]) *)
	    if   n = "symbol"
            then bprintf b "Inductive %s := %a"      n (type_choices n) t
            else
              if   n = "label"
              then bprintf b "with %s := %a."        n (type_choices n) t
	      else
		if   n = "t5"
                then bprintf b "Inductive %s := %a"  n (type_choices n) t
		else bprintf b "Inductive %s := %a." n (type_choices n) t)
      | _ -> todo b
    end

  | _ -> todo b;;

let print_types b xsds =
  List.iter (function
    | []     -> assert false
    | h :: t -> bprintf b "%a" genr_type h;
                List.iter (fun xsd -> bprintf b "\n\n%a" genr_type xsd) t) xsds;;

(* [genr_types] is a priting function for a whole list [xsds]. *)

let genr_types b xsds = print_types b xsds;;

(**********************************************************************)

let num_of_name defined undefined len_undefined s =
  try
     let p = position s defined in
       Some (p + len_undefined)
  with Not_found   -> 
    try
      let p = position s undefined in
         Some p
    with Not_found -> None
 
(* funtion taking a position of xsds list and undefined list, return
   their element *)

let name_of_num xsds undefined len_undefined k =
  if   k < len_undefined
  then List.nth undefined k
  else List.nth xsds (k - len_undefined)

let coq_xsd_types =
  [ "nonNegativeInteger", "N";
    "integer",            "Z";
    "positiveInteger",    "positive";
    "long",               "Z";
    "boolean",            "bool" ];;

(* an undefined list is an list that does not has a definition in xsd type *)

let undefined     = List.map fst coq_xsd_types;;
 
let len_undefined = List.length undefined;;
  
(* build an undefined list into an xsds data types*)

let builtin_undefined_types =
  let xsd_of_type (n, d) = Elt (n, Some (SimpleType d), 1, Bound 1) in
    List.map xsd_of_type coq_xsd_types;;

let defined xsds = List.map name_of_elt xsds;;

(* transform an xsds to boolean matrix by using an pair of xsds
   (string, string list) list, if they have a connection between them
   then return true, otherwise return false *)

let matrix xsds =
  let pair_xsds = get_list_xsds xsds                         in
  let len       = List.length (defined xsds) + len_undefined in
  let boolmat   = Array.make_matrix len len false            in
  List.iter (fun (s, strs) ->
    match num_of_name (defined xsds) undefined len_undefined s     with
      | Some pos1 -> List.iter (fun t ->
        match num_of_name (defined xsds) undefined len_undefined t with
          | Some pos2 -> boolmat.(pos1).(pos2) <- true
          | None      -> ()) strs
      | None               -> ()
  ) pair_xsds;
  boolmat

let closure_matrix   xsds = transClosure (matrix xsds)

let line_matrix      xsds = linearize (closure_matrix xsds)

let equivalence      xsds = eq_classes (line_matrix xsds)

let sort_equivalence xsds = sort_eq_classes (line_matrix xsds)
                            (List.flatten (equivalence xsds))

let xsds_of_int xsds = List.map (List.map
  (name_of_num xsds builtin_undefined_types len_undefined))

let xsds_sorted xsds = xsds_of_int xsds [(sort_equivalence xsds)];;

let genr_coq b xsds =
  let xsds          = flatten_innerchoice xsds in
  let xsds_sorted   = xsds_sorted xsds         in
  bprintf b
    "(* DO NOT MODIFY THIS FILE. IT HAS BEEN AUTOMATICALLY GENERATED *)\n\n\
     Set Implicit Arguments.\n\
     Require Import ZArith String Int31.\n\
     Open Local Scope type_scope.\n\
     (**************************************************************)\n\
     (* Describing CPF type in Coq type *)\n\
     (**************************************************************)\n\n\
     %a\n\n"
    genr_types xsds_sorted;;
