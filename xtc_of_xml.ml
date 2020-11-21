(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-09-04

internal representation of XTC files version 0.4
******************************************************************************)

open Xtc;;
open Xml;;
open Util;;
open Libxml;;
open Error;;

let bound_of_string = function
  | "?" -> BoundUnknown
  | "POLY" -> BoundPoly
  | "O(1)" -> BoundOn 0
  | s -> BoundOn (Scanf.sscanf s "O(%d)" (fun x -> x));;

let get_bound x =
  try bound_of_string (get_pc x)
  with Scanf.Scan_failure _ -> error_xml x "not a bound";;

let bound t = get_first_son t get_bound;;

let lowerbound = bound "lowerbound";;
let upperbound = bound "upperbound";;

let automaton = get_first_son "automatonstuff" get_pc;;

let startterm = function
  | Element ("constructor-based", _, _, _) -> STConstructorBased
  | Element ("full", _, _, _) -> STFull
  | Element ("automaton", _, _, x :: _) -> STAutomaton (automaton x)
  | (Element _ | PCData _) as x -> error_xml x "not a startterm";;

let get_int x =
  try Pervasives.int_of_string (get_pc x)
  with Scanf.Scan_failure _ -> error_xml x "not an integer";;

let entry = get_first_son "entry" get_int;;

let replacementmap = List.map entry;;

let name = get_first_son "name" get_pc;;
let var = get_first_son "var" get_pc;;

let rec get_typ = function
  | Element ("basic", _, _, x :: _) -> TypeBasic (get_pc x)
  | Element ("arrow", _, _, x1 :: x2 :: _) -> TypeArrow (typ x1, typ x2)
  | (Element _ | PCData _) as x -> error_xml x "not a type element"

and typ x = get_first_son "type" get_typ x;;

let rec term = function
  | Element ("var", _, _, x :: _) -> TermVar (get_pc x)
  | Element ("funapp", _, _, x :: xs) -> TermFunapp (name x, List.map arg xs)
  | Element ("application", _, _, x1 :: x2 :: _) -> TermApp (term x1, term x2)
  | Element ("lambda", _, _, x1 :: x2 :: x3 :: _) ->
      TermLam (var x1, typ x2, term x3)
  | (Element _ | PCData _) as x -> error_xml x "not a term"

and arg x = get_first_son "arg" term x;;

let lhs = get_first_son "lhs" term;;
let rhs = get_first_son "rhs" term;;

let comment_attributes x =
  let rec aux a d = function
    | [] -> a, d
    | ("author", a') :: l -> aux (Some a') d l
    | ("date", d') :: l -> aux a (Some d') l
    | _ :: l -> aux a d l
  in fun l -> match aux None None l with
    | Some a, Some d -> a, d
    | _, _ -> error_xml x "no author or date attribute";;

let condition = function
  | Element ("condition", _, _, x1 :: x2 :: _) -> lhs x1, rhs x2
  | (Element _ | PCData _) as x -> error_xml x "not a condition";;

let conditions = get_sons "conditions" (List.map condition);;

let rule = function
  | Element ("rule", _, _, x1 :: x2 :: []) -> lhs x1, rhs x2, []
  | Element ("rule", _, _, x1 :: x2 :: x3 :: _) ->
      lhs x1, rhs x2, conditions x3
  | (Element _ | PCData _) as x -> error_xml x "not a rule";;

let metainformation =
  let rec aux ofns a d c = function
    | [] -> ofns, a, d, c
    | Element ("originalfilename", _, _, x :: _) :: xs ->
	aux (get_pc x :: ofns) a d c xs
    | Element ("author", _, _, x :: _) :: xs -> aux ofns (get_pc x) d c xs
    | Element ("date", _, _, x :: _) :: xs -> aux ofns a (get_pc x) c xs
    | Element ("comment", _, l, c) as x :: xs ->
	aux ofns a d (Some (comment_attributes x l, c)) xs
    | (Element _ | PCData _) as x :: _ ->
	error_xml x "not a metainformation element"
  in aux [] "" "" None;;

let status = function
  | Element ("no", _, _, _) -> StatusNo
  | Element ("maybe", _, _, _) -> StatusMaybe
  | Element ("yes", _, _, []) -> StatusYes None
  | Element ("yes", _, _, x1 :: x2 :: _) ->
      StatusYes (Some (lowerbound x1, upperbound x2))
  | (Element _ | PCData _) as x -> error_xml x "not a status";;

let strategy_of_string = function
  | "FULL" -> StratFull
  | "INNERMOST" -> StratInnermost
  | "OUTERMOST" -> StratOutermost
  | s -> raise (Scanf.Scan_failure s);;

let get_strategy x =
  try strategy_of_string (get_pc x)
  with Scanf.Scan_failure _ -> error_xml x "not a strategy";;

let strategy = get_first_son "strategy" get_strategy;;

let conditiontype_of_string = function
  | "JOIN" -> CTJoin
  | "ORIENTED" -> CTOriented
  | "OTHER" -> CTOther
  | s -> raise (Scanf.Scan_failure s);;

let get_conditiontype x =
  try conditiontype_of_string (get_pc x)
  with Scanf.Scan_failure _ -> error_xml x "not a conditiontype";;

(*UNUSED:let conditiontype = get_first_son "conditiontype" get_conditiontype;;*)

let theory_of_string = function
  | "A" -> ThyA
  | "C" -> ThyC
  | "AC" -> ThyAC
  | s -> raise (Scanf.Scan_failure s);;

let get_theory x =
  try theory_of_string (get_pc x)
  with Scanf.Scan_failure _ -> error_xml x "not a theory";;

(*UNUSED:let theory = get_first_son "theory" get_theory;;*)

let arity = get_first_son "arity" get_int;;

let rec funcsym_aux t rm = function
  | [] -> t, rm
  | Element ("theory", _, _, x :: _) :: xs ->
      funcsym_aux (get_theory x) rm xs
  | Element ("replacementmap", _, _, xs') :: xs ->
      funcsym_aux t (Some (replacementmap xs')) xs
  | (Element _ | PCData _) as x :: _ ->
      error_xml x "not a funcsym element";;

let funcsym = function
  | Element ("funcsym", _, _, x1 :: x2 :: xs) ->
      let t, rm = funcsym_aux ThyNone None xs in name x1, arity x2, t, rm
  | (Element _ | PCData _) as x -> error_xml x "not a funcsym";;

(*UNUSED:let firstOrderSignature = get_sons "signature" (List.map funcsym);;*)

let varDeclaration = function
  | Element ("varDeclaration", _, _, x1 :: x2 :: _) -> var x1, typ x2
  | (Element _ | PCData _) as x ->
      error_xml x "not a varDeclaration element";;

let variableTypeInfo = get_sons "variableTypeInfo" (List.map varDeclaration);;

let typeDeclaration = function
  | Element ("typeDeclaration", _, _, x :: xs) -> map_split_last typ x xs
  | (Element _ | PCData _) as x ->
      error_xml x "not a typeDeclaration element";;

let funcDeclaration = function
  | Element ("funcDeclaration", _, _, x1 :: x2 :: _) ->
      name x1, typeDeclaration x2
  | (Element _ | PCData _) as x ->
      error_xml x "not a funcDeclaration element";;

let functionSymbolTypeInfo =
  get_sons "functionSymbolTypeInfo" (List.map funcDeclaration);;

let signature = function
  | Element ("signature", _, _, xs) -> SignFO (List.map funcsym xs)
  | Element ("higherOrderSignature", _, _, x1 :: x2 :: _) ->
      SignHO (variableTypeInfo x1, functionSymbolTypeInfo x2)
  | (Element _ | PCData _) as x ->
      error_xml x "not a signature element";;

let relrules = List.map rule;;

let rec rules_aux rs rels = function
  | [] -> rs, rels
  | Element ("rule", _, _, _) as x :: xs -> rules_aux (rule x :: rs) rels xs
  | Element ("relrules", _, _, xs) :: _ -> rs, relrules xs
  | (Element _ | PCData _) as x :: _ -> error_xml x "not a rules element";;

let rules = get_sons "rules" (rules_aux [] []);;

let rec trs_aux c ct = function
  | [] -> c, ct
  | Element ("comment", _, l, c) as x :: xs ->
      trs_aux (Some (comment_attributes x l, c)) ct xs
  | Element ("conditiontype", _, _, x :: _) :: xs ->
      trs_aux c (get_conditiontype x) xs
  | (Element _ | PCData _) as x :: _ -> error_xml x "not a trs element";;

let trs = function
  | Element ("trs", _, _, x1 :: x2 :: xs) ->
      let c, ct = trs_aux None CTNone xs in rules x1, signature x2, c, ct
  | (Element _ | PCData _) as x -> error_xml x "not a trs";;

let rec problem_aux st s mi = function
  | [] -> st, s, mi
  | Element ("startterm", _, _, x :: _) :: xs ->
      problem_aux (startterm x) s mi xs
  | Element ("status", _, _, x :: _) :: xs ->
      problem_aux st (status x) mi xs
  | Element ("metainformation", _, _, ys) :: xs ->
      problem_aux st s (Some (metainformation ys)) xs
  | (Element _ | PCData _) as x :: _ -> error_xml x "not a problem element";;

let xtc_type x = function
  | "termination" -> Term
  | "complexity" -> Comp
  | _ -> error_xml x "invalid type attribute value";;

let problem_attribute x =
  let rec aux t = function
    | [] -> t
    | ("type", t') :: l -> aux (Some (xtc_type x t')) l
    | (_, _) :: l -> aux t l
  in fun l -> match aux None l with
    | Some t -> t
    | _ -> error_xml x "no type attribute";;

let problem = function
  | Element ("problem", _, l, x1 :: x2 :: xs) as x ->
      let st, s, mi = problem_aux STNone StatusNone None xs in
	problem_attribute x l, trs x1, strategy x2, st, s, mi
  | (Element _ | PCData _) as x -> error_xml x "not a problem";; 
