(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

from xml to the rainbow internal representation of termination problems
******************************************************************************)

open Problem;;
open Xml;;
open Libxml;;
open Error;;

(*****************************************************************************)
(* Symbols, terms and words *)
(*****************************************************************************)

let is_identifier _s = (*FIXME*) true;;

(*UNUSED:
let identifier x =
  let s = get_pc x in
    if is_identifier s then s else error_xml x "not an identifier";;*)

let rec symbol = function
  | PCData (s, _) when is_identifier s -> Ident s
  | Element ("hd_mark", _, _, x :: _) -> Hd (symbol x)
  | Element ("int_mark", _, _, x :: _) -> Int (symbol x)
  | Element ("labelled_symbol", _, _, x :: xs) ->
      Label (fun_symbol x, List.map (get_first_son "label" fun_symbol) xs)
  | x -> error_xml x "not a symbol"

and fun_symbol x = get_first_son "fun" symbol x;;

let rec term = function
  | Element ("var", _, _, x :: _) -> Var (get_nonNegativeInteger x)
  | Element ("app", _, _, x :: xs) ->
      App (fun_symbol x, List.map (get_first_son "arg" term) xs)
  | x -> error_xml x "not a term";;

let rec letter = function
  | PCData (s, _) when is_identifier s -> Ident s
  | Element ("labelled_letter", _, _, x :: xs) ->
      Label (fun_letter x, List.map (get_first_son "label" fun_letter) xs)
  | x -> error_xml x "not a letter"

and fun_letter x = get_first_son "letter" letter x;;

let word = List.map fun_letter;;

(*****************************************************************************)
(* Rewrite rules *)
(*****************************************************************************)

let norm_or_join = function
  | Element ("norm", _, _, _) -> Norm
  | Element ("join", _, _, _) -> Join
  | x -> error_xml x "not a condition";;

let lhs = get_first_son "lhs" term;;
let rhs = get_first_son "rhs" term;;

let condition = function
  | Element ("if", _, _, x1 :: x2 :: x3 :: _) ->
      { cond_lhs = lhs x1;
	cond_test = norm_or_join x2;
	cond_rhs = rhs x3 }
  | x -> error_xml x "not a condition";;

let trsRule = function
  | Element ("rule", _, _, x1 :: x2 :: xs) ->
      { trs_lhs = lhs x1; trs_rhs = rhs x2;
	trs_conds = List.map condition xs }
  | x -> error_xml x "not a trsRule";;

let trsRules = List.map trsRule;;

let srsRule = function
  | Element ("rule", _, _, x1 :: x2 :: _) ->
      { srs_lhs = get_sons "lhs" word x1;
	srs_rhs = get_sons "rhs" word x2 }
  | x -> error_xml x "not an srsRule";;

let srsRules = List.map srsRule;;

(*****************************************************************************)
(* Strategies *)
(*****************************************************************************)

let replacementMapping = function
  | Element ("mapping", _, _, x :: xs) ->
    fun_symbol x, List.map (get_first_son "index" get_positiveInteger) xs
  | x -> error_xml x "not a replacementMapping";;

let replacementMap = map_of_list replacementMapping;;

let trsStrategy = function
  | Element ("none", _, _, _) -> None
  | Element ("innermost", _, _, _) -> Some Innermost
  | Element ("outermost", _, _, _) -> Some Outermost
  | Element ("context_sensitive", _, _, xs) ->
      Some (ContextSensitive (replacementMap xs))
  | x -> error_xml x "not a trsStrategy";;

let srsStrategy = function
  | Element ("none", _, _, _) -> None
  | Element ("leftmost", _, _, _) -> Some Leftmost
  | Element ("rightmost", _, _, _) -> Some Rightmost
  | x -> error_xml x "not an srsStrategy";;

(*****************************************************************************)
(* Theories *)
(*****************************************************************************)

let c_or_ac = function
  | Element ("commutative", _, _, _) -> Commutative
  | Element ("associative", _, _, _) -> Associative
  | Element ("associative_commutative", _, _, _) -> AssociativeCommutative
  | x -> error_xml x "not a builtin";;

let axiom = function
  | Element ("builtin", _, _, x1 :: x2 :: _) ->
      Builtin (fun_symbol x1, c_or_ac x2)
  | Element ("equation", _, _, x1 :: x2 :: _) -> Equation (lhs x1, rhs x2)
  | x -> error_xml x "not an axiom";;

let theory = List.map axiom;;

(*****************************************************************************)
(* Signatures *)
(*****************************************************************************)

let arityMapping = function
  | Element ("mapping", _, _, x1 :: x2 :: _) ->
      fun_symbol x1, get_first_son "arity" get_nonNegativeInteger x2
  | x -> error_xml x "not an arityMapping";;

let signature = map_of_list arityMapping;;

let algebra = function
  | Element ("varyadic", _, _, _) -> Varyadic
  | Element ("signature", _, _, xs) -> Signature (signature xs)
  | x -> error_xml x "not an algebra";;

(*****************************************************************************)
(* Termination problems *)
(*****************************************************************************)

let problemKind = function
  | Element ("trs", _, _, x1 :: x2 :: x3 :: x4 :: x5 :: _) ->
      let le_rules = get_sons "le_rules" trsRules x4
      and rules = get_sons "rules" trsRules x5 in
	Trs { trs_symbols = symb_set_of_list symbols_of_trs_rule
	                    (le_rules @ rules) SymbSet.empty;
	      trs_algebra = get_first_son "algebra" algebra x1;
	      trs_axioms = get_sons "theory" theory x2;
	      trs_strategy = get_first_son "strategy" trsStrategy x3;
	      trs_le_rules = le_rules;
	      trs_rules = rules }
  | Element ("srs", _, _, x1 :: x2 :: x3 :: _) ->
      let le_rules = get_sons "le_rules" srsRules x2
      and rules = get_sons "rules" srsRules x3 in
	Srs { srs_symbols = symb_set_of_list symbols_of_srs_rule
	                   (le_rules @ rules) SymbSet.empty;
	      srs_strategy = get_first_son "strategy" srsStrategy x1;
	      srs_le_rules = le_rules;
	      srs_rules = rules }
  | x -> error_xml x "not a problemKind";;

let problem = function
  | Element ("problem", _, _, x :: _) -> problemKind x
  | x -> error_xml x "not a problem";;
