(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31
- Adam Koprowski, 2007-04-20, adding matrix interpretations
- Ducas Leo, 2007-08-10

from xml to the rainbow internal representation of termination proofs
******************************************************************************)

open Proof;;
open Xml;;
open Pb_of_xml;;
open Libxml;;
open Error;;

(*****************************************************************************)
(* Number, vectors and matrices *)
(*****************************************************************************)

let arcticNumber = function
  | Element ("minus_infinite", _, _, _) -> MinusInf
  | Element ("finite", _, _, x :: _) -> Fin (get_int x)
  | x -> error_xml x "not an arcticNumber";;

let tropicalNumber = function
  | Element ("plus_infinite", _, _, _) -> PlusInf
  | Element ("finite", _, _, x :: _) -> TroFin (get_int x)
  | x -> error_xml x "not a tropicalNumber";;

let natVector = List.map (get_first_son "velem" get_nonNegativeInteger);;

let arcticVector = List.map (get_first_son "velem" arcticNumber);;
let tropicalVector = List.map (get_first_son "velem" tropicalNumber);;

let natMatrix = List.map (get_sons "row" natVector);;

let arcticMatrix = List.map (get_sons "row" arcticVector);;
let tropicalMatrix = List.map (get_sons "row" tropicalVector);;

(*****************************************************************************)
(* Polynomials *)
(*****************************************************************************)

let monomial = function
  | Element ("monomial", _, _, x :: xs) ->
      get_first_son "coef" get_nonNegativeInteger x,
      List.map (get_first_son "var" get_nonNegativeInteger) xs
  | x -> error_xml x "not a monomial";;

let polynomial = get_sons "polynomial" (List.map monomial);;

(*****************************************************************************)
(* Polynomial and matrix interpretations *)
(*****************************************************************************)

let polynomialMapping = function
  | Element ("mapping", _, _, x1 :: x2 :: _) -> fun_symbol x1, polynomial x2
  | x -> error_xml x "not a polynomialMapping";;

let dimension = get_first_son "dimension" get_positiveInteger;;

let funMatrixInterpretation = function
  | Element ("mi_fun", _, _, x :: xs) ->
      { mi_const = get_sons "const" natVector x;
	mi_args = List.map (get_sons "arg" natMatrix) xs }
  | x -> error_xml x "not a funMatrixInterpretation";;

let matrixMapping = function
  | Element ("mapping", _, _, x1 :: x2 :: _) ->
      fun_symbol x1, funMatrixInterpretation x2
  | x -> error_xml x "not a matrixMapping";;

let mi_map f = get_sons "mi_map" (List.map f);;

let funArcticInterpretation = function
  | Element ("mi_fun", _, _, x :: xs) ->
      { mi_const = get_sons "const" arcticVector x;
	mi_args = List.map (get_sons "arg" arcticMatrix) xs }
  | x -> error_xml x "not a funArcticInterpretation";;

let funTropcialInterpretation = function
  | Element ("mi_fun", _, _, x :: xs) ->
      { mi_const = get_sons "const" tropicalVector x;
	mi_args = List.map (get_sons "arg" tropicalMatrix) xs }
  | x -> error_xml x "not a funTropicalInterpretation";;

let arcticMapping = function
  | Element ("mapping", _, _, x1 :: x2 :: _) ->
      fun_symbol x1, funArcticInterpretation x2
  | x -> error_xml x "not an arcticMapping";;

let tropicalMapping = function
  | Element ("mapping", _, _, x1 :: x2 :: _) ->
      fun_symbol x1, funTropcialInterpretation x2
  | x -> error_xml x "not a tropicalMapping";;

(*****************************************************************************)
(* Argument filterings *)
(*****************************************************************************)

let get_bool = function
  | Element ("true",_, _, _) -> true
  | Element ("false",_, _, _) -> false
  | x -> error_xml x "not a boolean";;

let vectorBool = List.map get_bool;;

let argBoolMapping = function
  | Element ("mapping", _, _, x1 :: x2 :: _) ->
      fun_symbol x1, get_sons "bool" vectorBool x2
  | x -> error_xml x "not an argFilterMapping";;

let proj = function
  | [] -> None
  | x :: _ -> Some (get_nonNegativeInteger x);;

let argProjMapping = function
  | Element ("mapping", _, _, x1 :: x2 :: _) ->
      fun_symbol x1, get_sons "proj" proj x2
  | x -> error_xml x "not an argProjMapping";;

let arg = get_first_son "arg" get_nonNegativeInteger;;

let listArg = List.map arg;;

let argPermMapping = function
  | Element ("mapping", _, _, x1 :: x2 :: _) ->
      fun_symbol x1, get_sons "perm" listArg x2
  | x -> error_xml x "not an argPermMapping";;

let filter = function
  | Element ("bool", _, _, xs) -> Bool (vectorBool xs)
  | Element ("proj", _, _, x :: _) -> Proj (get_nonNegativeInteger x)
  | Element ("perm", _, _, xs) -> Perm (listArg xs)
  | x -> error_xml x "not a filter";;

let argFilterMapping = function
  | Element ("mapping", _, _, x1 :: []) -> fun_symbol x1, None
  | Element ("mapping", _, _, x1 :: x2 :: _) -> fun_symbol x1, Some (filter x2)
  | x -> error_xml x "not an argFilterMapping";;

let af_def f = get_sons "def" (List.map f);;

let simpleProjMapping = function
  | Element ("mapping", _, _, x1 :: x2 :: _) ->
      fun_symbol x1, get_first_son "proj" get_nonNegativeInteger x2
  | x -> error_xml x "not a simpleProjMapping";;

(*****************************************************************************)
(* RPO *)
(*****************************************************************************)

let get_status = function
  | Element ("lex", _, _, _) -> Lex
  | Element ("mul", _, _, _) -> Mul
  | x -> error_xml x "not a status";;

let status = get_first_son "status" get_status;;

let precedence = get_first_son "prec" get_int;;

let statusMapping = function
  | Element ("mapping", _, _, x1 :: x2 :: x3 :: _) ->
      fun_symbol x1, (status x2, precedence x3)
  | x -> error_xml x "not a statusMapping";;

(*****************************************************************************)
(* Reduction orderings *)
(*****************************************************************************)

let rec reductionOrder = function
  | Element ("poly_int", _, _, xs) ->
      PolyInt (List.map polynomialMapping xs)
  | Element ("matrix_int", _, _, x1 :: x2 :: _) ->
      MatrixInt { mi_dim = dimension x1; mi_int = mi_map matrixMapping x2 }
  | Element ("arctic_int", _, _, x1 :: x2 :: _) ->
      ArcticInt { mi_dim = dimension x1; mi_int = mi_map arcticMapping x2 }
  | Element ("tropical_int", _, _, x1 :: x2 :: _) ->
      TropicalInt { mi_dim = dimension x1; mi_int = mi_map tropicalMapping x2 }
  | Element ("arctic_bz_int", _, _, x1 :: x2 :: _) ->
      ArcticBZInt { mi_dim = dimension x1; mi_int = mi_map arcticMapping x2 }
  | Element ("arg_bool", _, _, x1 :: x2 :: _) ->
      ArgBoolOrd (af_def argBoolMapping x1, order x2)
  | Element ("arg_proj", _, _, x1 :: x2 :: _) ->
      ArgProjOrd (af_def argProjMapping x1, order x2)
  | Element ("arg_filter", _, _, x1 :: x2 :: _) ->
      ArgFilterOrd (af_def argFilterMapping x1, order x2)
  | Element ("rpo", _, _, xs) -> Rpo (List.map statusMapping xs)
  | x -> error_xml x "not a reductionOrder"

and order x = get_first_son "order" reductionOrder x;;

(*****************************************************************************)
(* Dependency graph approximations *)
(*****************************************************************************)

let overDpGraph = function
  | Element ("hde", _, _, _) -> HDE
  | Element ("hde_marked", _, _, _) -> HDE_Marked
  | Element ("unif", _, _, _) -> Unif
  | (Element _ | PCData _) as x -> error_xml x "not an overDPGraph";;

(*****************************************************************************)
(* Counter-examples *)
(*****************************************************************************)

let trs_pos = get_sons "position" listArg;;

let trsModStep = function
  | Element ("step", _, _, x1 :: x2 :: _) ->
      { cet_mod_step_pos = trs_pos x1;
	cet_mod_step_rule = trsRule x2 }
  | x -> error_xml x "not a trsModStep";;

let trsModSteps = List.map trsModStep;;

let trsStep = function
  | Element ("step", _, _, x1 :: x2 :: []) ->
      { cet_step_mod_steps = [];
	cet_step_pos = trs_pos x1;
	cet_step_rule = trsRule x2 }
  | Element ("step", _, _, x1 :: x2 :: x3 :: _) ->
      { cet_step_mod_steps = get_sons "modulo" trsModSteps x1;
	cet_step_pos = trs_pos x2;
	cet_step_rule = trsRule x3 }
  | x -> error_xml x "not a trsStep";;

let trsSteps = List.map trsStep;;

let trsCounterExample = function
  | Element ("var_cond", _, _, _) -> CET_var_cond
  | Element ("loop", _, _, x1 :: x2 :: x3 :: x4 :: _) ->
      CET_loop { cet_start = get_first_son "start" term x1;
		 cet_steps = get_sons "steps" trsSteps x2;
		 cet_mod = get_sons "modulo" trsModSteps x3;
		 cet_pos = trs_pos x4 }
  | Element ("loop", _, _, x1 :: x2 :: x3 :: _) ->
      CET_loop { cet_start = get_first_son "start" term x1;
		 cet_steps = get_sons "steps" trsSteps x2;
		 cet_mod = [];
		 cet_pos = trs_pos x3 }
  | x -> error_xml x "not a trsCounterExample";;

let srs_pos = get_first_son "position" get_nonNegativeInteger;;

let srsModStep = function
  | Element ("step", _, _, x1 :: x2 :: _) ->
      { ces_mod_step_pos = srs_pos x1;
	ces_mod_step_rule = srsRule x2 }
  | x -> error_xml x "not an srsModStep";;

let srsModSteps = List.map srsModStep;;

let srsStep = function
  | Element ("step", _, _, x1 :: x2 :: []) ->
      { ces_step_mod_steps = [];
	ces_step_pos = srs_pos x1;
	ces_step_rule = srsRule x2 }
  | Element ("step", _, _, x1 :: x2 :: x3 :: _) ->
      { ces_step_mod_steps = get_sons "modulo" srsModSteps x1;
	ces_step_pos = srs_pos x2;
	ces_step_rule = srsRule x3 }
  | x -> error_xml x "not a srsStep";;

let srsSteps = List.map srsStep;;

let srsCounterExample = function
  | Element ("loop", _, _, x1 :: x2 :: x3 :: x4 :: _) ->
      CES_loop { ces_start = get_sons "start" word x1;
		 ces_steps = get_sons "steps" srsSteps x2;
		 ces_mod = get_sons "modulo" srsModSteps x3;
		 ces_pos = srs_pos x4 }
  | Element ("loop", _, _, x1 :: x2 :: x3 :: _) ->
      CES_loop { ces_start = get_sons "start" word x1;
		 ces_steps = get_sons "steps" srsSteps x2;
		 ces_mod = [];
		 ces_pos = srs_pos x3 }
  | x -> error_xml x "not an srsCounterExample";;

let counterExample = function
  | Element ("trs_counter_example", _, _, x :: _) ->
      CE_trs (trsCounterExample x)
  | Element ("srs_counter_example", _, _, x :: _) ->
      CE_srs (srsCounterExample x)
  | x -> error_xml x "not a counterExample";;

(*****************************************************************************)
(* Proof kinds *)
(*****************************************************************************)

let rec proofKind = function
  | Element ("trivial", _, _, _) -> Trivial
  | Element ("manna_ness", _, _, x1 :: x2 :: _ :: _) ->
      MannaNess (true, order x1, proof x2)
  | Element ("manna_ness", _, _, x1 :: x2 :: _) ->
      MannaNess (false, order x1, proof x2)
  | Element ("dp", _, _, x :: _) -> DP (proof x)
  | Element ("mark_symbols", _, _, x :: _) -> MarkSymb (proof x)
  | Element ("decomp", _, _, x :: xs) ->
      Decomp (get_first_son "graph" overDpGraph x, List.map component xs)
  | Element ("arg_bool", _, _, x1 :: x2 :: _) ->
      ArgBool (af_def argBoolMapping x1, proof x2)
  | Element ("arg_proj", _, _, x1 :: x2 :: _) ->
      ArgProj (af_def argProjMapping x1, proof x2)
  | Element ("arg_perm", _, _, x1 :: x2 :: _) ->
      ArgPerm (af_def argPermMapping x1, proof x2)
  | Element ("arg_filter", _, _, x1 :: x2 :: _) ->
      ArgFilter (af_def argFilterMapping x1, proof x2)
  | Element ("as_trs", _, _, x :: _) -> AsTrs (proof x)
  | Element ("as_srs", _, _, x :: _) -> AsSrs (proof x)
  | Element ("srs_rev", _, _, x :: _) -> SrsRev (proof x)
  | Element ("trs_rev", _, _, x :: _) -> TrsRev (proof x)
  | Element ("flat_cc", _, _, x :: _) -> FlatCC (proof x)
  | Element ("root_lab", _, _, x :: _) -> RootLab (proof x)
  | Element ("unlab", _, _, x :: _) -> Unlab (proof x)
  | Element ("subterm_crit", _, _, x1 :: x2 :: _) ->
      SubtermCrit (af_def simpleProjMapping x1, proof x2)
  | x -> error_xml x "not a proofKind"

and proof x = get_first_son "proof" proofKind x

and component = function
  | Element ("component", _, _, x1 :: x2 :: _) ->
      get_sons "rules" trsRules x1, Some (proof x2)
  | Element ("component", _, _, x :: _) ->
      get_sons "rules" trsRules x, None
  | x -> error_xml x "not a component";;

(*****************************************************************************)
(* Certificates *)
(*****************************************************************************)

let certificate = function
  | Element ("proof", _, _, x :: _) -> Proof (proofKind x)
  | Element ("counter_example", _, _, x :: _) ->
      Counter_example (counterExample x)
  | x -> error_xml x "not a certificate";;
