(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2010-06-15

convert a CPF problem into a Rainbow problem
******************************************************************************)

open Cpf;;
open Problem;;
open Error;;

let strategy = function
  | StratFull -> None
  | StratIn -> Some Innermost;;

let term = Prf_of_cpf.term false;;

let rule (l, r) = Util.init_var_map ();
  canonical_rule { trs_lhs = term l; trs_rhs = term r; trs_conds = [] };;

let rules = List.map rule;;

let equation (l, r) = term l, term r;;

let equations = List.map equation;;

let axiom e = Equation e;;
 
let axioms = List.map axiom;;

let input = function
  | InTrs (rs, st, es, rels) ->
      let rs = rules rs and rels = rules rels and es = equations es in
      let am = arity_map_of_trs_rules (trs_rules_of_equations es @ rels @ rs) in
	Trs { trs_symbols = symbset_of_map am;
	      trs_algebra = Signature am;
	      trs_axioms = axioms es;
	      trs_strategy = strategy st;
	      trs_le_rules = rels;
	      trs_rules = rs }
  | InDp (_, _, _, _)
  | InOrd _ -> not_supported "inputs other than TRSs";;

let problem (i, _, _, _) = input i;;
