(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2010-06-15

convert a CPF problem into a Rainbow problem
******************************************************************************)

open Cpf0;;
open Problem;;
open Error;;

let option f = function
  | None   -> None
  | Some x -> Some (f x);;

let list_option f = function
  | None   -> []
  | Some x -> f x;;

let strategy = function
  | Strategy_innermost       -> Innermost
  | Strategy_innermostLhss _ -> not_supported "innermostLhss"
  | Strategy_outermost       -> not_supported "outermost";;

let term = Prf_of_newcpf.term false;;

let cpf_rule (l, r) = Util.init_var_map ();
  canonical_rule { trs_lhs = term l; trs_rhs = term r; trs_conds = [] };;

let rules = List.map cpf_rule;;

let equation (l, r) = term l, term r;;

let equations = List.map equation;;

let axiom e = Equation e;;

let axioms = List.map axiom;;

let input = function
  | Input_trsInput (((rs, st), es), rels) ->
      let rs   = rules rs
      and rels = list_option rules rels
      and es   = list_option equations es in
      let am   = arity_map_of_trs_rules (trs_rules_of_equations es @ rels @ rs) in
	Trs { trs_symbols = symbset_of_map am;
	      trs_algebra = Signature am;
	      trs_axioms = axioms es;
	      trs_strategy = option strategy st;
	      trs_le_rules = rels;
	      trs_rules = rs }
  | Input_dpInput (((_, _), _), _)
  | Input_orderingConstraints _      -> not_supported "inputs other than TRSs"
  | Input_completionInput _          -> not_supported "completionInput"
  | Input_equationalReasoningInput _ -> not_supported "equationalReasoningInput"
  | Input_complexityInput _          -> not_supported "complexityInput"
  | Input_ctrsInput _                -> not_supported "ctrsInput";;

let problem (((i, _), _), _) = input i;;
