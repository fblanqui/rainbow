(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-09-04

converting xtc version 0.4 to problem
******************************************************************************)

open Xtc;;
open Problem;;
open Util;;
open Error;;

let strategy_aux = function
  | StratFull -> None
  | StratInnermost -> Some Innermost
  | StratOutermost -> Some Outermost;;

let strategy strat rm =
  if rm <> SymbMap.empty then Some (ContextSensitive rm)
  else strategy_aux strat;;

let theory_aux = function
  | ThyNone -> None
  | ThyA -> Some Associative
  | ThyC -> Some Commutative
  | ThyAC -> Some AssociativeCommutative;;

let add_theory axs f t =
  match theory_aux t with
    | Some a -> Builtin (f, a) :: axs
    | _ -> axs;;

let add_replacementmap rm f = function
  | Some l -> SymbMap.add f l rm
  | _ -> rm;;

let fo_signature =
  let rec aux ss am axs rm = function
    | [] -> ss, am, axs, rm
    | (n, a, t, o) :: l ->
	let f = Ident n in
	let ss' = SymbSet.add f ss
	and am' = SymbMap.add f a am
	and axs' = add_theory axs f t
	and rm' = add_replacementmap rm f o in
	  aux ss' am' axs' rm' l
  in aux SymbSet.empty SymbMap.empty [] SymbMap.empty;;

let signature = function
  | SignFO s -> fo_signature s
  | SignHO _ -> not_supported "higherOrderSignature";;

let test = function
  | CTJoin -> Join
  | CTOriented -> Norm
  | CTOther -> not_supported "conditiontype OTHER"
  | CTNone -> error_fmt "no conditiontype given for conditional rules";;

let rec term = function
  | TermVar i -> Var (var i)
  | TermFunapp (n, ts) -> App (Ident n, List.map term ts)
  | TermLam _ -> not_supported "lambda"
  | TermApp _ -> not_supported "application";;

let condition ct (l, r) =
  { cond_lhs = term l; cond_test = test ct; cond_rhs = term r };;

let trs_rule ct (l, r, cs) = Util.init_var_map ();
  canonical_rule { trs_lhs = term l; trs_rhs = term r;
		   trs_conds = List.map (condition ct) cs };;

let relrules ct = List.map (trs_rule ct);;

let rules ct (rs, lers) = relrules ct rs, relrules ct lers;;

let trs (rs, sign, _, ct) strat =
  let ss, am, axs, rm = signature sign in
  let rs, lers = rules ct rs in
    { trs_symbols = ss;
      trs_algebra = Signature am;
      trs_axioms = axs;
      trs_strategy = strategy strat rm;
      trs_le_rules = lers;
      trs_rules = rs };;

let problem = function
  | Term, t, s, _, _, _ -> Trs (trs t s)
  | Comp, _, _, _, _, _ -> not_supported "complexity problems";;

