(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2010-11-10

convert PB to XTC
******************************************************************************)

open Xtc;;
open Problem;;
open Error;;

let strategy = function
  | None -> StratFull
  | Some Innermost -> StratInnermost
  | Some Outermost -> StratOutermost
  | Some (ContextSensitive _) -> StratFull;; (* defined in the signature *)

let name = function
  | Ident s -> s
  | Hd _ | Int _ | Label (_, _) ->
      error_fmt "no marked or labelled symbol in XTC";;

let builtin = function
  | Associative -> ThyA
  | Commutative -> ThyC
  | AssociativeCommutative -> ThyAC;;

let rec theory f = function
  | [] -> ThyNone
  | Builtin (g, a) :: _ when f = g -> builtin a
  | Builtin (_, _) :: axs -> theory f axs
  | Equation _ :: _ -> error_fmt "no equation in XTC";;

let replacement_map s f =
  match s.trs_strategy with
    | Some (ContextSensitive m) ->
	begin try Some (SymbMap.find f m) with Not_found -> None end
    | Some (Innermost|Outermost)
    | None -> None;;

let funcsym s f n l =
  (name f, n, theory f s.trs_axioms, replacement_map s f) :: l;;

let signature s =
  match s.trs_algebra with
    | Varyadic -> error_fmt "no varyadic symbol in XTC"
    | Signature m -> SignFO (SymbMap.fold (funcsym s) m []);;

let rec term = function
  | Var x -> TermVar (Printf.sprintf "x%d" x)
  | App (s, ts) -> TermFunapp (name s, List.map term ts);;

let condition c = term c.cond_lhs, term c.cond_rhs;;

let rule r = term r.trs_lhs, term r.trs_rhs, List.map condition r.trs_conds;;

let same_conditiontype ct =
  List.for_all (fun r ->
		  List.for_all (fun c -> c.cond_test = ct) r.trs_conds);;

let conditiontype_aux = function
  | Norm -> CTOriented
  | Join -> CTJoin;;

let conditiontype s =
  try
    let r = List.find (fun r -> r.trs_conds <> []) s.trs_rules in
      begin match r.trs_conds with
	| [] -> assert false
	| c :: _ ->
	    if same_conditiontype c.cond_test s.trs_rules then
	      conditiontype_aux c.cond_test
	    else error_fmt "XTC does not support different condition types"
      end
  with Not_found -> CTNone;;

let trs s =
  (List.map rule s.trs_rules, List.map rule s.trs_le_rules),
  signature s, None, conditiontype s;;

let problem_aux s =
  Term, trs s, strategy s.trs_strategy, STNone, StatusNone, None;;

let problem = function
  | Trs s -> problem_aux s
  | Srs s -> problem_aux (trs_of_srs s);;

