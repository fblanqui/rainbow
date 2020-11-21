(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

convert a tpdb declaration list into a rainbow problem
******************************************************************************)

open Util;;
open Problem;;
open Error;;

(****************************************************************************)
(* rainbow environment for trs *)
(****************************************************************************)

(*UNUSED:
type tpdb_env = (string * Trs_sem.type_info) list;;*)

type env_info =
    | Evar of int
    | Esymb of int;;

(*UNUSED:
type env = env_info StrMap.t;;*)

let symb_set_map_of_env env =
  let f s info ((set,amap) as x) =
    match info with
      | Esymb k -> SymbSet.add (Ident s) set, SymbMap.add (Ident s) k amap
      | Evar _ -> x
  in StrMap.fold f env (SymbSet.empty, SymbMap.empty);;

(* function building a rainbow environment from a tpdb environment *)

let rainbow_env_of_tpdb_env =
  let new_var = let n = ref 0 in fun () -> n := succ !n; !n in
  let rainbow_of_tpdb = function
    | Trs_sem.Var -> Evar (new_var())
    | Trs_sem.Function k_ref -> Esymb !k_ref in
  let rec aux acc = function
    | [] -> acc
    | (s,ti) :: xs -> aux (StrMap.add s (rainbow_of_tpdb ti) acc) xs
  in aux StrMap.empty;;

(****************************************************************************)
(* functions building a rainbow trs from a tpdb trs *)
(****************************************************************************)

let term env =
  let rec aux = function
    | Trs_ast.Term ((_pos, s), ts) ->
	(match StrMap.find s env with
	  | Evar k -> Var k
	  | Esymb _ -> App (Ident s, List.map aux ts))
  in aux;;

let cond env = function
  | Trs_ast.Arrow (l, r) ->
      { cond_lhs = term env l;
	cond_test = Norm;
	cond_rhs = term env r; }
  | Trs_ast.Darrow (l, r) ->
      { cond_lhs = term env l;
	cond_test = Join;
	cond_rhs = term env r; };;

let add_trs_rules env (rs, le_rs) = function
  | Trs_ast.Rew (cs, l, r) ->
      let r = canonical_rule
	{ trs_lhs = term env l;
	  trs_rhs = term env r;
	  trs_conds = List.map (cond env) cs }
      in r :: rs, le_rs
  | Trs_ast.RelRew (cs, l, r) ->
      let r = canonical_rule
	{ trs_lhs = term env l;
	  trs_rhs = term env r;
	  trs_conds = List.map (cond env) cs }
      in rs, r :: le_rs;;

let add_trs_rules_list env =
  let rec aux acc = function
    | [] -> acc
    | x :: xs -> aux (add_trs_rules env acc x) xs
  in aux;;

let builtin_axiom_of_ident (_, s) =
  match s with
    | "AC" -> AssociativeCommutative
    | "C" -> Commutative
    | "A" -> Associative
    | _ -> not_supported
	"axioms different from associativity and commutativity";;

let add_axioms env axs = function
  | Trs_ast.Builtin (id, ids) ->
      let ax = builtin_axiom_of_ident id in
      append_map (fun (_, s) -> Builtin (Ident s, ax)) ids axs
  | Trs_ast.Equations eqs ->
      append_map
	(fun (l,r) -> Equation (canonical_equation (term env l, term env r)))
	eqs axs;;

let add_axioms_list env =
  let rec aux axs = function
    | [] -> axs
    | x :: xs -> aux (add_axioms env axs x) xs
  in aux;;

let add_trs_strategy =
  let rec aux smap = function
    | [] -> smap
    | ((_pos,s),l) :: xs ->
	aux (SymbMap.add (Ident s) (List.map snd l) smap) xs
  in fun s strat ->
    match s with
      | Trs_ast.Innermost -> Some Innermost
      | Trs_ast.Outermost -> Some Outermost
      | Trs_ast.ContextSensitive l ->
	  let smap =
	    match strat with
	      | None -> SymbMap.empty
	      | Some (ContextSensitive smap) -> smap
	      | Some Innermost | Some Outermost ->
		  error_fmt "two different strategies"
	  in Some (ContextSensitive (aux smap l));;

let add_trs_decl env (axs, rules, strat) = function
  | Trs_ast.TheoryDecl tpdb_axs ->
      add_axioms_list env axs tpdb_axs, rules, strat
  | Trs_ast.RulesDecl tpdb_rs ->
      axs, add_trs_rules_list env rules tpdb_rs, strat
  | Trs_ast.StrategyDecl s -> axs, rules, add_trs_strategy s strat
  | Trs_ast.VarDecl _ | Trs_ast.OtherDecl _ -> axs, rules, strat;;

let elements_of_trs_decls env =
  let rec aux acc = function
    | [] -> acc
    | x :: xs -> aux (add_trs_decl env acc x) xs
  in aux ([], ([], []), None);;

let pb_of_trs decls =
  let tpdb_env = Trs_sem.spec decls in
  let env = rainbow_env_of_tpdb_env tpdb_env in
  let axs, (rs, le_rs), strat = elements_of_trs_decls env decls
  and symbs, amap = symb_set_map_of_env env in
    Trs { trs_symbols = symbs;
	  trs_algebra = Signature amap;
	  trs_axioms = axs;
	  trs_strategy = strat;
	  trs_rules = rs;
	  trs_le_rules = le_rs };;

let parse_trs ic = Trs_parser.spec Trs_lexer.token (Lexing.from_channel ic);;

(****************************************************************************)
(* functions building a rainbow srs from a tpdb srs *)
(****************************************************************************)

let ident (_pos, s) = Ident s;;

let word = List.map ident;;

let add_srs_rules (rs,le_rs) = function
  | Srs_ast.Rew (l, r) ->
      let r = { srs_lhs = word l; srs_rhs = word r } in r :: rs, le_rs
  | Srs_ast.RelRew (l, r) ->
      let r = { srs_lhs = word l; srs_rhs = word r } in rs, r :: le_rs;;

let rec add_srs_rules_list acc = function
  | [] -> acc
  | x :: xs -> add_srs_rules_list (add_srs_rules acc x) xs;;

let add_srs_strategy = function
  | Srs_ast.Leftmost -> Some Leftmost
  | Srs_ast.Rightmost -> Some Rightmost;;

let add_srs_decl (rules, strat) = function
  | Srs_ast.RulesDecl tpdb_rs -> add_srs_rules_list rules tpdb_rs, strat
  | Srs_ast.StrategyDecl s -> rules, add_srs_strategy s
  | Srs_ast.OtherDecl _ -> rules, strat;;

let elements_of_srs_decls =
  let rec aux acc = function
    | [] -> acc
    | x :: xs -> aux (add_srs_decl acc x) xs
  in aux (([], []), None);;

let pb_of_srs decls =
  let (rs, le_rs), strat = elements_of_srs_decls decls in
  let symbs = symb_set_of_list symbols_of_srs_rule (le_rs @ rs) SymbSet.empty
  in Srs { srs_symbols = symbs;
	   srs_strategy = strat;
	   srs_rules = rs;
	   srs_le_rules = le_rs };;

let parse_srs ic = Srs_parser.spec Srs_lexer.token (Lexing.from_channel ic);;
