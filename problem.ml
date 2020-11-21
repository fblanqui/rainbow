(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

internal representation of termination problems
******************************************************************************)
open Util;;

(*****************************************************************************)
(* symbols *)
(*****************************************************************************)

type symbol =
  | Ident of string
  | Hd of symbol
  | Int of symbol
  | Label of symbol * label
      
and label = symbol list;;

module SymbOrd = struct
  type t = symbol
  let compare = Pervasives.compare
end;;

module SymbSet = Set.Make (SymbOrd);;
module SymbMap = Map.Make (SymbOrd);;

let symbols_of_map m = SymbMap.fold (fun f _ fs -> f :: fs) m [];;
let symbset_of_map m =
  SymbMap.fold (fun f _ fs -> SymbSet.add f fs) m SymbSet.empty;;

type arity_map = int SymbMap.t;;

let rec ident_of_symbol = function
  | Ident s -> s
  | Hd s -> ident_of_symbol s
  | Int s -> ident_of_symbol s
  | Label (s, _) -> ident_of_symbol s;;

let idents_of_symbols s =
  SymbSet.fold (fun f s -> StrSet.add (ident_of_symbol f) s) s StrSet.empty;;

let is_singleton s =
  try let e = SymbSet.choose s in SymbSet.equal s (SymbSet.singleton e) 
  with Not_found -> false;;

let symb_set_of_list f =
  let rec aux l acc =
    match l with
      | [] -> acc
      | x :: xs -> aux xs (SymbSet.union (f x) acc)
  in aux;;

let list_of_map f map = SymbMap.fold (fun k v xs -> f k v :: xs) map [];;

let map_of_list f =
  let rec aux acc = function
    | [] -> acc
    | x :: xs -> let (k,v) = f x in aux (SymbMap.add k v acc) xs
  in aux SymbMap.empty;;

let nb_symbols m = SymbMap.fold (fun _ _ n -> n + 1) m 0;;

exception Found of symbol;;

let symbol_of_arity n amap =
  try SymbMap.iter (fun f k -> if k = n then raise (Found f)) amap; None
  with Found f -> Some f;;

let symbol_of_arity_gt0 amap =
  try SymbMap.iter (fun f k -> if k > 0 then raise (Found f)) amap; None
  with Found f -> Some f;;

(*****************************************************************************)
(* problems *)
(*****************************************************************************)

type term =
  | Var of int
  | App of symbol * term list;;

type word = symbol list;;

type test = Norm | Join;;

type condition = {
  cond_lhs : term;
  cond_test : test;
  cond_rhs : term };;

type trs_rule = {
  trs_lhs : term;
  trs_rhs : term;
  trs_conds : condition list };;

type srs_rule = {
  srs_lhs : word;
  srs_rhs : word };;

type builtin_axiom =
  | Associative
  | Commutative
  | AssociativeCommutative;;

type equation = term * term;;

type axiom =
  | Builtin of symbol * builtin_axiom
  | Equation of equation;;

type algebra =
  | Varyadic
  | Signature of arity_map;;

type replacement_map = (int list) SymbMap.t;;

type trs_strategy =
  | Innermost
  | Outermost
  | ContextSensitive of replacement_map;;

type srs_strategy =
  | Leftmost
  | Rightmost;;

type trs = {
  trs_symbols : SymbSet.t;
  trs_algebra : algebra;
  trs_axioms : axiom list;
  trs_strategy : trs_strategy option;
  trs_le_rules : trs_rule list;
  trs_rules : trs_rule list };;

type srs = {
  srs_symbols : SymbSet.t;
  srs_strategy : srs_strategy option;
  srs_le_rules : srs_rule list;
  srs_rules : srs_rule list };;

type problem =
  | Trs of trs
  | Srs of srs;;

(*****************************************************************************)
(* basic functions on problems *)
(*****************************************************************************)

let has_relative_rules = function
  | Trs { trs_le_rules = _ :: _; _}
  | Trs { trs_axioms = _ :: _; _ }
  | Srs { srs_le_rules = _ :: _; _ } -> true
  | Trs _ | Srs _ -> false;;

(*****************************************************************************)
(* convert an equation into a rule *)
(*****************************************************************************)

let trs_rule_of_equation (l, r) =
  { trs_lhs = l; trs_rhs = r; trs_conds = [] };;

let trs_rules_of_equations = List.map trs_rule_of_equation;;

(*****************************************************************************)
(* convert an SRS into a TRS *)
(*****************************************************************************)

let rec term = function
  | [] -> Var 0
  | s :: ss -> App (s, [term ss]);;

let trs_rule r =
  { trs_lhs = term r.srs_lhs; trs_rhs = term r.srs_rhs; trs_conds = [] };;

let trs_strategy = function
  | None -> None
  | Some _ -> Error.error_fmt "no SRS strategy in XTC";;

let signature s = SymbSet.fold (fun f m -> SymbMap.add f 1 m) s SymbMap.empty;;

let trs_of_srs s =
  { trs_symbols = s.srs_symbols;
    trs_algebra = Signature (signature s.srs_symbols);
    trs_axioms = [];
    trs_strategy = trs_strategy s.srs_strategy;
    trs_le_rules = List.map trs_rule s.srs_le_rules;
    trs_rules = List.map trs_rule s.srs_rules };;

(*****************************************************************************)
(* set of symbols in a problem *)
(*****************************************************************************)

(*FIXME: includes symbols in labels too?*)
let rec symbols_of_term_aux f ts =
  SymbSet.add f (symb_set_of_list symbols_of_term ts SymbSet.empty)

and symbols_of_term = function
  | App (f, ts) -> symbols_of_term_aux f ts
  | Var _ -> SymbSet.empty;;

let symbols_of_condition c =
  SymbSet.union (symbols_of_term c.cond_lhs) (symbols_of_term c.cond_rhs);;

let symbols_of_trs_rule r =
  symb_set_of_list symbols_of_condition r.trs_conds
    (SymbSet.union (symbols_of_term r.trs_lhs) (symbols_of_term r.trs_rhs));;

let rec symbols_of_word = function
  | [] -> SymbSet.empty
  | x::xs -> SymbSet.add x (symbols_of_word xs);;

let symbols_of_srs_rule r =
  SymbSet.union (symbols_of_word r.srs_lhs) (symbols_of_word r.srs_rhs);;

let symbols_of_problem = function
  | Trs p -> p.trs_symbols
  | Srs p -> p.srs_symbols;;

let arity_map_of_trs_rules =
  let rec add_term am = function
    | App (f, ts) ->
	List.fold_left add_term (SymbMap.add f (List.length ts) am) ts
    | Var _ -> am in
  let add_rule am r = add_term (add_term am r.trs_lhs) r.trs_rhs in
    List.fold_left add_rule SymbMap.empty;;

(*****************************************************************************)
(* set of variables in a problem *)
(*****************************************************************************)

let rec variables_of_term = function
  | App (_, ts) -> int_set_of_list variables_of_term ts
  | Var x -> IntSet.singleton x;;

(*UNUSED:
let variables_of_condition c =
  IntSet.union (variables_of_term c.cond_lhs) (variables_of_term c.cond_rhs);;

let variables_of_trs_rule r =
  IntSet.union (int_set_of_list variables_of_condition r.trs_conds)
    (IntSet.union (variables_of_term r.trs_lhs)
       (variables_of_term r.trs_rhs));;*)

(*****************************************************************************)
(* check terms wrt signature *)
(*****************************************************************************)

let is_correct_term amap =
  let rec aux = function
    | Var _ -> true
    | App (f, ts) ->
      List.length ts = SymbMap.find f amap && List.for_all aux ts
  in aux;;

let is_correct_condition amap c =
  is_correct_term amap c.cond_lhs && is_correct_term amap c.cond_rhs;;

let is_correct_rule amap r =
  is_correct_term amap r.trs_lhs && is_correct_term amap r.trs_rhs
  && List.for_all (is_correct_condition amap) r.trs_conds;;

(*****************************************************************************)
(* list of variables occurring in a term computed in a depth-first
   manner: a variable occurs in the list as many times as it occurs in
   the term *)
(*****************************************************************************)

let rec variables = function
   | Var x -> [x]
   | App (_, ts) -> List.flatten (List.map variables ts);;

let variables_cond c = variables c.cond_lhs @ variables c.cond_rhs;;

let variables_rule r =
  variables r.trs_lhs @ List.flatten (List.map variables_cond r.trs_conds)
  @ variables r.trs_rhs;;

let variables_equation (u, v) = variables u @ variables v;;

(*****************************************************************************)
(* canonical representation of a term: a variable is replaced by its
   leftmost position (starting from 0) in the list of variables, computed
   in a depth-first manner, of the term. *)
(*****************************************************************************)

let rename xs =
  let rec aux = function
    | Var x -> Var (position x xs)
    | App (f, ts) -> App (f, List.map aux ts)
  in aux;;

let canonical t = rename (variables t) t;;

(*****************************************************************************)
(* canonical representation of a rule or equation: a variable in a
rule (resp. equation) [LHS -> RHS | cond1, ..., condn] (resp. [LHS ==
RHS]) is replaced by its leftmost position (starting from 0) in the
list of variables, computed in a depth-first manner, of the term
F(LHS,cond1,..,condn,RHS) (resp. F(LHS,RHS)) where F is some arbitrary
new symbol of the appropriate arity. *)
(*****************************************************************************)

let rename_cond xs c = {
  cond_lhs = rename xs c.cond_lhs;
  cond_test = c.cond_test;
  cond_rhs = rename xs c.cond_rhs };;

let rename_rule xs r = {
  trs_lhs = rename xs r.trs_lhs;
  trs_rhs = rename xs r.trs_rhs;
  trs_conds = List.map (rename_cond xs) r.trs_conds };;

let canonical_rule r = rename_rule (variables_rule r) r;;

let rename_equation xs (u, v) = (rename xs u, rename xs v);;

let canonical_equation e = rename_equation (variables_equation e) e;;
