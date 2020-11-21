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

module SymbOrd : Set.OrderedType with type t = symbol;;
module SymbSet : Set.S with type elt = symbol;;
module SymbMap : Map.S with type key = symbol;;

val symbols_of_map : 'a SymbMap.t -> symbol list;;
val symbset_of_map : 'a SymbMap.t -> SymbSet.t;;

type arity_map = int SymbMap.t;;

val ident_of_symbol : symbol -> string;;
val idents_of_symbols : SymbSet.t -> Util.StrSet.t;;

val is_singleton : SymbSet.t -> bool;;
val symb_set_of_list : ('a -> SymbSet.t) -> 'a list -> SymbSet.t -> SymbSet.t;;

val list_of_map : (symbol -> 'a -> 'b) -> 'a SymbMap.t -> 'b list;;
val map_of_list : ('a -> symbol * 'b) -> 'a list -> 'b SymbMap.t;;

val nb_symbols : 'a SymbMap.t -> int;;

val symbol_of_arity : int -> arity_map -> symbol option;;
val symbol_of_arity_gt0 : arity_map -> symbol option;;

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

val has_relative_rules : problem -> bool;;

val trs_rule_of_equation : equation -> trs_rule;;
val trs_rules_of_equations : equation list -> trs_rule list;;

val trs_of_srs : srs -> trs;;

(*****************************************************************************)
(* set of symbols in a problem *)
(*****************************************************************************)

val symbols_of_term : term -> SymbSet.t;;
val symbols_of_condition : condition -> SymbSet.t;;
val symbols_of_trs_rule : trs_rule -> SymbSet.t;;

val symbols_of_word : word -> SymbSet.t;;
val symbols_of_srs_rule : srs_rule -> SymbSet.t;;

val symbols_of_problem : problem -> SymbSet.t;;

val arity_map_of_trs_rules : trs_rule list -> int SymbMap.t;;

(*****************************************************************************)
(* check terms wrt signature *)
(*****************************************************************************)

val is_correct_term  : arity_map -> term -> bool;;
val is_correct_condition : arity_map -> condition -> bool;;
val is_correct_rule : arity_map -> trs_rule -> bool;;

(*****************************************************************************)
(* set of variables in a term *)
(*****************************************************************************)

val variables_of_term : term -> IntSet.t;;

(* list of variables occurring in a term computed in a depth-first
   manner: a variable occurs in the list as many times as it occurs in
   the term *)

(*****************************************************************************)
(* canonical representation of terms *)
(*****************************************************************************)

val variables : term -> int list;;

(* canonical representation of a term: a variable is replaced by its
   leftmost position (starting from 0) in the list of variables, computed
   in a depth-first manner, of the term. *)

val canonical : term -> term;;

(* canonical representation of a rule or equation: a variable in a
rule (resp. equation) [LHS -> RHS | cond1, ..., condn] (resp. [LHS ==
RHS]) is replaced by its leftmost position (starting from 0) in the
list of variables, computed in a depth-first manner, of the term
F(LHS,cond1,..,condn,RHS) (resp. F(LHS,RHS)) where F is some arbitrary
new symbol of the appropriate arity. *)

val canonical_rule : trs_rule -> trs_rule;;
val canonical_equation : equation -> equation;;
