(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

from the internal representation of problems to xml
******************************************************************************)

open Problem;;
open Xml;;
open Util;;
open Libxml;;

let pc_int k = pc (string_of_int k)
let elt_int' tag k = elt tag [pc_int k]

let arity = elt_int "arity";;
let index = elt_int' "index";;

let rec symbol = function
  | Ident s -> pc s
  | Hd f -> elt "hd_mark" [symbol f]
  | Int f -> elt "int_mark" [symbol f]
  | Label (f, ls) -> elt "labelled_symbol" (fun_symbol f :: List.map label ls)

and fun_symbol f = elt "fun" [symbol f]

and label f = elt "label" [fun_symbol f];;

let rec term = function
  | Var i -> elt_int "var" i
  | App (f, ts) -> elt "app" (fun_symbol f :: List.map arg ts)

and arg t = elt "arg" [term t];;

let trs_lhs t = elt "lhs" [term t];;
let trs_rhs t = elt "rhs" [term t];;

let letter_symbol f = elt "letter" [symbol f];;

let word = List.map letter_symbol;;

let string_of_test = function Norm -> "norm" | Join -> "join";;

let test t = elt (string_of_test t) [];;

let condition c = elt "if"
  [term c.cond_lhs; test c.cond_test; term c.cond_rhs];;

let trs_rule r = elt "rule"
  (trs_lhs r.trs_lhs :: trs_rhs r.trs_rhs :: List.map condition r.trs_conds);;

let srs_lhs w = elt "lhs" (word w);;
let srs_rhs w = elt "rhs" (word w);;

let srs_rule r = elt "rule" [srs_lhs r.srs_lhs; srs_rhs r.srs_rhs];;

let string_of_builtin = function
  | Associative -> "associative"
  | Commutative -> "commutative"
  | AssociativeCommutative -> "associative_commutative";;

let builtin b = elt (string_of_builtin b) [];;

let axiom = function
  | Builtin (s,a) -> elt "builtin" [fun_symbol s; builtin a]
  | Equation (l,r) -> elt "equation" [trs_lhs l; trs_rhs r];;

let add_arity s k xs = elt "mapping" [fun_symbol s; arity k] :: xs;;

let algebra = function
  | Varyadic -> elt "varyadic" []
  | Signature amap -> elt "signature" (SymbMap.fold add_arity amap []);;

let replacement s ks = elt "replacement" (fun_symbol s :: List.map index ks);;

let trs_strategy = function
  | None -> elt "none" []
  | Some Innermost -> elt "innermost" []
  | Some Outermost -> elt "outermost" []
  | Some (ContextSensitive rmap) ->
      elt "context_sensitive" (list_of_map replacement rmap);;

let string_of_srs_strategy = function
  | None -> "none"
  | Some Leftmost -> "leftmost"
  | Some Rightmost -> "rightmost";;

let srs_strategy s = elt (string_of_srs_strategy s) [];;

let trs p = elt "trs"
  [elt "algebra" [algebra p.trs_algebra];
   elt "theory" (List.map axiom p.trs_axioms);
   elt "strategy" [trs_strategy p.trs_strategy];
   elt "le_rules" (List.map trs_rule p.trs_le_rules);
   elt "rules" (List.map trs_rule p.trs_rules)];;

let srs p = elt "srs"
  [elt "strategy" [srs_strategy p.srs_strategy];
   elt "le_rules" (List.map srs_rule p.srs_le_rules);
   elt "rules" (List.map srs_rule p.srs_rules)];;

let problem_aux = function
  | Trs p -> trs p
  | Srs p -> srs p;;

let problem p = Element
  ("problem", dummy_pos,
  ["xmlns", "urn:rainbow.problem.format";
   "xmlns:xsi", "http://www.w3.org/2001/XMLSchema-instance";
   "xsi:schemaLocation",
     "urn:rainbow.problem.format http://color.loria.fr/problem.xsd"],
  [problem_aux p]);;
