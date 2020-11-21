(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

from the internal representation of xtc problems to xml
******************************************************************************)

open Xml;;
open Util;;
open Libxml;;
open Xtc;;

let opt f = function
  | None -> []
  | Some x -> [f x];;

let list s f l = elt s (List.map f l);;

let opt_list s f = function
  | [] -> []
  | l -> [list s f l];;

let name n = elt "name" [pc n];;
let arity a = elt_int "arity" a;;

let theory = function
  | ThyNone -> []
  | ThyA -> [elt "theory" [pc "A"]]
  | ThyC -> [elt "theory" [pc "C"]]
  | ThyAC -> [elt "theory" [pc "AC"]];;

let pc_int k = pc (string_of_int k)
let elt_int' tag k = elt tag [pc_int k]

let entry = elt_int' "entry";;

let rec typ t = elt "type" [typ_aux t]

and typ_aux = function
  | TypeBasic s -> elt "basic" [pc s]
  | TypeArrow (t1, t2) -> elt "arrow" [typ t1; typ t2]

let var v = elt "var" [pc v];;

let rec term = function
  | TermVar v -> var v
  | TermFunapp (n, ts) -> elt "funapp" (name n :: List.map arg ts)
  | TermLam (v, ty, tm) -> elt "lambda" [var v; typ ty; term tm]
  | TermApp (t1, t2) -> elt "application" [term t1; term t2]

and arg t = elt "arg" [term t];;

let lhs l = elt "lhs" [term l];;
let rhs r = elt "rhs" [term r];;

let condition (l, r) = elt "condition" [lhs l; rhs r];;

let rule (l, r, cs) =
  elt "rule" (lhs l :: rhs r :: opt_list "conditions" condition cs);;

let varDeclaration (v, t) = elt "varDeclaration" [var v; typ t];;

let funcDeclaration (n, (ts, t)) =
  elt "funcDeclaration" [name n; list "typeDeclaration" typ (ts @ [t])];;

let funcsym (n, a, t, orm) = elt "funcsym"
  (name n :: arity a :: theory t @ opt (list "replacementmap" entry) orm);;

let signature = function
  | SignFO l -> list "signature" funcsym l
  | SignHO (vs, fs) -> elt "higherOrderSignature"
      [list "variableTypeInfo" varDeclaration vs;
       list "functionSymbolTypeInfo" funcDeclaration fs];;

let comment ((a, d), xs) =
  Element ("comment", dummy_pos, ["author", a; "date", d], xs);;

let conditiontype = function
  | CTNone -> []
  | CTJoin -> [elt "conditiontype" [pc "JOIN"]]
  | CTOriented -> [elt "conditiontype" [pc "ORIENTED"]]
  | CTOther -> [elt "conditiontype" [pc "OTHER"]];;

let author s = elt "author" [pc s];;
let date s = elt "date" [pc s];;
let originalfilename s = elt "originalfilename" [pc s];;

let metainfo (fs, a, d, oc) = elt "metainformation"
  (List.map originalfilename fs @ author a :: date d :: opt comment oc);;

let rules (rs, rels) =
  elt "rules" (List.map rule rs @ opt_list "relrules" rule rels);;

let trs (rs, s, oc, ct) =
  elt "trs" (rules rs :: signature s :: opt comment oc @ conditiontype ct);;

let string_of_strategy = function
  | StratFull -> "FULL"
  | StratInnermost -> "INNERMOST"
  | StratOutermost -> "OUTERMOST";;

let strategy s = elt "strategy" [pc (string_of_strategy s)];;

let startterm = function
  | STNone -> []
  | STAutomaton a -> [elt "automaton" [elt "automatonstuff" [pc a]]]
  | STFull -> [elt "full" []]
  | STConstructorBased -> [elt "constructor-based" []];;

let string_of_bound = function
  | BoundUnknown -> "?"
  | BoundPoly -> "POLY"
  | BoundOn i -> Printf.sprintf "O(%d)" i;;

let bound b = elt "bound" [pc (string_of_bound b)];;

let status = function
  | StatusNone -> []
  | StatusNo -> [elt "no" []]
  | StatusMaybe -> [elt "maybe" []]
  | StatusYes None -> [elt "yes" []]
  | StatusYes (Some (b1, b2)) -> [elt "yes" [bound b1; bound b2]];;

let string_of_xtc_type = function
  | Term -> "termination"
  | Comp -> "complexity";;

let problem (typ, r, strat, start, stat, ometa) = Element
  ("problem", dummy_pos,
   ["xmlns:xsi", "http://www.w3.org/2001/XMLSchema-instance";
    "xsi:noNamespaceSchemaLocation", "http://dev.aspsimon.org/xtc.xsd";
    "type", string_of_xtc_type typ],
   (trs r :: strategy strat :: startterm start @ status stat
    @ opt metainfo ometa));;
