(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-08-28

internal representation of XTC files version 0.4
******************************************************************************)

(* we follow the structure of xtc.xsd:

   - a top-level element/group is translated into a type definition
   with the same name

   - an element/group definition is translated into a type expression

   - a choice is translated into a concrete data type T, and
   constructor names are prefixed by a prefix of the name of T

   - a sequence of non fixed length is translated into a list

   - a sequence of fixed length is translated into a tuple

   - an element occuring at most once is translated into an option
   type except for lists and strings
*)

open Xml;;

type bound =
  | BoundUnknown
  | BoundPoly
  | BoundOn of int;;

type automatonstuff = string;;

type startterm =
  | STNone
  | STConstructorBased
  | STFull
  | STAutomaton of automatonstuff;;

type entry = int;;

type var = string;;

type replacementmap = entry list;;

type name = string;;

type typ =
  | TypeBasic of string
  | TypeArrow of typ * typ;;

type term =
  | TermVar of var
  | TermFunapp of funapp
  | TermLam of var * typ * term
  | TermApp of term * term

and funapp = name * term list;;

type arg = term;;
type lhs = term;;
type rhs = term;;

type author = string;;
type date = string;;

type comment = (author * date) * xml list;;

type condition = lhs * rhs;;

type conditions = condition list;;

type rule = lhs * rhs * conditions;;

type originalfilename = string;;

type metainformation = originalfilename list * author * date * comment option;;

type status =
  | StatusNone
  | StatusNo
  | StatusMaybe
  | StatusYes of (bound * bound) option;;

type strategy = StratFull | StratInnermost | StratOutermost;;

type conditiontype = CTNone | CTJoin | CTOriented | CTOther;;

type theory = ThyNone | ThyA | ThyC | ThyAC;;

type arity = int;;

type funcsym = name * arity * theory * replacementmap option;;

type varDeclaration = var * typ;;

type funcDeclaration = name * (typ list * typ);;

type signature =
  | SignFO of funcsym list
  | SignHO of varDeclaration list * funcDeclaration list;;

type relrules = rule list;;

type rules = rule list * relrules;;

type xtc_type = Term | Comp;;

type trs = rules * signature * comment option * conditiontype;;

type problem = xtc_type * trs * strategy * startterm * status
    * metainformation option;;
