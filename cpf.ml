(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-08-28

internal representation of CPF files
******************************************************************************)

(* we follow the structure of cpf.xsd:

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

type integer = int;;

type nonNegativeInteger = int;;

type positiveInteger = int;;

type name = string

and label =
  | LabNone
  | LabInt of nonNegativeInteger list
  | LabSymb of symbol list

and symbol =
  | SymbName of name
  | SymbSharp of symbol
  | SymbLab of symbol * label

and var = string

and term =
  | TermVar of var
  | TermApp of symbol * term list

and rule = term * term

and rules = rule list

and dps = rules

and trs = rules

and usableRules = rules

and number =
  | NumInt of integer
  | NumRat of integer * positiveInteger 

and coefficient =
  | CoefNum of number
  | CoefMinusInf
  | CoefPlusInf
  | CoefVec of vector
  | CoefMat of matrix

and vector = coefficient list

and matrix = vector list

and polynomial =
  | PolCoef of coefficient
  | PolVar of positiveInteger
  | PolSum of polynomial list
  | PolProd of polynomial list
  | PolMax of polynomial list
  | PolMin of polynomial list

and cpf_function =
  | FunPol of polynomial

and arity = nonNegativeInteger

and dimension = positiveInteger

and strictDimension = positiveInteger

and degree = nonNegativeInteger

and position = positiveInteger

and argumentFilter = (symbol * arity * argumentFilterEntryKind) list

and argumentFilterEntryKind =
  | ArgFilCollaps of positiveInteger
  | ArgFilNonCollaps of position list

and domain =
  | DomNat
  | DomInt
  | DomRat of number
  | DomArctic of domain
  | DomTropical of domain
  | DomMat of dimension * strictDimension * domain

and redPair =
  | RedInt of redPairIntType * (symbol * arity * cpf_function) list
  | RedRPO of (symbol * arity * nonNegativeInteger * redPairRPOStatus) list
      * argumentFilter

and redPairIntType =
  | TypPol of domain * degree
  | TypMat of domain * dimension * strictDimension

and redPairRPOStatus =
  | StatLex
  | StatMul

and arithFunction =
  | ArithNat of nonNegativeInteger
  | ArithVar of positiveInteger
  | ArithSum of arithFunction list
  | ArithProd of arithFunction list
  | ArithMin of arithFunction list
  | ArithMax of arithFunction list

and model =
  | ModFin of
      positiveInteger * tupleOrder * (symbol * arity * arithFunction) list
  | ModRootLab

and tupleOrder =
  | TOrdNone
  | TOrdPointWise

and dpProof =
  | DpEmpty
  | DpGraph of (dps * bool * positiveInteger list * dpProof option) list
  | DpRed of orderingConstraints * orderingConstraintProof * dps * dpProof
  | DpRedUR of orderingConstraints * orderingConstraintProof
      * dps * usableRules * dpProof
  | DpRedMono of orderingConstraints * orderingConstraintProof
      * dps * trs * dpProof
  | DpRedMonoUR of orderingConstraints * orderingConstraintProof
      * dps * trs * usableRules * dpProof
  | DpSubterm of argumentFilter * projectedRewriteSequence list * dps * dpProof
  | DpSemLab of model * dps * trs * dpProof
  | DpUnlab of dps * trs * dpProof
  | DpSC of sizeChangeProc * sizeChangeGraph list
  | DpFlatCC of symbol option * context list * dps * trs * dpProof
  | DpArgFilter of argumentFilter * dps * trs * dpProof
  | DpHyp of dpInput

and projectedRewriteSequence = rule * rewriteSequence

and sizeChangeProc =
  | SCSubterm
  | SCRedPair of orderingConstraints * orderingConstraintProof * usableRules
 
and sizeChangeGraph = rule * edge list

and edge = position * bool * position

and substitution = (var * term) list

and context =
  | ContEmpty
  | ContApp of symbol * term list * context * term list

and rewriteStep = position list * rule * bool * term

and rewriteSequence = term * rewriteStep list

and trsTerminationProof =
  | TrsEmpty
  | TrsRuleRemoval of
      orderingConstraints * orderingConstraintProof * trs * trsTerminationProof
  | TrsDpTrans of dps * bool * dpProof
  | TrsSemLab of model * trs * trsTerminationProof
  | TrsUnlab of trs * trsTerminationProof
  | TrsRev of trs * trsTerminationProof
  | TrsFlatCC of context list * trs * trsTerminationProof
  | TrsHyp of trsInput

and loop = rewriteSequence * substitution * context

and trsNonterminationProof =
  | TrsNTVarCond
  | TrsNTRuleRemoval of trs * trsNonterminationProof
  | TrsNTRev of trs * trsNonterminationProof 
  | TrsNTLoop of loop
  | TrsNTDp of dps * bool * dpNonterminationProof
  | TrsNTHyp of trsInput

and relativeTerminationProof =
  | RelEmptyR
  | RelEmptyS
  | RelRuleRemoval of orderingConstraints * orderingConstraintProof
      * trs * trs * relativeTerminationProof
  | RelSemLab of model * trs * trs * relativeTerminationProof
  | RelUnlab of trs * trs * relativeTerminationProof
  | RelRev of trs * trs * relativeTerminationProof
  | RelHyp of trsInput

and dpNonterminationProof =
  | DpNTLoop of loop
  | DpNTRuleRemoval of dps * trs * dpNonterminationProof
  | DpNTHyp of dpInput

and relativeNonterminationProof =
  | RelNTLoop of loop
  | RelNTTrs of trsNonterminationProof
  | RelNTVarCond
  | RelNTRuleRemoval of trs * trs * relativeNonterminationProof
  | RelNTHyp of trsInput

and orderingConstraints = orderingConstraintElement list

and orderingConstraintElement =
    bool * bool * monotonePositions option * ignoredPositions option * rules

and monotonePositions =
  | MonAll
  | MonArgFil of argumentFilter

and ignoredPositions = argumentFilter

and orderingConstraintProof =
  | OrdRedPair of redPair
  | OrdHyp of orderingConstraints

and proof =
  | Prf of trsTerminationProof
  | PrfNT of trsNonterminationProof
  | PrfRel of relativeTerminationProof
  | PrfRelNT of relativeNonterminationProof
  | PrfDp of dpProof
  | PrfDpNT of dpNonterminationProof
  | PrfOrd of orderingConstraintProof

and url = string

and strategy =
  | StratFull
  | StratIn

and trsInput = trs * strategy * rules * rules

and dpInput = trs * dps * strategy * bool

and input =
  | InTrs of trsInput
  | InDp of dpInput
  | InOrd of orderingConstraints

and certificationProblem = input * string * proof * origin option

and origin = proofOrigin * inputOrigin

and proofOrigin = tool list * toolUser list

and tool = string * string * string * url

and toolUser = string * string * url

and inputOrigin = bool * string;;
