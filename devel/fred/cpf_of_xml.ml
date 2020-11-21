(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-08-28

from xml to the internal representation of cpf files version 2.0
******************************************************************************)

open Cpf;;
open Xml;;
open Util;;
open Libxml;;
open Error;;

let is_elt is_tag = function
  | Element (t, _, _, _) -> is_tag t
  | _ -> false;;

let bool = function
  | PCData ("true", _) -> true
  | PCData ("false", _) -> false
  | x -> error_xml x "not a boolean";;

let rec name = get_pc

and label = function
  | Element ("numberLabel", _, _, xs) -> LabInt (List.map label_number xs)
  | Element ("symbolLabel", _, _, xs) -> LabSymb (List.map symbol xs)
  | x -> error_xml x "not a label"

and label_number = get_son "number" get_nonNegativeInteger

and symbol = function
  | Element ("name", _, _, x :: _) -> SymbName (name x)
  | Element ("sharp", _, _, x :: _) -> SymbSharp (symbol x)
  | Element ("labeledSymbol", _, _, x1 :: x2 :: _) ->
      SymbLab (symbol x1, label x2)
  | x -> error_xml x "not a symbol"

and var = get_pc

and term = function
  | Element ("var", _, _, x :: _) -> TermVar (var x)
  | Element ("funapp", _, _, x :: xs) -> TermApp (symbol x, List.map arg xs)
  | x -> error_xml x "not a term"

and arg x = get_son "arg" term x

and rule = function
  | Element ("rule", _, _, x1 :: x2 :: _) -> lhs x1, rhs x2
  | x -> error_xml x "not a rule"

and lhs = get_son "lhs" term

and rhs = get_son "rhs" term

and rules = get_sons "rules" (List.map rule)

and dps = get_son "dps" rules

and trs = get_son "trs" rules

and usableRules = get_son "usableRules" rules

and number = function
  | Element ("integer", _, _, x :: _) -> NumInt (get_int x)
  | Element ("rational", _, _, x1 :: x2 :: _) ->
      NumRat (numerator x1, denominator x2)
  | x -> error_xml x "not a number"

and numerator = get_son "numerator" get_int

and denominator = get_son "denominator" get_positiveInteger

and coefficient = function
  | x when is_number x -> CoefNum (number x)
  | Element ("minusInfinity", _, _, _) -> CoefMinusInf
  | Element ("plusInfinity", _, _, _) -> CoefPlusInf
  | Element ("vector", _, _, xs) -> CoefVec (vector xs)
  | Element ("matrix", _, _, xs) -> CoefMat (matrix xs)
  | x -> error_xml x "not a coefficient"

and is_number = is_elt is_number_tag

and is_number_tag = function
  | "integer" | "rational" -> true
  | _ -> false

and vector = List.map (get_son "coefficient" coefficient)

and matrix = List.map (get_sons "vector" vector)

and polynomial = get_son "polynomial" polynomial_aux

and polynomial_aux = function
  | Element ("coefficient", _, _, x :: _) -> PolCoef (coefficient x)
  | Element ("variable", _, _, x :: _) -> PolVar (get_positiveInteger x)
  | Element ("sum", _, _, xs) -> PolSum (List.map polynomial xs)
  | Element ("product", _, _, xs) -> PolProd (List.map polynomial xs)
  | Element ("max", _, _, xs) -> PolMax (List.map polynomial xs)
  | Element ("min", _, _, xs) -> PolMin (List.map polynomial xs)
  | x -> error_xml x "not a polynomial"

and cpf_function = function
  | Element ("polynomial", _, _, x :: _) -> FunPol (polynomial_aux x)
  | x -> error_xml x "not a function"

and arity = get_son "arity" get_nonNegativeInteger

and dimension = get_son "dimension" get_positiveInteger

and strictDimension = get_son "strictDimension" get_positiveInteger

and degree = get_son "degree" get_positiveInteger

and position = get_son "position" get_positiveInteger

and argumentFilter = get_sons "argumentFilter" argumentFilter_aux

and argumentFilter_aux = List.map argumentFilterEntry

and argumentFilterEntry = function
  | Element ("argumentFilterEntry", _, _, x1 :: x2 :: x3 :: _) ->
      symbol x1, arity x2, argumentFilterEntryKind x3
  | x -> error_xml x "not an argumentFilterEntry"

and argumentFilterEntryKind = function
  | Element ("collapsing", _, _, x :: _) ->
      ArgFilCollaps (get_positiveInteger x)
  | Element ("nonCollapsing", _, _, xs) ->
      ArgFilNonCollaps (List.map position xs)
  | x -> error_xml x "not an argumentFilter"

and domain x = get_son "domain" domain_aux x

and domain_aux = function
  | Element ("naturals", _, _, _) -> DomNat
  | Element ("integers", _, _, _) -> DomtInt
  | Element ("rationals", _, _, x :: _) -> DomRat (get_son "delta" number)
  | Element ("arctic", _, _, x :: _) -> DomArctic (domain x)
  | Element ("tropical", _, _, x :: _) -> DomTropical (domain x)
  | Element ("matrices", _, _, x1 :: x2 :: x3 :: _) ->
      DomMat (dimension x1, strictDimension x2, domain x3)
  | x -> error_xml x "not a domain"

and redPair = get_son "redPair" redPair_aux

and redPair_aux = function
  | Element ("interpretation", _, _, x :: xs) ->
      RedInt (redPair_type x, List.map redPair_interpret xs)
  | Element ("pathOrder", _, _, x :: []) -> RedRPO (statusPrecedence x, [])
  | Element ("pathOrder", _, _, x1 :: x2 :: _) ->
      RedRPO (statusPrecedence x1, argumentFilter x2)
  | x -> error_xml x "not a redPair"

and redPair_type = get_son "type" redPair_type_aux

and redPair_type_aux = function
  | Element ("polynomial", _, _, x1 :: x2 :: _) ->
      TypPol (domain x1, degree x2)
  | Element ("matrixInterpretation", _, _, x1 :: x2 :: x3 :: _) ->
      TypMat (domain x1, dimension x2, strictDimension x3)
  | x -> error_xml x "not an interpretation type"

and redPair_interpret = function
  | Element ("interpret", _, _, x1 :: x2 :: x3 :: _) ->
      symbol x1, arity x2, cpf_function x3
  | x -> error_xml x "not a redPair"

and statusPrecedence =
  get_sons "statusPrecedence" (List.map statusPrecedenceEntry)

and statusPrecedenceEntry = function
  | Element ("statusPrecedenceEntry", _, _, x1 :: x2 :: x3 :: x4 :: _) ->
      symbol x1, arity x2, precedence x3, status x4
  | x -> error_xml x "not a statusPrecedenceEntry"

and precedence = get_son "precedence" get_nonNegativeInteger

and status = function
  | Element ("lex", _, _, _) -> StatLex
  | Element ("mul", _, _, _) -> StatMul
  | x -> error_xml x "not a status"

and arithFunction x = get_son "arithFunction" arithFunction_aux x

and arithFunction_aux = function
  | Element ("natural", _, _, x :: _) -> ArithNat (get_nonNegativeInteger x)
  | Element ("variable", _, _, x :: _ ) -> ArithVar (get_positiveInteger x)
  | Element ("sum", _, _, xs) -> ArithSum (List.map arithFunction xs)
  | Element ("product", _, _, xs) -> ArithProd (List.map arithFunction xs)
  | Element ("min", _, _, xs) -> ArithMin (List.map arithFunction xs)
  | Element ("max", _, _, xs) -> ArithMax (List.map arithFunction xs)
  | x -> error_xml x "not an arithFunction"

and model = function
  | Element ("finiteModel", _, _, xs) -> ModFin (finiteModel xs)
  | Element ("rootLabeling", _, _, _) -> ModRootLab
  | x -> error_xml x "not a model"

and finiteModel = finiteModel_aux 0 TOrdNone []

and finiteModel_aux s o is = function
  | [] -> s, o, List.rev is
  | Element ("carrierSize", _, _, x :: _) :: xs' ->
      finiteModel_aux (get_positiveInteger x) o is l xs'
  | Element ("tupleOrder", _, _, x :: _) :: xs' ->
      finiteModel_aux s TOrdPointWise is l xs'
  | Element ("interpret", _, _, x1 :: x2 :: x3 :: _) :: xs' ->
      finiteModel_aux s o ((symbol x1, arity x2, arithFunction x3) :: is) l xs'
  | Element ("labeling", _, _, _) :: xs' ->
      finiteModel_aux s o is xs'
  | x :: _ -> error_xml x "not a finiteModel";;
 
and modelDef = function
  | Element ("interpret", _, _, x1 :: x2 :: x3 :: _) ->
      symbol x1, arity x2, arithFunction x3
  | x -> error_xml x "not a model"

and dpProof = function
  | Element ("pIsEmpty", _, _, _) -> DpEmpty
  | Element ("depGraphProc", _, _, xs) -> DpGraph (depGraphProc xs)
  | Element ("redPairProc", _, _, xs) -> DpRed (redPairProc xs)
  | Element ("redPairUrProc", _, _, xs) -> DpRedUR (redPairUrProc xs)
  | Element ("monoRedPairProc", _, _, xs) -> DpRedMono (monoRedPairProc xs)
  | Element ("monoRedPairUrProc", _, _, xs) ->
      DpRedMonoUR (monoRedPairUrProc xs)
  | Element ("subtermProc", _, _, xs) -> DpSubterm (subtermProc xs)
  | Element ("semlabProc", _, _, x1 :: x2 :: x3 :: x4 :: _) ->
      DpSemLab (model x1, dps x2, trs x3, dpProof x4)
  | Element ("unlabProc", _, _, x1 :: x2 :: x3 :: _) ->
      DpUnlab (dps x1, trs x2, dpProof x3)
  | Element ("sizeChangeCriterion", _, _, x :: xs) ->
      DpSC (sc x, List.map scg xs)
  | Element ("flatContextClosureProc", _, _, xs) ->
      DpFlatCC (flatContextClosureProc xs)
  | Element ("argumentFilterProc", _, _, x1 :: x2 :: x3 :: x4 :: _) ->
      DpArgFilter (argumentFilter x1, dps x2, trs x3, dpProof x4)
  | Element ("finitenessAssumption", _, _, x :: _) -> DpHyp (dpInput x)
  | x -> error_xml x "not a dpProof"

and depGraphProc = List.map component

and component = function
  | Element ("component", _, _, x1 :: x2 :: xs) ->
      dps x1, realScc x2, component_aux [] None xs
  | x -> error_xml x "not a component"

and realScc = get_son "realScc" bool

and component_aux l p = function
  | [] -> l, p
  | Element ("arcs", _, _, xs) :: _ ->
      component_aux (List.map forwardArcs xs) p
  | Element ("dpProof", _, _, x :: _) -> component_aux l (Some (dpProof x))
  | x :: _ -> error_xml x "not a component"

and forwardArc = function
  | Element ("forwardArc", _, _, x :: _) -> get_positiveInteger x
  | x -> error_xml x "not a forwardArc"

and redPairProc = redPairProc_aux [] ? [] ?

and redPairProc_aux ocs ocp dps p = function
  | [] -> ocs, ocp, dps, p
  | Element ("orderingConstraints", _, _, xs) :: xs' ->
      redPairProc_aux (orderingConstraints xs) ocp dps p xs'
  | Element ("orderingConstraintProof", _, _, x :: _) :: xs'
      redPairProc_aux ocs (orderingConstraintProof x) dps p xs'
  | Element ("dps", _, _, xs) :: xs' ->
      redPairProc_aux ocs ocp (rules xs) p xs'
  | Element ("dpProof", _, _, x :: _) ->
      redPairProc_aux ocs ocp dps (dpProof x) xs'
  | x :: _ -> error_xml "not a redPairProc"

and redPairUrProc = redPairUrProc_aux [] ? [] [] ?

and redPairUrProc_aux ocs ocp dps urs p = function
  | [] -> ocs, ocp, dps, urs, p
  | Element ("orderingConstraints", _, _, xs) :: xs' ->
      redPairUrProc_aux (orderingConstraints xs) ocp dps urs p xs'
  | Element ("orderingConstraintProof", _, _, x :: _) :: xs'
      redPairUrProc_aux ocs (orderingConstraintProof x) dps urs p xs'
  | Element ("dps", _, _, xs) :: xs' ->
      redPairUrProc_aux ocs ocp (rules xs) urs p xs'
  | Element ("usableRules", _, _, xs) :: xs' ->
      redPairUrProc_aux ocs ocp (rules xs) p xs'
  | Element ("dpProof", _, _, x :: _) ->
      redPairUrProc_aux ocs ocp dps urs (dpProof x) xs'
  | x :: _ -> error_xml "not a redPairUrProc"

and monoRedPairProc = monoRedPairProc_aux [] ? [] [] ?

and monoRedPairProc_aux ocs ocp dps trs p = function
  | [] -> ocs, ocp, dps, trs, p
  | Element ("orderingConstraints", _, _, xs) :: xs' ->
      monoRedPairProc_aux (orderingConstraints xs) ocp dps trs p xs'
  | Element ("orderingConstraintProof", _, _, x :: _) :: xs'
      monoRedPairProc_aux ocs (orderingConstraintProof x) dps trs p xs'
  | Element ("dps", _, _, xs) :: xs' ->
      monoRedPairProc_aux ocs ocp (rules xs) trs p xs'
  | Element ("trs", _, _, xs) :: xs' ->
      monoRedPairProc_aux ocs ocp dps (rules xs) p xs'
  | Element ("dpProof", _, _, x :: _) ->
      monoRedPairProc_aux ocs ocp dps trs (dpProof x) xs'
  | x :: _ -> error_xml "not a monoRedPairProc"

and monoRedPairUrProc = monoRedPairUrProc_aux [] ? [] [] [] ?

and monoRedPairUrProc_aux ocs ocp dps trs urs p = function
  | [] -> ocs, ocp, dps, trs, urs, p
  | Element ("orderingConstraints", _, _, xs) :: xs' ->
      monoRedPairUrProc_aux (orderingConstraints xs) ocp dps trs urs p xs'
  | Element ("orderingConstraintProof", _, _, x :: _) :: xs'
      monoRedPairUrProc_aux ocs (orderingConstraintProof x) dps trs urs p xs'
  | Element ("dps", _, _, xs) :: xs' ->
      monoRedPairUrProc_aux ocs ocp (rules xs) trs urs p xs'
  | Element ("trs", _, _, xs) :: xs' ->
      monoRedPairUrProc_aux ocs ocp dps (rules xs) urs p xs'
  | Element ("usableRules", _, _, xs) :: xs' ->
      monoRedPairUrProc_aux ocs ocp dps trs (rules xs) p xs'
  | Element ("dpProof", _, _, x :: _) ->
      monoRedPairUrProc_aux ocs ocp dps trs urs (dpProof x) xs'
  | x :: _ -> error_xml "not a monoRedPairUrProc"

and subtermProc = subtermProc_aux ? [] [] ?

and subtermProc_aux af prs dps p = function
  | [] -> af, List.rev prs, dps, p
  | Element ("argumentFilter", _, _, xs) :: xs' ->
      subtermProc_aux (argumentFilter_aux xs) prs dps p xs'
  | Element ("projectedRewriteSequence", _, _, x1 :: x2 :: _) :: xs'
      subtermProc_aux af ((rule x1, rewriteSequence x2) :: prs) dps p xs'
  | Element ("dps", _, _, xs) :: xs' ->
      subtermProc_aux af prs (rules xs) p xs'
  | Element ("dpProof", _, _, x :: _) ->
      subtermProc_aux af prs dps (dpProof x) xs'
  | x :: _ -> error_xml "not a subtermProc"

and sc = function
  | Element ("subtermCriterion", _, _, _) -> SCSubterm
  | Element ("reductionPair", _, _, x1 :: x2 :: _) ->
      SCRedPair (redPair x1, usableRules x2)
  | x -> error_xml x "not a sizeChangeCriterion"

and scg = function
  | Element ("sizeChangeGraph", _, _, x :: xs) ->
      rule x, List.map edge xs
  | x -> error_xml x "not a sizeChangeGraph"

and edge = function
  | Element ("edge", _, _, x1 :: x2 :: x3 :: _) ->
      position x1, edge_kind x2, position x3
  | x -> error_xml x "not an edge"

and edge_kind = get_son "strict" bool

and flatContextClosureProc = flatContextClosureProc_aux None [] [] [] ?

and flatContextClosureProc_aux f cs dps trs p = function
  | [] -> f, cs, dps, trs, p
  | Element ("freshSymbol", _, _, x :: _) :: xs' ->
      flatContextClosureProc_aux (Some (symbol x)) cs dps trs p xs'
  | Element ("flatContexts", _, _, xs) :: xs' ->
      flatContextClosureProc_aux f (List.map context xs) dps trs p xs'
  | Element ("dps", _, _, xs) :: xs' ->
      flatContextClosureProc_aux f cs (rules xs) trs p xs'
  | Element ("trs", _, _, xs) :: xs' ->
      flatContextClosureProc_aux f cs dps (rules xs) p xs'
  | Element ("dpProof", _, _, x :: _) ->
      flatContextClosureProc_aux f cs dps trs (dpProof x) xs'
  | x :: _ -> error_xml "not a flatContextClosureProc"

and substitution = List.map substEntry

and substEntry = function
  | Element ("substEntry", _, _, x1 :: x2 :: _) -> var x1, term x2
  | x -> error_xml x "not a substEntry"

and var = get_son "var" get_pc

and context = function
  | Element ("box", _, _, _) -> ContEmpty
  | Element ("funContext", _, _, x1 :: x2 :: x3 :: x4 :: _) ->
      ContApp (symbol x1, before x2, context x3, after x4)
  | x -> error_xml x "not a context"

and before = get_sons "before" terms

and after = get_sons "after" terms

and terms = List.map term

and rewriteSequence = function
  | Element ("rewriteSequence", _, _, x :: xs) ->
      startTerm x, List.map rewriteStep xs
  | x -> error_xml x "not a rewriteSequence"

and startTerm = get_son "startTerm" term

and rewriteStep = rewriteStep_aux

and rewriteStep_aux p r b t = function
  | [] -> p, r, b, t
  | Element ("positionInTerm", _, _, xs) :: xs' ->
      rewriteStep_aux (List.map position xs) r b t xs'
  | Element ("rule", _, _, x :: _) :: xs' ->
      rewriteStep_aux p (rule



and positionInTerm = get_sons "positionInTerm" positions



and is_context_tag = function
  | "box" | "funContext" -> true
  | _ -> false

and is_context = is_elt is_context_tag

and flat_contexts = get_sons "flatContexts" (List.map context)

and trsTerminationProof = function
  | Element ("rIsEmpty", _, _, _) -> TrsEmpty
  | Element ("ruleRemoval", _, _, x1 :: x2 :: x3 :: _) ->
      TrsRuleRemoval (redPair x1, trs x2, trsTerminationProof x3)
  | Element ("dpTrans", _, _, x1 :: x2 :: x3 :: _) ->
      TrsDpTrans (dps x1, get_son "markedSymbols" bool x2, dpProof x3)
  | Element ("semlab", _, _, x1 :: x2 :: x3 :: _) ->
      TrsSemLab (get_son "model" model x1, trs x2, trsTerminationProof x3)
  | Element ("unlab", _, _, x1 :: x2 :: _) ->
      TrsUnlab (trs x1, trsTerminationProof x2)
  | Element ("stringReversal", _, _, x1 :: x2 :: _) ->
      TrsRev (trs x1, trsTerminationProof x2)
  | Element ("flatContextClosure", _, _, x1 :: x2 :: x3 :: _) ->
      TrsFlatCC (flat_contexts x1, trs x2, trsTerminationProof x3)
  | x -> error_xml x "not a trsTerminationProof"

and is_trsTerminationProof_tag = function
  | "rIsEmpty" | "ruleRemoval" | "dpTrans" | "semlab" | "unlab"
  | "stringReversal" | "flatContextClosure" -> true
  | _ -> false

and is_trsTerminationProof = is_elt is_trsTerminationProof_tag




and loop_aux rs s c = function
  | [] -> TrsNTLoop (List.rev rs, s, c)
  | Element ("redex", _, ats, x1 :: x2 :: x3 :: _) :: xs ->
      and r = term x1, positionInTerm x2, rule x3, List.mem ("type","rel") ats 
      in loop_aux (r :: rs) s c xs
  | Element ("substitution", _, _, xs') :: xs ->
      loop_aux rs (substitution xs') c xs
  | x :: xs when is_context x -> loop_aux rs s (context x) xs
  | x :: _ -> error_xml x "not a trsNonterminationProof"

and loop = loop_aux [] [] ContEmpty

and trsNonterminationProof = function
  | Element ("variableConditionViolated", _, _, _) -> TrsNTVarCond
  | Element ("loop", _, _, xs) -> loop xs
  | x -> error_xml x "not a trsNonterminationProof"








and orderingConstraints = List.map orderingConstraintElement

and orderingConstraintElement = function
  | Element ("orderingConstraintElement", _, _, x1 :: x2 :: xs) ->
      bool x1 :: bool x2 :: oce_elts None None [] xs
  | x -> error_xml x "not an orderingConstraintElement"

and oce_elts mps ips rs = function
  | [] -> mps, ips, List.rev rs
  | Element ("monotonePositions", _, _, x :: _) :: xs ->
      oce_elts (Some (monotone_positions x)) ips rs xs
  | Element ("ignoredPositions", _, _, x :: _) :: _ ->
      oce_elts mps (Some (argumentFilter x)) rs xs
  | x :: xs -> oce_elts mps ips (rule x :: rs) xs

and monotonePositions = function
  | Element ("everySymbolAndPosition", _, _, _) -> MonAll
  | x -> MonArgFil (argumentFilter x)

and orderingConstraintProof = function
  | Element ("redPair", _, _, x :: _) -> OrdRedPair (redPair_aux x)
  | Element ("satisfiableAssumption", _, _, x :: _) ->
      OrdHyp (orderingConstraints x)
  | x -> error_xml x "not an orderingConstraintProof"

and proof = function
  | Element ("trsTerminationProof", _, _, x :: _) ->
      Prf (trsTerminationProof x)
  | Element ("trsNonterminationProof", _, _, x :: _) ->
      Prf (trsNonterminationProof x)
  | Element ("relativeTerminationProof", _, _, x :: _) ->
      Prf (relativeTerminationProof x)
  | Element ("relativeNonterminationProof", _, _, x :: _) ->
      Prf (relativeNonterminationProof x)
  | Element ("dpProof", _, _, x :: _) ->
      Prf (dpProof x)
  | Element ("dpNonterminationProof", _, _, x :: _) ->
      Prf (dpNonterminationProof x)
  | Element ("orderingConstraintProof", _, _, x :: _) ->
      Prf (orderingConstraintProof x)
  | x -> error_xml x "not a proof"

and url = get_son "url" get_pc

and trsInput = trsInput_aux [] StratFull [] []

and trsInput_aux rs s es rrs = function
  | [] -> InTrs (rs, s, es, rrs)
  | Element ("trs", _, _, x :: _) :: xs ->
      trsInput_aux (rules x) s es rrs xs
  | Element ("strategy", _, _, x :: _) :: xs ->
      trsInput_aux rs (strategy x) es rrs xs
  | Element ("equations", _, _, x :: _) :: xs ->
      trsInput_aux rs s (rules x) rrs xs
  | Element ("relativeRules", _, _, x :: _) :: xs ->
      trsInput_aux rs s es (rules x) xs
  | x :: _ -> error_xml x "not a trsInput"

and strategy = function
  | Element ("innermost", _, _, _) -> StratIn
  | x -> error_xml x "not a strategy"

and dpInput = dpInput_aux [] StratFull [] []

and dpInput_aux rs dps s b = function
  | [] -> InDp (rs, dps, s, b)
  | Element ("trs", _, _, x :: _) :: xs ->
      dpInput_aux (rules x) dps s b
  | Element ("dps", _, _, x :: _) :: xs ->
      dpInput_aux rs (dps x) s b
  | Element ("strategy", _, _, x :: _) :: xs ->
      dpInput_aux rs dps (strategy x) b
  | Element ("minimal", _, _, x :: _) :: xs ->
      dpInput_aux rs dps s (bool x)
  | x :: _ -> error_xml x "not a dpInput"

and certificationProblem = function
  | Element ("certificationProblem", _, _, x1 :: x2 :: x3 :: xs) ->
      input x1, cpfVersion x2, proof x3, origin xs
  | x -> error_xml x "not a certificationProblem"

and input = function
  | Element ("trsInput", _, _, xs) -> trsInput xs
  | Element ("dpInput", _, _, xs) -> dpInput xs
  | Element ("orderingConstraints", _, _, xs) -> orderingConstraints xs
  | x -> error_xml x "not an input"

and cpfVersion = get_son "cpfVersion" get_pc

and origin = function
  | [] -> None
  | Element ("origin", _, _, x1 :: x2 :: _) :: _ ->
      Some (proofOrigin x1, inputOrigin x2)
  | x :: _ -> error_xml x "not an origin"

and proofOrigin = get_sons "proofOrigin" (proofOrigin_aux [] [])

and proofOrigin_aux ts tus = function
  | [] -> ts, tus
  | Element ("tool", _, _, xs') :: xs ->
      proofOrigin_aux (tool xs' :: ts) tus xs
  | Element ("toolUser", _, _, x1 :: x2 :: []) :: xs ->
      and tu = firstName x1, lastName x2, ""
      in proofOrigin_aux ts (tu :: tus) xs
  | Element ("toolUser", _, _, x1 :: x2 :: x3 :: _) :: xs ->
      and tu = firstName x1, lastName x2, url x3
      in proofOrigin_aux ts (tu :: tus) xs
  | x :: _ -> error_xml x "not a proofOrigin"

and tool = tool_aux "" "" "" ""

and tool_aux n v s u = function
  | [] -> n, v, s, u
  | Element ("name", _, _, x :: _) :: xs -> tool_aux (get_pc x) v s u xs
  | Element ("version", _, _, x :: _) :: xs -> tool_aux n (get_pc x) s u xs
  | Element ("strategy", _, _, x :: _) :: xs -> tool_aux n v (get_pc x) u xs
  | Element ("url", _, _, x :: _) :: xs -> tool_aux n v s (get_pc x) xs
  | x :: _ -> error_xml x "not a tool"

and firstName = get_son "firstName" get_pc

and lastName = get_son "lastName" get_pc

and inputOrigin = get_sons "inputOrigin" (inputOrigin_aux false "")

and inputOrigin_aux b s = function
  | [] -> b, s
  | Element ("tpdb-reference", _, _, _) :: xs -> inputOrigin_aux true s xs
  | Element ("source", _, _, x :: _) :: xs -> inputOrigin_aux b (get_pc x) xs
  | x :: _ -> error_xml x "not an inputOrigin";;
