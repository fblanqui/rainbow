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
  | PCData (s, _) -> bool_of_string s
  | x -> error_xml x "not a boolean";;

let get s = function
  | Some v -> v
  | None -> error_fmt ("missing " ^ s)

let rec name = get_pc

and label = function
  | Element ("numberLabel", _, _, xs) -> LabInt (List.map label_number xs)
  | Element ("symbolLabel", _, _, xs) -> LabSymb (List.map symbol xs)
  | x -> error_xml x "not a label"

and label_number = get_first_son "number" get_nonNegativeInteger

and symbol = function
  | Element ("name", _, _, x :: _) -> SymbName (name x)
  | Element ("sharp", _, _, x :: _) -> SymbSharp (symbol x)
  | Element ("labeledSymbol", _, _, x1 :: x2 :: _) ->
      SymbLab (symbol x1, label x2)
  | x -> error_xml x "not a symbol"

and var = get_first_son "var" get_pc 

and term = function
  | Element ("var", _, _, x :: _) -> TermVar (get_pc x)
  | Element ("funapp", _, _, x :: xs) -> TermApp (symbol x, List.map arg xs)
  | x -> error_xml x "not a term"

and arg x = get_first_son "arg" term x

and rule = function
  | Element ("rule", _, _, x1 :: x2 :: _) -> lhs x1, rhs x2
  | x -> error_xml x "not a rule"

and lhs x = get_first_son "lhs" term x

and rhs x = get_first_son "rhs" term x

and rules x = get_sons "rules" (List.map rule) x

and dps x = get_first_son "dps" rules x

and trs x = get_first_son "trs" rules x

and usableRules x = get_first_son "usableRules" rules x

and number = function
  | Element ("integer", _, _, x :: _) -> NumInt (get_int x)
  | Element ("rational", _, _, x1 :: x2 :: _) ->
      NumRat (numerator x1, denominator x2)
  | x -> error_xml x "not a number"

and numerator = get_first_son "numerator" get_int

and denominator = get_first_son "denominator" get_positiveInteger

and coefficient = function
  | x when is_number x -> CoefNum (number x)
  | Element ("minusInfinity", _, _, _) -> CoefMinusInf
  | Element ("plusInfinity", _, _, _) -> CoefPlusInf
  | Element ("vector", _, _, xs) -> CoefVec (vector xs)
  | Element ("matrix", _, _, xs) -> CoefMat (matrix xs)
  | x -> error_xml x "not a coefficient"

and is_number x = is_elt is_number_tag x

and is_number_tag = function
  | "integer" | "rational" -> true
  | _ -> false

and vector xs = List.map (get_first_son "coefficient" coefficient) xs

and matrix xs = List.map (get_sons "vector" vector) xs

and polynomial x = get_first_son "polynomial" polynomial_aux x

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

and arity x = get_first_son "arity" get_nonNegativeInteger x

and dimension x = get_first_son "dimension" get_positiveInteger x

and strictDimension x = get_first_son "strictDimension" get_positiveInteger x

and degree x = get_first_son "degree" get_nonNegativeInteger x

and position x = get_first_son "position" get_positiveInteger x

and argumentFilter x =
    get_sons "argumentFilter" (List.map argumentFilterEntry) x

and argumentFilterEntry = function
  | Element ("argumentFilterEntry", _, _, x1 :: x2 :: x3 :: _) ->
      symbol x1, arity x2, argumentFilterEntryKind x3
  | x -> error_xml x "not an argumentFilterEntry"

and argumentFilterEntryKind = function
  | Element ("collapsing", _, _, x :: _) ->
      ArgFilCollaps (get_positiveInteger x)
  | Element ("nonCollapsing", _, _, xs) ->
      ArgFilNonCollaps (List.map position xs)
  | x -> error_xml x "not an argumentFilterEntry"

and domain x = get_first_son "domain" domain_aux x

and domain_aux = function
  | Element ("naturals", _, _, _) -> DomNat
  | Element ("integers", _, _, _) -> DomInt
  | Element ("rationals", _, _, x :: _) -> DomRat (delta x)
  | Element ("arctic", _, _, x :: _) -> DomArctic (domain x)
  | Element ("tropical", _, _, x :: _) -> DomTropical (domain x)
  | Element ("matrices", _, _, x1 :: x2 :: x3 :: _) ->
      DomMat (dimension x1, strictDimension x2, domain x3)
  | x -> error_xml x "not a domain"

and delta x = get_first_son "delta" number x

and redPair x = get_first_son "redPair" redPair_aux x

and redPair_aux = function
  | Element ("interpretation", _, _, x :: xs) ->
      RedInt (redPair_type x, List.map redPair_interpret xs)
  | Element ("pathOrder", _, _, x :: []) -> RedRPO (statusPrecedence x, [])
  | Element ("pathOrder", _, _, x1 :: x2 :: _) ->
      RedRPO (statusPrecedence x1, argumentFilter x2)
  | x -> error_xml x "not a redPair"

and redPair_type x = get_first_son "type" redPair_type_aux x

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

and statusPrecedence x =
  get_sons "statusPrecedence" (List.map statusPrecedenceEntry) x

and statusPrecedenceEntry = function
  | Element ("statusPrecedenceEntry", _, _, x1 :: x2 :: x3 :: x4 :: _) ->
      symbol x1, arity x2, precedence x3, status x4
  | x -> error_xml x "not a statusPrecedenceEntry"

and precedence x = get_first_son "precedence" get_nonNegativeInteger x

and status = function
  | Element ("lex", _, _, _) -> StatLex
  | Element ("mul", _, _, _) -> StatMul
  | x -> error_xml x "not a statusPrecedenceEntry"

and arithFunction x = get_first_son "arithFunction" arithFunction_aux x

and arithFunction_aux = function
  | Element ("natural", _, _, x :: _) -> ArithNat (get_nonNegativeInteger x)
  | Element ("variable", _, _, x :: _ ) -> ArithVar (get_positiveInteger x)
  | Element ("sum", _, _, xs) -> ArithSum (List.map arithFunction xs)
  | Element ("product", _, _, xs) -> ArithProd (List.map arithFunction xs)
  | Element ("min", _, _, xs) -> ArithMin (List.map arithFunction xs)
  | Element ("max", _, _, xs) -> ArithMax (List.map arithFunction xs)
  | x -> error_xml x "not an arithFunction"

and model x = get_first_son "model" model_aux x

and model_aux = function
  | Element ("finiteModel", _, _, xs) -> finiteModel xs
  | Element ("rootLabeling", _, _, _) -> ModRootLab
  | x -> error_xml x "not a model"

and finiteModel xs = finiteModel_aux 0 TOrdNone [] xs

and finiteModel_aux s o is = function
  | [] -> ModFin (s, o, List.rev is)
  | Element ("carrierSize", _, _, x :: _) :: xs' ->
      finiteModel_aux (get_positiveInteger x) o is xs'
  | Element ("tupleOrder", _, _, x :: _) :: xs' ->
      finiteModel_aux s (tupleOrder x) is xs'
  | Element ("interpret", _, _, x1 :: x2 :: x3 :: _) :: xs' ->
      finiteModel_aux s o ((symbol x1, arity x2, arithFunction x3) :: is) xs'
  | Element ("labeling", _, _, _) :: xs' ->
      finiteModel_aux s o is xs'
  | x :: _ -> error_xml x "not a finiteModel"

and tupleOrder = function
  | Element ("pointWise", _, _, _) -> TOrdPointWise
  | x -> error_xml x "not a tupleOrder"

and dpProof x = get_first_son "dpProof" dpProof_aux x

and dpProof_aux = function
  | Element ("pIsEmpty", _, _, _) -> DpEmpty
  | Element ("depGraphProc", _, _, xs) -> DpGraph (List.map component xs)
  | Element ("redPairProc", _, _, xs) -> redPairProc xs
  | Element ("redPairUrProc", _, _, xs) -> redPairUrProc xs
  | Element ("monoRedPairProc", _, _, xs) -> monoRedPairProc xs
  | Element ("monoRedPairUrProc", _, _, xs) -> monoRedPairUrProc xs
  | Element ("subtermProc", _, _, xs) -> subtermProc xs
  | Element ("semlabProc", _, _, x1 :: x2 :: x3 :: x4 :: _) ->
      DpSemLab (model x1, dps x2, trs x3, dpProof x4)
  | Element ("unlabProc", _, _, x1 :: x2 :: x3 :: _) ->
      DpUnlab (dps x1, trs x2, dpProof x3)
  | Element ("sizeChangeProc", _, _, x :: xs) ->
      DpSC (sizeChangeProc_aux x, List.map sizeChangeGraph xs)
  | Element ("flatContextClosureProc", _, _, xs) -> flatContextClosureProc xs
  | Element ("argumentFilterProc", _, _, x1 :: x2 :: x3 :: x4 :: _) ->
      DpArgFilter (argumentFilter x1, dps x2, trs x3, dpProof x4)
  | Element ("finitenessAssumption", _, _, x :: _) -> DpHyp (dpInput x)
  | x -> error_xml x "not a dpProof"

and component = function
  | Element ("component", _, _, x1 :: x2 :: xs) ->
      let l, p = component_aux [] None xs in dps x1, realScc x2, l, p 
  | x -> error_xml x "not a component"

and realScc = get_first_son "realScc" bool

and component_aux l p = function
  | [] -> l, p
  | Element ("arcs", _, _, xs) ::  xs' ->
      component_aux (List.map forwardArc xs) p xs'
  | Element ("dpProof", _, _, x :: _) :: xs' ->
      component_aux l (Some (dpProof_aux x)) xs'
  | x :: _ -> error_xml x "not a component"

and forwardArc = function
  | Element ("forwardArc", _, _, x :: _) -> get_positiveInteger x
  | x -> error_xml x "not a forwardArc"

and redPairProc xs = redPairProc_aux [] None [] None xs

and redPairProc_aux ocs ocp dps p = function
  | [] -> DpRed (ocs, get "orderingConstraintProof" ocp, dps, get "dpProof" p)
  | Element ("orderingConstraints", _, _, xs) :: xs' ->
      redPairProc_aux (List.map orderingConstraintElement xs) ocp dps p xs'
  | Element ("orderingConstraintProof", _, _, x :: _) :: xs' ->
      redPairProc_aux ocs (Some (orderingConstraintProof_aux x)) dps p xs'
  | Element ("dps", _, _, x :: _) :: xs' ->
      redPairProc_aux ocs ocp (rules x) p xs'
  | Element ("dpProof", _, _, x :: _) :: xs' ->
      redPairProc_aux ocs ocp dps (Some (dpProof_aux x)) xs'
  | x :: _ -> error_xml x "not a redPairProc"

and redPairUrProc xs = redPairUrProc_aux [] None [] [] None xs

and redPairUrProc_aux ocs ocp dps urs p = function
  | [] -> DpRedUR
      (ocs, get "orderingConstraintProof" ocp, dps, urs, get "dpProof" p)
  | Element ("orderingConstraints", _, _, xs) :: xs' -> redPairUrProc_aux
      (List.map orderingConstraintElement xs) ocp dps urs p xs'
  | Element ("orderingConstraintProof", _, _, x :: _) :: xs' ->
      redPairUrProc_aux
	ocs (Some (orderingConstraintProof_aux x)) dps urs p xs'
  | Element ("dps", _, _, x :: _) :: xs' ->
      redPairUrProc_aux ocs ocp (rules x) urs p xs'
  | Element ("usableRules", _, _, x :: _) :: xs' ->
      redPairUrProc_aux ocs ocp dps (rules x) p xs'
  | Element ("dpProof", _, _, x :: _) :: xs' ->
      redPairUrProc_aux ocs ocp dps urs (Some (dpProof_aux x)) xs'
  | x :: _ -> error_xml x "not a redPairUrProc"

and monoRedPairProc xs = monoRedPairProc_aux [] None [] [] None xs

and monoRedPairProc_aux ocs ocp dps trs p = function
  | [] -> DpRedMono
      (ocs, get "orderingConstraintProof" ocp, dps, trs, get "dpProof" p)
  | Element ("orderingConstraints", _, _, xs) :: xs' -> monoRedPairProc_aux
      (List.map orderingConstraintElement xs) ocp dps trs p xs'
  | Element ("orderingConstraintProof", _, _, x :: _) :: xs' ->
      monoRedPairProc_aux
	ocs (Some (orderingConstraintProof_aux x)) dps trs p xs'
  | Element ("dps", _, _, x :: _) :: xs' ->
      monoRedPairProc_aux ocs ocp (rules x) trs p xs'
  | Element ("trs", _, _, x :: _) :: xs' ->
      monoRedPairProc_aux ocs ocp dps (rules x) p xs'
  | Element ("dpProof", _, _, x :: _) :: xs' ->
      monoRedPairProc_aux ocs ocp dps trs (Some (dpProof_aux x)) xs'
  | x :: _ -> error_xml x "not a monoRedPairProc"

and monoRedPairUrProc xs = monoRedPairUrProc_aux [] None [] [] [] None xs

and monoRedPairUrProc_aux ocs ocp dps trs urs p = function
  | [] -> DpRedMonoUR
      (ocs, get "orderingConstraintProof" ocp, dps, trs, urs, get "dpProof" p)
  | Element ("orderingConstraints", _, _, xs) :: xs' -> monoRedPairUrProc_aux
      (List.map orderingConstraintElement xs) ocp dps trs urs p xs'
  | Element ("orderingConstraintProof", _, _, x :: _) :: xs' ->
      monoRedPairUrProc_aux
	ocs (Some (orderingConstraintProof_aux x)) dps trs urs p xs'
  | Element ("dps", _, _, x :: _) :: xs' ->
      monoRedPairUrProc_aux ocs ocp (rules x) trs urs p xs'
  | Element ("trs", _, _, x :: _) :: xs' ->
      monoRedPairUrProc_aux ocs ocp dps (rules x) urs p xs'
  | Element ("usableRules", _, _, x :: _) :: xs' ->
      monoRedPairUrProc_aux ocs ocp dps trs (rules x) p xs'
  | Element ("dpProof", _, _, x :: _) :: xs' ->
      monoRedPairUrProc_aux ocs ocp dps trs urs (Some (dpProof_aux x)) xs'
  | x :: _ -> error_xml x "not a monoRedPairUrProc"

and subtermProc xs = subtermProc_aux [] [] [] None xs

and subtermProc_aux af prs dps p = function
  | [] -> DpSubterm (af, List.rev prs, dps, get "dpProof" p)
  | Element ("argumentFilter", _, _, xs) :: xs' ->
      subtermProc_aux (List.map argumentFilterEntry xs) prs dps p xs'
  | Element ("projectedRewriteSequence", _, _, x1 :: x2 :: _) :: xs' ->
      subtermProc_aux af ((rule x1, rewriteSequence x2) :: prs) dps p xs'
  | Element ("dps", _, _, x :: _) :: xs' ->
      subtermProc_aux af prs (rules x) p xs'
  | Element ("dpProof", _, _, x :: _) :: xs' ->
      subtermProc_aux af prs dps (Some (dpProof_aux x)) xs'
  | x :: _ -> error_xml x "not a subtermProc"

and sizeChangeProc_aux = function
  | Element ("subtermCriterion", _, _, _) -> SCSubterm
  | Element ("reductionPair", _, _, xs) -> sizeChangeProc_rp xs
  | x -> error_xml x "not a sizeChangeProc"

and sizeChangeProc_rp xs = sizeChangeProc_rp_aux [] None [] xs

and sizeChangeProc_rp_aux ocs ocp urs = function
  | [] -> SCRedPair (ocs, get "orderingConstraintProof" ocp, urs)
  | Element ("orderingConstraints", _, _, xs) :: xs' ->
      sizeChangeProc_rp_aux (List.map orderingConstraintElement xs) ocp urs xs'
  | Element ("orderingConstraintProof", _, _, x :: _) :: xs' ->
      sizeChangeProc_rp_aux ocs (Some (orderingConstraintProof_aux x)) urs xs'
  | Element ("usableRules", _, _, x :: _) :: xs' ->
      sizeChangeProc_rp_aux ocs ocp (rules x) xs'
  | x :: _ -> error_xml x "not a sizeChangeProc"

and sizeChangeGraph = function
  | Element ("sizeChangeGraph", _, _, x :: xs) -> rule x, List.map edge xs
  | x -> error_xml x "not a sizeChangeGraph"

and edge = function
  | Element ("edge", _, _, x1 :: x2 :: x3 :: _) ->
      position x1, strict x2, position x3
  | x -> error_xml x "not an edge"

and strict x = get_first_son "strict" bool x

and flatContextClosureProc xs =
	flatContextClosureProc_aux None [] [] [] None xs

and flatContextClosureProc_aux f cs dps trs p = function
  | [] -> DpFlatCC (f, cs, dps, trs, get "dpProof" p)
  | Element ("freshSymbol", _, _, x :: _) :: xs' ->
      flatContextClosureProc_aux (Some (symbol x)) cs dps trs p xs'
  | Element ("flatContexts", _, _, xs) :: xs' ->
      flatContextClosureProc_aux f (List.map context xs) dps trs p xs'
  | Element ("dps", _, _, x :: _) :: xs' ->
      flatContextClosureProc_aux f cs (rules x) trs p xs'
  | Element ("trs", _, _, x :: _) :: xs' ->
      flatContextClosureProc_aux f cs dps (rules x) p xs'
  | Element ("dpProof", _, _, x :: _) :: xs' ->
      flatContextClosureProc_aux f cs dps trs (Some (dpProof_aux x)) xs'
  | x :: _ -> error_xml x "not a flatContextClosureProc"

and substitution x = get_sons "substitution" (List.map substEntry) x

and substEntry = function
  | Element ("substEntry", _, _, x1 :: x2 :: _) -> var x1, term x2
  | x -> error_xml x "not a substEntry"

and context = function
  | Element ("box", _, _, _) -> ContEmpty
  | Element ("funContext", _, _, x1 :: x2 :: x3 :: x4 :: _) ->
      ContApp (symbol x1, before x2, context x3, after x4)
  | x -> error_xml x "not a context"

and before x = get_sons "before" (List.map term) x

and after x = get_sons "after" (List.map term) x

and rewriteSequence = function
  | Element ("rewriteSequence", _, _, x :: xs) ->
      startTerm x, List.map rewriteStep xs
  | x -> error_xml x "not a rewriteSequence"

and startTerm x = get_first_son "startTerm" term x

and rewriteStep x =
	get_sons "rewriteStep" (rewriteStep_aux [] None false None) x

and rewriteStep_aux p r b t = function
  | [] -> p, get "rule" r, b, get "term" t
  | Element ("positionInTerm", _, _, xs) :: xs' ->
      rewriteStep_aux (List.map position xs) r b t xs'
  | Element ("rule", _, _, x1 :: x2 :: _) :: xs' ->
      rewriteStep_aux p (Some (lhs x1, rhs x2)) b t xs'
  | Element ("relative", _, _, _) :: xs' ->
      rewriteStep_aux p r true t xs'
  | x :: xs' -> rewriteStep_aux p r b (Some (term x)) xs'

and trsTerminationProof x =
	get_first_son "trsTerminationProof" trsTerminationProof_aux x

and trsTerminationProof_aux = function
  | Element ("rIsEmpty", _, _, _) -> TrsEmpty
  | Element ("ruleRemoval", _, _, xs) -> ruleRemoval xs
  | Element ("dpTrans", _, _, x1 :: x2 :: x3 :: _) ->
      TrsDpTrans (dps x1, markedSymbols x2, dpProof x3)
  | Element ("semlab", _, _, x1 :: x2 :: x3 :: _) ->
      TrsSemLab (model x1, trs x2, trsTerminationProof x3)
  | Element ("unlab", _, _, x1 :: x2 :: _) ->
      TrsUnlab (trs x1, trsTerminationProof x2)
  | Element ("stringReversal", _, _, x1 :: x2 :: _) ->
      TrsRev (trs x1, trsTerminationProof x2)
  | Element ("flatContextClosure", _, _, x1 :: x2 :: x3 :: _) ->
      TrsFlatCC (flatContexts x1, trs x2, trsTerminationProof x3)
  | Element ("terminationAssumption", _, _, x :: _) ->
      TrsHyp (trsInput x)
  | x -> error_xml x "not a trsTerminationProof"

and ruleRemoval xs = ruleRemoval_aux [] None [] None xs

and ruleRemoval_aux ocs ocp rs p = function
  | [] -> TrsRuleRemoval
      (ocs, get "orderingConstraintProof" ocp, rs, get "trsTerminationProof" p)
  | Element ("orderingConstraints", _, _, xs) :: xs' ->
      ruleRemoval_aux (List.map orderingConstraintElement xs) ocp rs p xs'
  | Element ("orderingConstraintProof", _, _, x :: _) :: xs' ->
      ruleRemoval_aux ocs (Some (orderingConstraintProof_aux x)) rs p xs'
  | Element ("trs", _, _, x :: _) :: xs' ->
      ruleRemoval_aux ocs ocp (rules x) p xs'
  | Element ("trsTerminationProof", _, _, x :: _) :: xs' ->
      ruleRemoval_aux ocs ocp rs (Some (trsTerminationProof_aux x)) xs'
  | x :: _ -> error_xml x "not a ruleRemoval"

and markedSymbols x = get_first_son "markedSymbols" bool x

and flatContexts x = get_sons "flatContexts" (List.map context) x

and _loop = function
  | Element ("loop", _, _, x1 :: x2 :: x3 :: _) ->
      rewriteSequence x1, substitution x2, context x3
  | x -> error_xml x "not a loop"

and trsNonterminationProof x =
	get_first_son "trsNonterminationProof" trsNonterminationProof_aux x

and trsNonterminationProof_aux = function
  | Element ("variableConditionViolated", _, _, _) -> TrsNTVarCond
  | Element ("ruleRemoval", _, _, x1 :: x2 :: _) ->
      TrsNTRuleRemoval (trs x1, trsNonterminationProof x2)
  | Element ("stringReversal", _, _, x1 :: x2 :: _) ->
      TrsNTRev (trs x1, trsNonterminationProof x2)
  | Element ("loop", _, _, x1 :: x2 :: x3 :: _) ->
      TrsNTLoop (rewriteSequence x1, substitution x2, context x3)
  | Element ("dpTrans", _, _, x1 :: x2 :: x3 :: _) ->
      TrsNTDp (dps x1, markedSymbols x2, dpNonterminationProof x3)
  | Element ("nonterminationAssumption", _, _, x :: _) ->
      TrsNTHyp (trsInput x)
  | x -> error_xml x "not a trsNonterminationProof"
 
and relativeTerminationProof x =
	get_first_son "relativeTerminationProof" relativeTerminationProof_aux x

and relativeTerminationProof_aux = function
  | Element ("rIsEmpty", _, _, _) -> RelEmptyR
  | Element ("sIsEmpty", _, _, _) -> RelEmptyS
  | Element ("ruleRemoval", _, _,
	    Element ("orderingConstraints", _, _, xs)
	     :: x1 :: x2 :: x3 :: x4 :: _) ->
      RelRuleRemoval (List.map orderingConstraintElement xs,
		      orderingConstraintProof x1,
		      trs x2, trs x3, relativeTerminationProof x4)
  | Element ("ruleRemoval", _, _, x1 :: x2 :: x3 :: x4 :: _) ->
      RelRuleRemoval ([], orderingConstraintProof x1,
		      trs x2, trs x3, relativeTerminationProof x4)
  | Element ("semlab", _, _, x1 :: x2 :: x3 :: x4 :: _) ->
      RelSemLab (model x1, trs x2, trs x3, relativeTerminationProof x4)
  | Element ("unlab", _, _, x1 :: x2 :: x3 :: _) ->
      RelUnlab (trs x1, trs x2, relativeTerminationProof x3)
  | Element ("stringReversal", _, _, x1 :: x2 :: x3 :: _) ->
      RelRev (trs x1, trs x2, relativeTerminationProof x3)
  | Element ("relativeTerminationAssumption", _, _, x :: _) ->
      RelHyp (trsInput x)
  | x -> error_xml x "not a relativeTerminationProof"

and dpNonterminationProof x =
	get_first_son "dpNonterminationProof" dpNonterminationProof_aux x

and dpNonterminationProof_aux = function
  | Element ("loop", _, _, x1 :: x2 :: x3 :: _) ->
      DpNTLoop (rewriteSequence x1, substitution x2, context x3)
  | Element ("dpRuleRemoval", _, _, x1 :: x2 :: x3 :: _) ->
      DpNTRuleRemoval (dps x1, trs x2, dpNonterminationProof x3)
  | Element ("infinitenessAssumption", _, _, x :: _) ->
      DpNTHyp (dpInput x)
  | x -> error_xml x "not a dpNonterminationProof"

and relativeNonterminationProof x =
	get_first_son "relativeNonterminationProof" relativeNonterminationProof_aux x

and relativeNonterminationProof_aux = function
  | Element ("loop", _, _, x1 :: x2 :: x3 :: _) ->
      RelNTLoop (rewriteSequence x1, substitution x2, context x3)
  | Element ("trsNonterminationProof", _, _, x :: _) ->
      RelNTTrs (trsNonterminationProof x)
  | Element ("variableConditionViolated", _, _, _) ->
      RelNTVarCond
  | Element ("ruleRemoval", _, _, x1 :: x2 :: x3 :: _) ->
      RelNTRuleRemoval (trs x1, trs x2, relativeNonterminationProof x3)
  | Element ("nonterminationAssumption", _, _, x :: _) ->
      RelNTHyp (trsInput x)
  | x -> error_xml x "not a relativeNonterminationProof"

and orderingConstraints x =
	get_sons "orderingConstraints" (List.map orderingConstraintElement) x

and orderingConstraintElement = function
  | Element ("orderingConstraintElement", _, _, x1 :: x2 :: xs) ->
      let mps, ips, rs = orderingConstraintElement_aux None None [] xs in
	strict x1, ceCompatible x2, mps, ips, rs
  | x -> error_xml x "not an orderingConstraintElement"

and orderingConstraintElement_aux mps ips rs = function
  | [] -> mps, ips, List.rev rs
  | Element ("monotonePositions", _, _, x :: _) :: xs' ->
      orderingConstraintElement_aux (Some (monotonePositions x)) ips rs xs'
  | Element ("ignoredPositions", _, _, x :: _) :: xs' ->
      orderingConstraintElement_aux mps (Some (argumentFilter x)) rs xs'
  | x :: xs' -> orderingConstraintElement_aux mps ips (rule x :: rs) xs'

and ceCompatible x = get_first_son "ceCompatible" bool x

and monotonePositions = function
  | Element ("everySymbolAndPosition", _, _, _) -> MonAll
  | x -> MonArgFil (argumentFilter x)

and orderingConstraintProof x =
	get_first_son "orderingConstraintProof" orderingConstraintProof_aux x

and orderingConstraintProof_aux = function
  | Element ("redPair", _, _, x :: _) -> OrdRedPair (redPair_aux x)
  | Element ("satisfiableAssumption", _, _, x :: _) ->
      OrdHyp (orderingConstraints x)
  | x -> error_xml x "not an orderingConstraintProof"

and proof x = get_first_son "proof" proof_aux x

and proof_aux = function
  | Element ("trsTerminationProof", _, _, x :: _) ->
      Prf (trsTerminationProof_aux x)
  | Element ("trsNonterminationProof", _, _, x :: _) ->
      PrfNT (trsNonterminationProof_aux x)
  | Element ("relativeTerminationProof", _, _, x :: _) ->
      PrfRel (relativeTerminationProof_aux x)
  | Element ("relativeNonterminationProof", _, _, x :: _) ->
      PrfRelNT (relativeNonterminationProof_aux x)
  | Element ("dpProof", _, _, x :: _) ->
      PrfDp (dpProof_aux x)
  | Element ("dpNonterminationProof", _, _, x :: _) ->
      PrfDpNT (dpNonterminationProof_aux x)
  | Element ("orderingConstraintProof", _, _, x :: _) ->
      PrfOrd (orderingConstraintProof_aux x)
  | x -> error_xml x "not a proof"

and url x = get_first_son "url" get_pc x

and trsInput x = get_sons "trsInput" trsInput_aux x

and trsInput_aux xs = trsInput_aux' [] StratFull [] [] xs

and trsInput_aux' rs s es rrs = function
  | [] -> rs, s, es, rrs
  | Element ("trs", _, _, x :: _) :: xs' ->
      trsInput_aux' (rules x) s es rrs xs'
  | Element ("strategy", _, _, x :: _) :: xs' ->
      trsInput_aux' rs (strategy x) es rrs xs'
  | Element ("equations", _, _, x :: _) :: xs' ->
      trsInput_aux' rs s (rules x) rrs xs'
  | Element ("relativeRules", _, _, x :: _) :: xs' ->
      trsInput_aux' rs s es (rules x) xs'
  | x :: _ -> error_xml x "not a trsInput"

and strategy = function
  | Element ("innermost", _, _, _) -> StratIn
  | x -> error_xml x "not a strategy"

and dpInput x = get_sons "dpInput" dpInput_aux x

and dpInput_aux xs = dpInput_aux' [] [] StratFull None xs

and dpInput_aux' rs dps s b = function
  | [] -> rs, dps, s, get "bool" b
  | Element ("trs", _, _, x :: _) :: xs' ->
      dpInput_aux' (rules x) dps s b xs'
  | Element ("dps", _, _, x :: _) :: xs' ->
      dpInput_aux' rs (rules x) s b xs'
  | Element ("strategy", _, _, x :: _) :: xs' ->
      dpInput_aux' rs dps (strategy x) b xs'
  | Element ("minimal", _, _, x :: _) :: xs' ->
      dpInput_aux' rs dps s (Some (bool x)) xs'
  | x :: _ -> error_xml x "not a dpInput"

and certificationProblem = function
  | Element ("certificationProblem", _, _, x1 :: x2 :: x3 :: xs) ->
      input x1, cpfVersion x2, proof x3, origin xs
  | x -> error_xml x "not a certificationProblem"

and input x = get_first_son "input" input_aux x

and input_aux = function
  | Element ("trsInput", _, _, xs) -> InTrs (trsInput_aux xs)
  | Element ("dpInput", _, _, xs) -> InDp (dpInput_aux xs)
  | Element ("orderingConstraints", _, _, xs) ->
      InOrd (List.map orderingConstraintElement xs)
  | x -> error_xml x "not an inputs"

and cpfVersion x = get_first_son "cpfVersion" get_pc x

and origin = function
  | [] -> None
  | Element ("origin", _, _, x1 :: x2 :: _) :: _ ->
      Some (proofOrigin x1, inputOrigin x2)
  | x :: _ -> error_xml x "not an origin"

and proofOrigin x = get_sons "proofOrigin" (proofOrigin_aux [] []) x

and proofOrigin_aux ts tus = function
  | [] -> ts, tus
  | Element ("tool", _, _, xs') :: xs ->
      proofOrigin_aux (tool xs' :: ts) tus xs
  | Element ("toolUser", _, _, x1 :: x2 :: []) :: xs ->
      proofOrigin_aux ts ((firstName x1, lastName x2, "") :: tus) xs
  | Element ("toolUser", _, _, x1 :: x2 :: x3 :: _) :: xs ->
      proofOrigin_aux ts ((firstName x1, lastName x2, url x3) :: tus) xs
  | x :: _ -> error_xml x "not a proofOrigin"

and tool xs = tool_aux "" "" "" "" xs

and tool_aux n v s u = function
  | [] -> n, v, s, u
  | Element ("name", _, _, x :: _) :: xs -> tool_aux (get_pc x) v s u xs
  | Element ("version", _, _, x :: _) :: xs -> tool_aux n (get_pc x) s u xs
  | Element ("strategy", _, _, x :: _) :: xs -> tool_aux n v (get_pc x) u xs
  | Element ("url", _, _, x :: _) :: xs -> tool_aux n v s (get_pc x) xs
  | x :: _ -> error_xml x "not a tool"

and firstName x = get_first_son "firstName" get_pc x

and lastName x = get_first_son "lastName" get_pc x

and inputOrigin x = get_sons "inputOrigin" (inputOrigin_aux false "") x

and inputOrigin_aux b s = function
  | [] -> b, s
  | Element ("tpdb-reference", _, _, _) :: xs -> inputOrigin_aux true s xs
  | Element ("source", _, _, x :: _) :: xs -> inputOrigin_aux b (get_pc x) xs
  | x :: _ -> error_xml x "not an inputOrigin";;
