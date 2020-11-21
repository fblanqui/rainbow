(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2010-12-21

Define CPF type in Coq
******************************************************************************)

Set Implicit Arguments.

Require Import ZArith String.

Section definition.

(***********************************************************************)
(** string *)

Definition integer : Type := Z.
Definition nonNegativeInteger : Type := integer.
Definition positiveInteger : Type := integer.
Definition boolean : Type := bool.

(*Definition string := list Sig.*)

Inductive name := string

with label :=
  | Lab_numberLabel : list nonNegativeInteger -> label
  | Lab_symbolLabel : list symbol -> label

with symbol := 
  | Symbol_name : name -> symbol
  | Symbol_sharp : symbol -> symbol
  | Symbol_labeledSymbol : symbol -> label -> symbol
(*  | arity : symbol -> nat -> symbol*)

with var := T1 : string -> var (**)

with term :=
  | Term_var : var -> term
  | Term_funapp : symbol -> list term -> term

with cpf_rule := T2 : term -> term -> cpf_rule (**)

with rules := T3 : list cpf_rule -> rules (**)

with dps := T4 : rules -> dps (**)

with trs := T5 : rules -> trs (**)

with usableRules := T6 : rules -> usableRules (**)

with number := 
  | Number_integer : integer -> number
  | Number_rational : integer -> positiveInteger -> number

with coefficient := 
  | Coefficient_number : number -> coefficient
  | Coefficient_minusInfinity
  | Coefficient_plusInfinity
  | Coefficient_vector : vector -> coefficient
  | Coefficient_matrix : matrix -> coefficient

with vector := T7 : list coefficient -> vector (**)

with matrix := T8 : list vector -> matrix (**)

with polynomial :=
  | Polynomial_coefficient : coefficient -> polynomial
  | Polynomial_variable : positiveInteger -> polynomial
  | Polynomial_sum : list polynomial -> polynomial
  | Polynomial_product : list polynomial -> polynomial
  | Polynomial_max : list polynomial -> polynomial
  | Polynomial_min : list polynomial -> polynomial

with cpf_function := 
  | Function_polynomial : polynomial -> cpf_function

with arity := T9 : nonNegativeInteger -> arity (**)

with dimension := T10 : positiveInteger -> dimension (**)

with strictDimension := T11 : positiveInteger -> strictDimension (**)

with degree := T12 : nonNegativeInteger -> degree (**)

with position := T13 : positiveInteger -> position (**)

with argumentFilter := T14 : list symbol -> list arity -> list t3 -> argumentFilter (**)

with t3 :=
  | T3_collapsing : positiveInteger -> t3
  | T3_nonCollapsing : list position -> t3

with domain := 
  | Domain_naturals 
  | Domain_integers
  | Domain_rationals : number -> domain
  | Domain_arctic : domain -> domain
  | Domain_tropical : domain -> domain
  | Domain_matrices : dimension -> strictDimension -> domain -> domain

with redPair :=
  | redpair_interpretation : cpf_type -> list symbol -> list arity -> list cpf_function -> redPair
  | redpair_pathOrder : list symbol -> list arity -> list nonNegativeInteger -> list t2 -> option argumentFilter -> redPair

with cpf_type :=
  | Cpf_type_polynomial : domain -> degree -> cpf_type
  | Cpf_type_matrixInterpretation : domain -> dimension -> strictDimension -> cpf_type

with t2 :=
  | T2_lex
  | T2_mul

with arithFunction :=
  | Arithfunction_natural : nonNegativeInteger -> arithFunction
  | Arithfunction_variable : positiveInteger -> arithFunction
  | Arithfunction_sum : list arithFunction -> arithFunction
  | Arithfunction_product : list arithFunction -> arithFunction
  | Arithfunction_min : list arithFunction -> arithFunction
  | Arithfunction_max : list arithFunction -> arithFunction

with model :=
  | Model_finiteModel : positiveInteger -> option tupleOrder -> list symbol -> list arity -> list arithFunction -> model
  | Model_rootLabeling

with tupleOrder :=
  | TupleOrder_pointWise

with dpProof := 
  | DpProof_pIsEmpty
  | DpProof_depGraphProc : list dps -> list boolean -> option (list positiveInteger) -> option (list dpProof) -> dpProof
  | DpProof_redPairProc : option orderingConstraints -> orderingConstraintProof -> dps -> dpProof -> dpProof
  | DpProof_redPairUrProc : option orderingConstraints -> orderingConstraintProof -> dps -> usableRules -> dpProof -> dpProof
  | DpProof_monoRedPairProc : option orderingConstraints -> orderingConstraintProof -> dps -> trs -> dpProof
  | DpProof_monoRedPairUrProc : option orderingConstraints -> orderingConstraintProof -> dps -> trs -> usableRules -> dpProof -> dpProof
  | DpProof_subtermProc : argumentFilter -> list cpf_rule -> list rewriteSequence -> dps -> dpProof -> dpProof
  | DpProof_semlabProc : model -> dps -> trs -> dpProof -> dpProof
  | DpProof_unlabProc : dps -> trs -> dpProof -> dpProof
  | DpProof_sizeChangeProc : t1 -> list cpf_rule -> list (list nonNegativeInteger -> list boolean -> list nonNegativeInteger) -> dpProof 
  | DpProof_flatContextClosureProc : option symbol -> list context -> dps -> trs -> dpProof -> dpProof
  | DpProof_argumentFilterProc : argumentFilter -> dps -> trs -> dpProof -> dpProof
  | DpProof_finitenessAssumption : dpInput -> dpProof

with t1 := 
  | T1_subtermCriterion
  | T1_reductionPair : option orderingConstraints -> orderingConstraintProof -> option usableRules -> t1

with substitution := T15 : list var -> list term -> substitution (**)

with context := 
  | Context_box
  | Context_funContext : symbol -> list term -> context -> (list term) -> context

with rewriteSequence := T16 : (term) -> list (list position) -> list (list cpf_rule) -> list (list term) -> rewriteSequence (**)

with trsTerminationProof := 
  | TrsTerminationProof_rIsEmpty
  | TrsTerminationProof_ruleRemoval : option orderingConstraints -> orderingConstraintProof -> trs -> trsTerminationProof -> trsTerminationProof
  | TrsTerminationProof_dpTrans : dps -> boolean -> dpProof -> trsTerminationProof
  | TrsTerminationProof_semlab : model -> trs -> trsTerminationProof -> trsTerminationProof
  | TrsTerminationProof_unlab : trs -> trsTerminationProof -> trsTerminationProof
  | TrsTerminationProof_stringReversal : trs -> trsTerminationProof -> trsTerminationProof
  | TrsTerminationProof_flatContextClosure : (list context) -> trs -> trsTerminationProof -> trsTerminationProof
  | TrsTerminationProof_terminationAssumption : trsInput -> trsTerminationProof

with loop := T17: rewriteSequence -> substitution -> context -> loop  (**)

with trsNonterminationProof := 
  | TrsNonterminationProof_variableConditionViolated
  | TrsNonterminationProof_ruleRemoval : trs -> trsNonterminationProof -> trsNonterminationProof
  | TrsNonterminationProof_stringReversal : trs -> trsNonterminationProof -> trsNonterminationProof
  | TrsNonterminationProof_loop : loop -> trsNonterminationProof
  | TrsNonterminationProof_dpTrans : dps -> boolean -> dpNonterminationProof -> trsNonterminationProof
  | TrsNonterminationProof_nonterminationAssumption : trsInput -> trsNonterminationProof

with relativeTerminationProof := 
| RelativeTerminationProof_rIsEmpty
| RelativeTerminationProof_sIsEmpty : trsTerminationProof -> relativeTerminationProof
| RelativeTerminationProof_ruleRemoval : option orderingConstraints -> orderingConstraintProof -> trs -> trs -> relativeTerminationProof -> relativeTerminationProof
| RelativeTerminationProof_semlab : model -> trs -> trs -> relativeTerminationProof -> relativeTerminationProof
| RelativeTerminationProof_unlab : trs -> trs -> relativeTerminationProof -> relativeTerminationProof
| RelativeTerminationProof_stringReversal : trs -> trs -> relativeTerminationProof -> relativeTerminationProof
| RelativeTerminationProof_relativeTerminationAssumption : trsInput -> relativeTerminationProof

with dpNonterminationProof := 
| DpNonterminationProof_loop : loop -> dpNonterminationProof
| DpNonterminationProof_dpRuleRemoval : dps -> trs -> dpNonterminationProof -> dpNonterminationProof
| DpNonterminationProof_infinitenessAssumption : dpInput -> dpNonterminationProof

with relativeNonterminationProof := 
| RelativeNonterminationProof_loop : loop -> relativeNonterminationProof
| RelativeNonterminationProof_trsNonterminationProof : trsNonterminationProof -> relativeNonterminationProof
| RelativeNonterminationProof_variableConditionViolated
| RelativeNonterminationProof_ruleRemoval : trs -> trs -> relativeNonterminationProof -> relativeNonterminationProof
| RelativeNonterminationProof_nonterminationAssumption : trsInput -> relativeNonterminationProof

with orderingConstraints := T18 : list boolean -> list boolean -> list (option monotonePositions) -> list (option argumentFilter) -> list cpf_rule -> orderingConstraints (**)

with monotonePositions := 
| MonotonePositions_argumentFilter : argumentFilter -> monotonePositions
| MonotonePositions_everySymbolAndPosition

with orderingConstraintProof := 
| OrderingConstraintProof_redPair : redPair -> orderingConstraintProof
| OrderingConstraintProof_satisfiableAssumption : orderingConstraints -> orderingConstraintProof

with proof := 
| Proof_trsTerminationProof : trsTerminationProof -> proof
| Proof_trsNonterminationProof :  trsNonterminationProof -> proof
| Proof_relativeTerminationProof : relativeTerminationProof -> proof
| Proof_relativeNonterminationProof :  relativeNonterminationProof -> proof
| Proof_dpProof : dpProof -> proof
| Proof_dpNonterminationProof :  dpNonterminationProof -> proof
| Proof_orderingConstraintProof :  orderingConstraintProof -> proof

with url :=  T19 : string -> url (**)

with trsInput := T20 : trs -> option strategy -> option (rules) -> option (rules) -> trsInput (**)

with dpInput := T21 : trs -> dps -> option strategy ->  boolean -> dpInput (**)

with strategy := 
| Strategy_innermost

with certificationProblem := T22 : input -> string -> proof -> option (list string) -> option (list (option string)) -> option (list (option string)) -> option (list (option string)) -> option (list string) -> option (list string) -> option (list (option url)) -> option (option string) -> certificationProblem (**)

with input := 
| Input_trsInput : trsInput -> input
| Input_dpInput :  dpInput -> input
| Input_orderingConstraints : orderingConstraints -> input.

(***********************************************************************)
(** Cpf *)
(*
Inductive Record Cpf : Type := mkCpf {
  check : Cpf -> option bool;
  label : Label;
  symbol : Symbol;
  term : Term;
  rule : Rule;
  rules : list Rule;
  asignature : Cpf -> option Sig;
  aterm: forall f: Sig, Term -> option Sig
}.

(***********************************************************************)
(** list of symbols occurring in a term *)

Fixpoint symbs_list (t: Term) : list Symbol :=
  match t with
    | Var x => nil
    | Fun f l =>
      let fix symb_list_list n (l : list Term) {struct l} : list Symbol :=
        match l with
          | nil => nil
          | t :: lt => symbs_list t ++ symb_list_list n lt
        end 
      in (f :: symb_list_list (arity f) l)
  end.

Function symb_list_list (l : list Term) {struct l} : list Symbol :=
  match l with
    | nil => nil
    | t :: lt => symbs_list t ++ symb_list_list lt
  end.
*)
End definition.
