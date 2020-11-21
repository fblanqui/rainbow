(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2011-04-06

* Utility of CPF *)

Set Implicit Arguments.

Require Import ATrs SN ZArith EqUtil String List ListDec ListForall
  ListUtil ZUtil LogicUtil BoolUtil VecUtil ARelation NatUtil
  ADuplicateSymb AMorphism.

(****************************************************************************)
(** ** Generalization of the option type with additional error information. *)

(* Todo: means the termination techniques that are not supported yet. *)

Inductive todo : Type :=
| TnumberRational
| TcoefMinusInf
| TcoefPlusInf
| TcoefVector
| TcoefVector_arc
| TcoefVector_arcbz
| TcoefVector_trop
| TcoefMatrix
| TcoefMatrix_arc
| TcoefMatrix_arcbz
| TcoefMatrix_trop
| TcoefToDo
| TpolyMax
| TpolyMin
| TInput_orderingConstraints
| TinputStrategy
| TinputEquations
(* Use this todo for both termination proof and relative termination
proof. *)
(* In the case of there are some ordering constraints. *)
| TTrsTerminationProof_ruleRemoval
| TTrsTerminationProof_semlab 
| TTrsTerminationProof_unlab
| TTrsTerminationProof_stringReversal
| TTrsTerminationProof_flatContextClosure
| TTrsTerminationProof_terminationAssumption
| TTrsTerminationProof_uncurry
| TTrsTerminationProof_bounds
| TTrsTerminationProof_switchInnermost
| TTrsTerminationProof_split
| TTrsTerminationProof_removeNonApplicableRules
(* In the case of relative termination *)
| TRelativeTerminationProof_equalityRemoval
| TProof_dpNonterminationProof
| TProof_orderingConstraintProof
(* Todo case in non termination proof *)
| TTrsNonterminationProof_ruleRemoval
| TTrsNonterminationProof_stringReversal
| TTrsNonterminationProof_loop
| TTrsNonterminationProof_loop_nil
| TTrsNonterminationProof_dpTrans
| TTrsNonterminationProof_nonLoop
| TTrsNonterminationProof_nonterminationAssumption
| TTrsNonterminationProof_innermostLhssIncrease
(* Todo case in relative non termination proof. *)
| TRelativeNonterminationProof_trsNonterminationProof
| TRelativeNonterminationProof_ruleRemoval
| TRelativeNonterminationProof_nonterminationAssumption
(* Domain in polynomial interpretation *)
| Ttype_polynomialDomain_naturals
| Ttype_polynomialDomain_integers
| Ttype_polynomialDomain_rationals
| Ttype_polynomialDomain_arctic
| Ttype_polynomialDomain_tropical
| Ttype_polynomialDomain_matrices
| TOrderingConstraintProof_satisfiableAssumption
(* Dependency proof *)
(* In the case where given some ordering constraint. *)
| TDpProof_redPairProc
| TDpProof_redPairUrProc
| TDpProof_monoRedPairProc
| TDpProof_monoRedPairUrProc
| TDpProof_subtermProc
| TDpProof_semlabProc
| TDpProof_unlabProc
| TDpProof_sizeChangeProc
| TDpProof_flatContextClosureProc
| TDpProof_argumentFilterProc
(* When the proof is not finish. *)
| TDpProof_finitenessAssumption
| TDpProof_usableRulesProc
| TDpProof_innermostLhssRemovalProc
| TDpProof_switchInnermostProc
| TDpProof_rewritingProc
| TDpProof_instantiationProc
| TDpProof_forwardInstantiationProc
| TDpProof_narrowingProc
| TDpProof_splitProc
| TDpProof_generalRedPairProc
(* Todo for redPair*)
| TRedPair_knuthBendixOrder
| TRedPair_scnp
(* This value is the value of the base case of the extra argument in
   the case of structually recursive function wrt this argument. *)
| TDpProof_zerobound (* REMOVE *)
(* Matrix interpretation *)
(* Todo in the case of Poly matrix interpretation over natural
numbers. *)
| TPoly_MatrixNatInt
| TPoly_MatrixInt_ArcNat
| TPoly_MatrixInt_ArcBZ
| TPoly_MatrixInt_Trop
(* Other cases *)
(* Todo in the case of dpProof. *)
| TdpProof
(* Todo in the case of orderingConstraintProof_redPair_dp. *)
| TorderingConstraintProof_redPair_dp
(* Todo in the case of orderingConstraintProof_redPair. *)
| TorderingConstraintProof_redPair
(* Use in the case of relative termination *)
| TorderingConstraintProof_redPair_pathOrder
| TorderingConstraintProof_redPair_knuthBendixOrder
| TorderingConstraintProof_redPair_scnp
| Todo1.

(* error: means it is a real error in the certificate *)

Inductive error : Type :=
(* Error messages *)
(* When a function symbol is applied to at least two sequences of
 arguments of different length *)
| EtermUnfixedArity
(* When a polynomial variable is bigger than some given constant. *)
| EpolyVarTooBig
| EpolyVarTooBig_matrix
 (* When the input and the proof are incompatible. *)
| EinputProofIncompatible
(* Empty *)
(* Error in the case of TRS is an empty set. *)
| ErNotEmpty
(* In the case DP is an empty set. *)
| ErDPNotEmpty
| ENegativeCoefficient
(* Error when convert an integer to a natural numbers. *)
| ENotANat
| ENotArcNat
| ENotArcBZ
| ENotTrop
(* Error when convert a vector to a list of size [d]. *)
| EVector_of_list
(* Error when return an [i-th] in a list of [A] to a result type
[A]. *)
| EMatrix_nth
(* Variable conditions. *)
(* Return error in the case of variable of non termination prof is
 not satisfy the two conditions. This use both in termination proof
 and relative termination proof. *)
| ErNotVariableConditionViolated
 (* Error in the case of relative non termination loop. *)
| ErrelativeNonTerminationProof_loop
(* Empty and poly of relative termination. *)
| Tmod_data_nil (* TEST: remove later *)
(* Error in the case of relative termination when D is an empty
set. *)
| ErNotEmptyrIsEmpty
| ERuleNotInLargeOrdering_poly_rel
(* Polynomial interpretation is not monotone over naturals in
 relative termination. *)
| ENotMonotone_rel_poly_nat
(* Polynomial interpretation is not monotone over rationals in
 relative termination. *)
| ENotMonotone_rel_poly_rat
(* The reduction pairs is not satisfy in the case of matrix
 interpretation in relative termination. *)
| ERuleNotInLargeOrdering_matrix_rel.

(* failure: means some possible errors, for instance, not succeeded in
checking monotony in polynomial. *)

Inductive failure : Type :=
| FDpProof_zerobound
| FComponent
| FDecomp
| FNotDepPairs_graph
| FdepGraphProc
| FNotMonotone_matrix_arc_bz
| FRuleNotInLargeOrdering_matrix_arcbz_dp
(* Return error in the case of non termination proof in loop
 method. *)
| FtrsNonTerminationProof_loop
(* In the case argument filtering is a nil list. *)
| FargumentFilter_nil
(* Argument filtering is not a collapsing or non-collapsing. *)
| FargumentFilter_false
(* Error when it is not a path ordering term *)
| FNotpathOrder_term
(* Error when it is not a path ordering in the case not apply argument
filtering. *)
| FNotpathOrder_rpo (* rpo alone *)
| FNotpathOrder_with_af (* with af *)
(* At top termination. *)
| FNotpathOrder_rpo_dp
| FNotpathOrder_with_af_dp
(* Error when argument filter with dpProof. *)
| Fdp_argumentfilter_nil
(* Precedence [i^th] have incompatible statuses. *)
| FPrecedence_incompatible_statuses
| FPrecedence_incompatible_statuses_dp
| FPrecedence_incompatible_statuses_proj (* Projection/collapsing *)
| FPrecedence_incompatible_statuses_filter (* Filter/non-collapsing *)
(* At top termination. *)
| FPrecedence_incompatible_statuses_dp_filter
| FPrecedence_incompatible_statuses_dp_proj
(* Monotone *)
(* When polynomial interpretation is not monotone over domain natural
 numbers. *)
| FNotMonotone
(* When polynomial interpretation is not monotone over domain
 rational numbers. *)
| FNotMonotone_rat
(* When polynomial interpretation in the case of DP is not monotone
over domain natural numbers. *)
| FNotMonotone_dp
 (* When polynomial interpretation in the case of DP is not monotone
 over domain rational numbers. *)
| FNotMonotone_rat_dp
| FNotMonotone_matrix_naturals
| FNotMonotone_matrix_naturals_dp
| FNotMonotone_matrix_arc_naturals
| FNotMonotone_matrix_tropical
(* Dependency transformation. *)
(* Return an error message in the case of dependency transformation of
unmarked symbols. *)
| FDPTransUnmark 
 (* Return an error message in the case of dependency transformation
 of marked symbols. *)
| FDPTransMark
(* Return an error message in the case of dependency
transformation. *)
(* Order in polynomial reduction pairs. *)
| FDPTrans
| FRuleNotInLargeOrdering_poly
(* Domain naturals *)
| FRuleNotInLargeOrdering_poly_nat
(* Domain rationals *)
| FRuleNotInLargeOrdering_poly_rat
(* Order in matrix reduction pairs. *)
| FRuleNotInLargeOrdering_matrix_naturals
| FRuleNotInLargeOrdering_matrix_arc_naturals
| FRuleNotInLargeOrdering_matrix_arc_bz
| FRuleNotInLargeOrdering_matrix_tropical
(* At top relation. *)
| FRuleNotInLargeOrdering_matrix_nat_dp
| FRuleNotInLargeOrdering_matrix_arcnat_dp
(*| ERuleNotInLargeOrdering_matrix_arcbz_dp*)
| FRuleNotInLargeOrdering_dp
(* Dependency proof [dpProof] *)
(* The decomposition graph is not valid. *)
| FDecompNotValid
(* The decomposition contains a rule that is not a DP. *)
| FNotSCC
(* The decomposition does not contain all DPs. *)
| FNotDepPairs
(* RPO and AF *)
| Frpo_af
| Frpo_af_nil
| Frpo_af_dp
| Frpo_af_dp_nil
(* trs termaination zero bound *)
| FtrsTerminationProof_zerobound
(* fail at string reverse *)
| Fstring_reverse.

(* Message has three kinds: todo, error or failure *)

Inductive message: Type :=
| Todo  : todo -> message
| Error : error -> message
| Fail  : failure -> message.

(* Result: Ok mean the function of type A is indeed correct. Ko
message: returns a suitable message *)

Inductive result (A : Type) : Type :=
| Ok : A -> result A
| Ko : message -> result A.

(* FIXME : Remove inductive unit by using unit type in Datatype, it is
for extraction reason *)

Inductive unit : Set := Zero.

Definition OK := Ok Zero.

(* Translation function from [result->bool] *)

Definition bool_of_result A (a : result A) :=
  match a with
    | Ok _ => true
    | Ko _ => false
  end.

(** Monads for error type. *)

Notation "'Match' e1 'With' x ===> e2" := 
  (match e1 with
    | Ok x => e2
    | Ko e => Ko _ e
   end) (right associativity, at level 60).

(** Translation function from [option -> result (list)] *)

Definition list_of_option A B (f : A -> result (list B)) x :=
  match x with
    | Some y => f y
    | None   => Ok nil
  end.

(** Map function is a function that applies a given function [f] to
   each element of a list; return a list of results. *)

(* TODO: give an example of map_rev result *)

Section map.

  Variables (A B C D: Type) (f : A -> result B).

  (* Mapping function [list -> result list], this is like the one in
  COQ. *)

  Fixpoint map (l:list A) : result (list B) :=
    match l with
      | nil    => Ok nil
      | x :: t =>
        Match f x   With y  ===>
        Match map t With t' ===> Ok (y :: t')
    end.

  (* [map_rev] if the application of [f] returns Ok on every element of [l],
     then returns Ok with the list of results obtained in reverse order,
     and Ko otherwise. *)

  Fixpoint map_rev_aux (acc: list B) (l: list A) : result (list B) :=
    match l with
      | nil     => Ok acc
      | x :: t =>
        Match f x With y ===> map_rev_aux (y :: acc) t
    end.

  Definition map_rev : list A -> result (list B) := map_rev_aux nil.

  (** Split function used in the [dpProof] definition.
     Return a list of first element of a tuple type.

     For example:
     [split_list ((1, 0, 3, 4) :: (2, 0, 0, 0) :: nil)]

     Return a list: [1 :: 2 :: nil]. *)

  Definition split_aux (x : A * B * C * D) :=
     let '(a, b, c, d) := x in a.

  Definition split_list l := List.map split_aux l.

  (** Split function used in the [Argumentfiltering] definition.
     Return a list of first element of a tuple type.

     For example:
     [split_list ((1, 0, 3) :: (2, 0, 0) :: nil)]

     Return a list: [1 :: 2 :: nil]. *)
  
  Definition split_triple (a: A * B * C) := 
    let '(a, b, c) := a in a.

  Definition list_split_triple (l: list (A * B * C)) :=
    List.map split_triple l.

  (** Return an i-th in a list of A to a result type A. *)

  (*Fixpoint Matrix_nth (l : list A) (i: nat) : result A :=
    match l, i with
      | (x :: l'), 0      => Ok x
      | (x :: l'), (S n') => Matrix_nth l' n'
      | _, _              => Ko _ (Error EMatrix_nth)
    end. *)

  (** Define a vector of list that taking a list and a natural number
     (d: nat), return a result type of vector of size [d], when the
     length of a list is equal to [d], return Ok vector of size [d],
     otherwise return an error.

     For example: [d = 2], [l = 1 :: 0 :: nil],
     [vector_of_list l d] will return an Ok of vector [(1, 0)]. *)

  Fixpoint vector_of_list (l : list A) (d : nat) :
    result (VecUtil.vector A d) :=
    match eq_nat_dec (length l) d with
      | left e    => Ok (Vcast (VecUtil.vec_of_list l) e) (* n = m *)
      | _         => Ko _ (Error EVector_of_list) (* n <> m *)
    end.

End map.

(** [int_to_nat] function is a function convert an integer number [z] to
   a result natural numbers (If [0 <= z] true then convert [z] from
   integer to natural number by function [Z.to_nat]). The function
   [Z.to_nat] will check if [z] is equal to [0] then return [0], if [z] is a
   positive then convert it by function [Pos.to_nat], and if [z] is a
   negative number it will return [0] (in this case we already catch at
   the condition [is_not_neg]). If a given integer has negative numbers
   return an error, otherwise return an Ok of type natural numbers. *)

(* FIXME *)

Require Import ZUtil.

Definition int_to_nat (z: Z) : result nat :=
  if    is_not_neg z
  then
    let i := Z.to_nat z in
        Ok i
  else  Ko _ (Error ENotANat).

(** [list_int_to_list_nat] convert a list of integer to a list of
   natural numbers of result type. *)

Definition list_int_to_list_nat (l : list Z) : result (list nat) :=
  map int_to_nat l.

(***********************************************************************)
(** ** Boolean equivality of two sets. *)

(* to move to CoLoR later *)

Section equiv.
  
  Require Import ListDec.
  
  Variable A      : Type.
  Variable beq    : A -> A -> bool.
  Variable beq_ok : forall x y, beq x y = true <-> x = y.

  Definition equiv l m := incl beq l m && incl beq m l.
  
  Lemma equiv_ok : forall l m, equiv l m = true <-> l [=] m.
    
  Proof.
    intuition. unfold lequiv. unfold equiv in H.
    rewrite andb_eq in H. do 2 rewrite incl_ok in H; hyp.
    unfold equiv. rewrite andb_eq. unfold lequiv in H.
    split. destruct H.
    rewrite incl_ok; hyp. destruct H.
    rewrite incl_ok; hyp.
  Qed.
  
End equiv.

(* positive : nat *)
Require Import Ascii String.

Definition pos_of_ascii (a: ascii) : positive :=
  N.succ_pos (N_of_ascii a).

(* string -> nonNegativeInteger *)

Definition string_of_N (s: string) : N :=
  match s with
    | EmptyString   => N0
    | String a _ => N_of_ascii a
  end.

(* string -> positive *)
Definition string_of_positive (s: string) : positive :=
  match s with
    | EmptyString => Pos.of_nat 0 (* remark it is empty string return 1 *)
    | String a _ => pos_of_ascii a
  end.

(* string -> Z *)

Definition string_of_Z (s: string) : Z :=
  match s with
    | EmptyString => Z0
    | String _ s  =>
      let  p := string_of_positive s in
      Zpos p
  end.
      (*if   ge p (xO%positive p) (* REMARK:
                      if p >= 0 then zpos else p < 0 mean 0 is neg *)
      then Zpos p
      else Zneg p
  end.*)