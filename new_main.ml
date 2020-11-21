(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2010-06-15

procedures for managing command line options
and converting a file from one format to another
******************************************************************************)

open Arg;;
open Printf;;
open Libxml;;
open Util;;

(*****************************************************************************)
(* input file types *)
(*****************************************************************************)

type problem = Trs | Srs | Pb | Xtc;;
type proof = Cpf | Prf;;

type input = Problem of problem | Proof of proof;;

(* in get_inputs(), the problem always come first *)
let add_input, get_inputs =
  let i = ref [] in
    (fun t s ->
       match t, !i with
	 | _, _::_::_
	 | Proof _, [Proof _,_]
	 | Problem _, [Problem _,_]
	 | Problem _, _ -> i := (t,s) :: !i
	 | _ -> i := !i @ [t,s]),
    (fun () -> if !i = [] then error "no input file provided" else !i);;

let add_problem p = add_input (Problem p);;
let add_proof p = add_input (Proof p);;
 
(*****************************************************************************)
(* output file types *)
(*****************************************************************************)

type output = OutCoq | OutPrf | OutPb | OutXtc | OutBool;;

let set_output, get_output =
  let o = ref None in
    (fun t () ->
       if !o = None then o := Some t else error "output type already set"),
    (fun () -> !o);;

(*****************************************************************************)
(* command line options parsing *)
(*****************************************************************************)

let set_usage_msg, get_usage_msg =
  let m = ref "" in
    (fun s -> m := s),
    (fun () -> !m);;

let rec options() =
  List.sort (fun (x,_,_) (y,_,_) -> Pervasives.compare x y) (Arg.align
[
  "-h", Unit print_help,
  " Display this list of options";
  "-itrs", String (add_problem Trs),
  " Take a .trs file as input";
  "-isrs", String (add_problem Srs),
  " Take a .srs file as input";
  "-ipb", String (add_problem Pb),
  " Take a .pb file as input";
  "-ixtc", String (add_problem Xtc),
  " Take a .xtc file as input";
  "-iprf", String (add_proof Prf),
  " Take a .prf file as input";
  "-icpf", String (add_proof Cpf),
  " Take a .cpf file as input";
  "-opb", Unit (set_output OutPb),
  " Generate a .pb file on stdout";
  "-oprf", Unit (set_output OutPrf),
  " Generate a .prf file on stdout";
  "-ocoq", Unit (set_output OutCoq),
  " Generate a .v file on stdout";
  "-oxtc", Unit (set_output OutXtc),
  " Generate a .xtc file on stdout";
  "-obool", Unit (set_output OutBool),
  " Generate an boolean ";
  "-hack", Unit set_hack,
  " Ignore usable rules and monotony requirements and enforce some conditions";
])

and print_options oc =
  List.iter (fun (k, _, d) -> fprintf oc "%s: %s\n" k d) (options())

and print_help() =
  print_endline (get_usage_msg()); print_options stdout; exit 0;;

let options = options();;

let anon_fun _ = error "invalid option";;

let parse_args() = Arg.parse options anon_fun (get_usage_msg());;

(*****************************************************************************)
(* input file parsing functions *)
(*****************************************************************************)

let pb_of_problem = function
  | Trs -> fun ic -> Pb_of_tpdb.pb_of_trs (Pb_of_tpdb.parse_trs ic)
  | Srs -> fun ic -> Pb_of_tpdb.pb_of_srs (Pb_of_tpdb.parse_srs ic)
  | Xtc -> fun ic -> Pb_of_xtc.problem (Xtc_of_xml.problem (parse_xml ic))
  | Pb -> fun ic -> Pb_of_xml.problem (parse_xml ic);;

let parse_cpf ic = Newcpf.certificationProblem (parse_xml ic);;

let parse_cpf_height ic =
  let x = parse_xml ic in Newcpf.certificationProblem x, height x;;

let prf_of_proof = function
  | Prf -> fun ic -> Prf_of_xml.certificate (parse_xml ic)
  | Cpf -> fun ic -> Prf_of_newcpf.certificate (parse_cpf ic);;

let pb_of_problem_file t s = parse_file (pb_of_problem t) s;;
let prf_of_proof_file t s = parse_file (prf_of_proof t) s;;

let pb_of_cpf_file s = Pb_of_newcpf.problem (Util.parse_file parse_cpf s);;

(*****************************************************************************)
(* generate coq from pb *)
(*****************************************************************************)

let coq_of_pb pb =
  let rmap = Rename.renaming_of_problem pb in
  let pb = Rename.rename_problem rmap pb
  and b = Buffer.create 10000 and br = Buffer.create 1000 in
    Coq_of_pb.genr_problem b pb;
    Require.require_import_modules br;
    Buffer.output_buffer stdout br;
    Buffer.output_buffer stdout b;;

(*****************************************************************************)
(* generate coq from prf *)
(*****************************************************************************)

let coq_of_prf pb prf =
  let rmap = Rename.renaming_of_problem pb in
  let pb = Rename.rename_problem rmap pb
  and prf = Rename.rename_certificate rmap prf
  and b = Buffer.create 50000 and br = Buffer.create 1000
			      and bp = Buffer.create 10000 in
    Coq_of_pb.genr_problem b pb;
    Coq_of_prf.genr_certif pb b bp prf;
    Require.require_import_modules br;
    Buffer.output_buffer stdout br;
    Buffer.output_buffer stdout b;
    Buffer.output_buffer stdout bp;;

(*****************************************************************************)
(* conversion procedure *)
(*****************************************************************************)
open Error_monad;;
open Cpf2color;;
open Rainbow_main;;

(* Output the 'string' for to do case *)

let string_of_todo = function
  | TnumberRational -> "TnumberRational"
  | TcoefMinusInf -> "TcoefMinusInf"
  | TcoefPlusInf -> "TcoefPlusInf"
  | TcoefVector -> "TcoefVector"
  | TcoefToDo -> "TcoefTodo "
  | TcoefVector_arc -> "TcoefVector_arc"
  | TcoefVector_arcbz -> "TcoefVector_arcbz"
  | TcoefVector_trop -> "TcoefVector_trop"
  | TcoefMatrix -> "TcoefMatrix"
  | TcoefMatrix_arc -> "TcoefMatrix_arc"
  | TcoefMatrix_arcbz -> "TcoefMatrix_arcbz"
  | TcoefMatrix_trop -> "TcoefMatrix_trop"
  | TpolyMax -> "TpolyMax"
  | TpolyMin -> "TpolyMin"
  | TInput_orderingConstraints ->
    "TInput_orderingConstraints"
  | TinputStrategy -> "TinputStrategy"
  | TinputEquations -> "TinputEquations"
  (* Todo in both termination and relative termination. *)
  | TTrsTerminationProof_ruleRemoval ->
    "TTrsTerminationProof_ruleRemoval"
  | TTrsTerminationProof_semlab ->
    "TTrsTerminationProof_semlab"
  | TTrsTerminationProof_unlab ->
    "TTrsTerminationProof_unlab"
  | TTrsTerminationProof_stringReversal ->
    "TTrsTerminationProof_stringReversal"
  | TTrsTerminationProof_flatContextClosure ->
    "TTrsTerminationProof_flatContextClosure"
  | TTrsTerminationProof_terminationAssumption ->
    "TTrsTerminationProof_terminationAssumption"
  | TTrsTerminationProof_uncurry ->
    "TTrsTerminationProof_uncurry"
  | TTrsTerminationProof_bounds ->
    "TTrsTerminationProof_bounds"
  | TTrsTerminationProof_switchInnermost ->
    "TTrsTerminationProof_switchInnermost"
  | TTrsTerminationProof_split ->
    "TTrsTerminationProof_split"
  | TTrsTerminationProof_removeNonApplicableRules ->
    "TTrsTerminationProof_removeNonApplicableRules"
  | TRelativeTerminationProof_equalityRemoval ->
    "TRelativeTerminationProof_equalityRemoval"
  | TProof_dpNonterminationProof ->
    "TProof_dpNonterminationProof"
  | TProof_orderingConstraintProof ->
    "TProof_orderingConstraintProof"
  (* Todo in the case of non termination proof *)
  | TTrsNonterminationProof_ruleRemoval ->
    "TrsNonterminationProof_ruleRemoval"
  | TTrsNonterminationProof_stringReversal ->
    "TrsNonterminationProof_stringReversal"
  | TTrsNonterminationProof_loop ->
    "TrsNonterminationProof_loop"
  | TTrsNonterminationProof_loop_nil ->
    "TrsNonterminationProof_loop_nil"
  | TTrsNonterminationProof_dpTrans ->
    "TrsNonterminationProof_dpTrans"
  | TTrsNonterminationProof_nonLoop ->
    "TrsNonterminationProof_nonLoop"
  | TTrsNonterminationProof_nonterminationAssumption ->
    "TrsNonterminationProof_nonterminationAssumption"
  | TTrsNonterminationProof_innermostLhssIncrease ->
    "TrsNonterminationProof_innermostLhssIncrease"
  (* Todo in the case of relative non termination proof. *)
  | TRelativeNonterminationProof_trsNonterminationProof ->
    "TRelativeNonterminationProof_trsNonterminationProof"
  | TRelativeNonterminationProof_ruleRemoval ->
    "TRelativeNonterminationProof_ruleRemoval"
  | TRelativeNonterminationProof_nonterminationAssumption ->
    "TRelativeNonterminationProof_nonterminationAssumption"
  (* Todo case of domain in polynomial intepretation. *)
  | Ttype_polynomialDomain_naturals ->
    "Ttype_polynomialDomain_naturals"
  | Ttype_polynomialDomain_integers ->
    "Ttype_polynomialDomain_integers"
  | Ttype_polynomialDomain_rationals ->
    "Ttype_polynomialDomain_rationals"
  | Ttype_polynomialDomain_arctic ->
    "Ttype_polynomialDomain_arctic"
  | Ttype_polynomialDomain_tropical ->
    "Ttype_polynomialDomain_tropical"
  | Ttype_polynomialDomain_matrices ->
    "Ttype_poly_polynomialDomain_matrices"
  | TOrderingConstraintProof_satisfiableAssumption ->
    "TOrderingConstraintProof_satisfiableAssumption"
  (* Todo case of dependency proof *)
  | TDpProof_zerobound -> "TDpProof_zerobound"
  | TDpProof_redPairProc ->
    "TDpProof_redPairProc" 
  | TDpProof_redPairUrProc ->
    "TDpProof_redPairUrProc" 
  | TDpProof_monoRedPairProc ->
    "TDpProof_monoRedPairProc"
  | TDpProof_monoRedPairUrProc ->
    "TDpProof_monoRedPairUrProc"
  | TDpProof_subtermProc -> "TDpProof_subtermProc"
  | TDpProof_semlabProc -> "TDpProof_semlabProc"
  | TDpProof_unlabProc -> "TDpProof_unlabProc"
  | TDpProof_sizeChangeProc -> "TDpProof_sizeChangeProc "
  | TDpProof_flatContextClosureProc ->
    "TDpProof_flatContextClosureProc"
  | TDpProof_argumentFilterProc ->
    "TDpProof_argumentFilterProc"
  | TDpProof_finitenessAssumption ->
    "TDpProof_finitenessAssumption"
  | TDpProof_usableRulesProc ->
    "TDpProof_usableRulesProc"
  | TDpProof_innermostLhssRemovalProc ->
    "TDpProof_innermostLhssRemovalProc"
  | TDpProof_switchInnermostProc ->
    "TDpProof_switchInnermostProc"
  | TDpProof_rewritingProc ->
    "TDpProof_rewritingProc"
  | TDpProof_instantiationProc ->
    "TDpProof_instantiationProc"
  | TDpProof_forwardInstantiationProc ->
    "TDpProof_forwardInstantiationProc"
  | TDpProof_narrowingProc ->
    "TDpProof_narrowingProc"
  | TDpProof_splitProc ->
    "TDpProof_splitProc"
  | TDpProof_generalRedPairProc ->
    "TDpProof_generalRedPairProc"
  | TRedPair_knuthBendixOrder   ->
    "TRedPair_knuthBendixOrder "
  | TRedPair_scnp ->
    "TRedPair_scnp"
  (* To do case of atrix interpretation *)
  | TPoly_MatrixNatInt -> "TPoly_MatrixNatInt "
  | TPoly_MatrixInt_ArcNat -> "TPoly_MatrixInt_ArcNat"
  | TPoly_MatrixInt_ArcBZ -> "TPoly_MatrixInt_ArcBZ"
  | TPoly_MatrixInt_Trop -> "TPoly_MatrixInt_Trop" 
  (* Others to do case *)
  | TdpProof -> "TdpProof "
  | TorderingConstraintProof_redPair_dp ->
    "TorderingConstraintProof_redPair_dp"
  | TorderingConstraintProof_redPair ->
    "TorderingConstraintProof_redPair"
  | TorderingConstraintProof_redPair_pathOrder ->
    "TorderingConstraintProof_redPair_pathOrder"
  | TorderingConstraintProof_redPair_knuthBendixOrder ->
    "TorderingConstraintProof_redPair_knuthBendixOrder"
  | TorderingConstraintProof_redPair_scnp ->
    "TorderingConstraintProof_redPair_scnp"
  | Todo1 -> "Todo";;

(* Output the eror message explain why it is an error. *)

let string_of_error = function
  | ErDPNotEmpty ->
    "dependency rules are not empty [dpProof_pIsEmpty]"
  | EtermUnfixedArity -> "term unfixed arity [EtermUnifixedArity]"
  | EpolyVarTooBig -> "variable in polynomial is too big [EpolyVarTooBig]"
  | EpolyVarTooBig_matrix ->
    "variable in polynomial of matrix is too big [EpolyVarTooBig_matrix]"
  | EinputProofIncompatible ->
    "input of proof is incompatible [EinputProofIncompatible]. "
  (* TRS is Empty*)
  | ErNotEmpty -> "rules are not empty [ErNotEmpty]. "
  (* Negative coefficient *)
  | ENegativeCoefficient ->
    "cofficient is negative number [ENegativeCoefficient]"
  (* Domain *)
  | ENotANat ->
    "it is not a N number [ENotANat]. "
  | ENotArcNat ->
    "it is not an artic N number [ENotArcNat]"
  | ENotArcBZ ->
    "it is not an artic Z number [ENotArcBZ]"
  | ENotTrop -> "it is not a tropical number \
          [ENotTrop]"
  | EVector_of_list ->
    "occur when convert list to vector \
          [EVector_of_list]"
  | EMatrix_nth ->
    "return an i-th in a list of A to a \
          result type A [EMatrix_nth]. "
  (* Non-Termination Problem. *)
  (* Variable conditions. *)
  | ErNotVariableConditionViolated ->
    "variable is not statisfy condition violated \
          [ErNotVariableConditionViolated]"
  | ErrelativeNonTerminationProof_loop ->
    "ErrelativeNonTerminationProof_loop"
  | Tmod_data_nil -> (* TEST remove later *)
    "Tmod_data_nil"
  (* Relative termination problem *)
  (* TRS is an empty list *)
  | ErNotEmptyrIsEmpty ->
    "rules are not empty in relative termination \
          [ErNotEmptyrIsEmpty]"
  (* Polynomial interpretation: monotone *)
  | ENotMonotone_rel_poly_nat ->
    "PolyInt on N at top \
          relation is not monotone [ENotMonotone_rel_poly_nat]"
  | ENotMonotone_rel_poly_rat ->
    "PolyInt on Q at top \
          relation is not monotone [ENotMonotone_rel_poly_rat]"
  (* Matrix interpretation over domain N. *)
  | ERuleNotInLargeOrdering_matrix_rel ->
    "Rules are not in large ordering in \
          MatrixInt of \
          relative termination [ERuleNotInLargeOrdering_matrix_rel]"
  | ERuleNotInLargeOrdering_poly_rel ->
    "Rules are not in large ordering in \
          PolyInt \
          [ERuleNotInLargeOrdering_poly_rel]";;

(* Output the string for [failure] *)
let string_of_failure = function
  | FDpProof_zerobound ->
    "Failure at zero bound [FDpProof_zerobound]"
  | FComponent ->
    "Failure at a component [FComponent]"
  | FDecomp ->
    "Failure at checking a valid decomposition graph [FDecomp]"
  | FNotDepPairs_graph ->
    "Failure at checking rules is not equivalence [FNotDepPairs_graph]" 
  | FdepGraphProc ->
    "Failure at DG [FdepGraphProc]." 
  | FNotMonotone_matrix_arc_bz ->
    "MatrixInt on arctic Z is not \
          monotone [FNotMonotone_matrix_arc_bz]. "
  (* Matrix interpretation over domain Arctic integer. *)
  | FRuleNotInLargeOrdering_matrix_arcbz_dp ->
    "Rules are not in large ordering in \
          MatrixInt \
          on artic Z at top relation \
          [FRuleNotInLargeOrdering_matrix_arc_bz]"
  (* Loop *)
  | FtrsNonTerminationProof_loop ->
    "ErtrsNonTerminationProof_loop"
  (* Argument filtering *)
  | FargumentFilter_nil ->
    "AF list is nil [EargumentFilter_nil]"
  | FargumentFilter_false ->
    "Non collapsing is false [EargumentFilter_false]"
  (* Recursive path ordering and argument filtering *)
  | FNotpathOrder_with_af ->
   "rules are not in large ordering in case of RPO + AF [ENotpathOrder_with_af]"
  | FNotpathOrder_with_af_dp ->
    "rules are not in large ordering in case of RPO + AF at top \
          relation [ENotpathOrder_with_af_dp]"
  (* Recursive path ordering *)
  | FNotpathOrder_term ->
    "Fail to convert term in case of RPO without AF [ENotpathOrder_term]"
  | FNotpathOrder_rpo ->
    "rules are not in large ordering in case of RPO without AF \
          [ENotpathOrder_rpo]"
  | FNotpathOrder_rpo_dp ->
    "rules are not in large ordering in case of RPO without AF \
          at top relation [ENotpathOrder_rpo_dp]"
  (* Argument filtering *)
  | Fdp_argumentfilter_nil ->
    "AF list is nil at top relation [Edp_argumentfilter_nil]"
  | FPrecedence_incompatible_statuses ->
    "Fail to convert term in case of RPO with AF \
          (collapsing and non collapsing) [EPrecedence_incompatible_statuses]"
  | FPrecedence_incompatible_statuses_proj ->
    "Fail to convert term in case of RPO with AF projection \
          (collapsing) [EPrecedence_incompatible_statuses_proj]"
  | FPrecedence_incompatible_statuses_filter ->
    "Fail to convert term in case of RPO with AF filtering \
          (non collapsing) [EPrecedence_incompatible_statuses_filtering]"
  | FPrecedence_incompatible_statuses_dp ->
    "Fail to convert term in case of RPO with AF \
          (collapsing and non collapsing) at top relation \
          [EPrecedence_incompatible_statuses_dp]"
  | FPrecedence_incompatible_statuses_dp_proj ->
    "Fail to convert term in case of RPO with AF projection \
          (collapsing) at top relation \
          [EPrecedence_incompatible_statuses_dp_proj]"
  | FPrecedence_incompatible_statuses_dp_filter ->
    "Fail to convert term in case of RPO with AF filtering \
          (non collapsing) at top relation \
          [EPrecedence_incompatible_statuses_dp_filter]"
  (* Polynomial interpretation: Monotone *)
  | FNotMonotone ->
    "PolyInt on N is not monotone [ENotMonotone]"
  | FNotMonotone_rat ->
    "PolyInt on Q is not monotone [ENotMonotone_rat]"
  | FNotMonotone_dp ->
    "PolyInt on N at top \
          relation is not monotone [ENotMonotone_dp]"
  | FNotMonotone_rat_dp ->
    "PolyInt on Q at top \
          relation is not monotone [ENotMonotone_rat_dp]"
  (* Matrix interpretation: monotone *)
  | FNotMonotone_matrix_naturals ->
    "MatrixInt on N is not \
          monotone [ENotMonotone_matrix_naturals]"
  | FNotMonotone_matrix_naturals_dp ->
    "MatrixInt on N at top\
          relation is not monotone [ENotMonotone_matrix_naturals_dp]. "
  | FNotMonotone_matrix_arc_naturals ->
    "MatrixInt on arctic N is not \
          monotone [ENotMonotone_matrix_arc_naturals]. "
  | FNotMonotone_matrix_tropical ->
    "MatrixInt on tropicals is not \
          monotone [ENotMonotone_matrix_tropical]"
  (* Reduction pairs built from polynomial interpretation. *)
  | FRuleNotInLargeOrdering_poly ->
    "Rules are not in large ordering in \
          PolyInt \
          [ERuleNotInLargeOrdering_poly]"
  | FRuleNotInLargeOrdering_poly_nat ->
    "Rules are not in large ordering in \
           PolyInt on N \
          [ERuleNotInLargeOrdering_poly_nat]"
  | FRuleNotInLargeOrdering_poly_rat ->
    "Rules are not in large ordering in \
          PolyInt on Q \
          [ERuleNotInLargeOrdering_poly_rat]"
  (* Reduction pairs built from matrix interpretation *)
  | FRuleNotInLargeOrdering_matrix_naturals ->
    "Rules are not in large ordering in \
          MatrixInt \
          on N [ERuleNotInLargeOrdering_matrix_naturals]"
  | FRuleNotInLargeOrdering_matrix_arc_naturals ->
    "Rules are not in large ordering in \
          MatrixInt \
          on arctic N [ERuleNotInLargeOrdering_matrix_arc_naturals]"
  | FRuleNotInLargeOrdering_matrix_arc_bz ->
    "Rules are not in large ordering in \
          MatrixInt \
          on artic Z [ERuleNotInLargeOrdering_matrix_arc_bz]"
  | FRuleNotInLargeOrdering_matrix_tropical ->
    "Rules are not in large ordering in \
          MatrixInt \
          on tropicals [ERuleNotInLargeOrdering_matrix_tropical]"
  (* Dependency proof [dpProof] *)
  (* DP is empty *)
  (* Dependency transformation *)
  | FDPTransUnmark ->
    "Rules are not equivalent in case of DP \
          transformation without mark symbols [EDPTransUnmark]. "
  | FDPTransMark ->
    "Rules are not equivalent in case of DP \
          transformation with mark symbols [EDPTransMark]"
  | FDPTrans ->
    "Fail when transform DP [EDPTrans]"
  (* Polynomial interpretation over domain N. *)
  | FRuleNotInLargeOrdering_dp ->
    "Rules are not in large ordering in \
          PolyInt \
          at top relation [FRuleNotInLargeOrdering_dp]"
  (* Matrix interpretation over domain N. *)
  | FRuleNotInLargeOrdering_matrix_nat_dp ->
    "Rules are not in large ordering in \
          MatrixInt \
          on N at top relation [FRuleNotInLargeOrdering_matrix_nat_dp]"
  (* Matrix interpretation over domain Arctic nat. *)
  | FRuleNotInLargeOrdering_matrix_arcnat_dp ->
    "Rules are not in large ordering in \
          MatrixInt \
          on arctic N at top relation \
          [FRuleNotInLargeOrdering_matrix_arc_naturals_dp]"
  (* Dependency graph *)
  | FDecompNotValid ->
    "The decomposition graph is not valid \
          [FDecompNotValid]"
  | FNotSCC ->
    "It is not a strongly conneted component \
          [FNotSCC]"
  | FNotDepPairs ->
    "It is not a DP [FNotDepPairs]"
  (* RPO and AF *)
  | Frpo_af ->
    "It is not a RPO-AF [Frpo_af]"
  | Frpo_af_nil ->
    "It is not empty [Frpo_af_nil]"
  | Frpo_af_dp ->
    "It is not a RPO-AF [Frpo_af_dp]"
  | Frpo_af_dp_nil ->
    "It is not a empty [Frpo_af_dp_nil]"
  (* trs termaination zero bound *)
  | FtrsTerminationProof_zerobound ->
    "It is in the case of zero [FtrsTerminationProof_zerobound]"
  (* fail at string reverse *)
  | Fstring_reverse ->
    "It is not a string reverse [Fstring_reverse]";;

let print_result_aux r m = print_endline r; prerr_endline m;;

(* Answer:
    - CERTIFIED : the certifiate is correct. 
   - UNSUPPORTED: it is the MAYBE case, when the termination
   techniques used in the certificate is not presented in the
   verifier.
   - REJECTED: It is NO, the certificate is indeed not correct. *)

let print_result x =
  match x with
    | Ok _ -> print_result_aux "CERTIFIED" ""
    | Ko e ->
      (match e with
	| Todo x -> print_result_aux "UNSUPPORTED" (string_of_todo x)
	| Error x -> print_result_aux "REJECTED" (string_of_error x)
	| Fail x -> print_result_aux "UNSUPPORTED" (string_of_failure x));;

let convert o is = 
  match o, is with
    | (OutPb|OutPrf), _::_::_ -> error "too many input files"
    | OutBool, [Proof Cpf, s] ->
      let cpf, cpf_height = parse_file parse_cpf_height s in
      let arity = arity_in_pb cpf in
      let result = check 10 var cpf_height 100 arity cpf in
      print_result result
      (* Arguments of check:
	 1) maximum number of arguments compared lexicographically in RPO:
	   we currently used value should be replaced by the biggest arity
	   but this requires arity_in_pb to return a finite map
	   instead of a function
	 2) injective function from string to int
	 3) termination argument for certificate verification
	 4) termination argument for unification *)
    | OutPb, [Problem t, s] ->
      output_xml stdout (Xml_of_pb.problem (pb_of_problem_file t s))
    | OutPb, [Proof Cpf, s] ->
      output_xml stdout (Xml_of_pb.problem (pb_of_cpf_file s))
    | OutXtc, [Problem t, s] ->
      output_xml stdout (Xml_of_xtc.problem
			   (Xtc_of_pb.problem (pb_of_problem_file t s)))
    | OutXtc, [Proof Cpf, s] ->
      output_xml stdout (Xml_of_xtc.problem
			   (Xtc_of_pb.problem (pb_of_cpf_file s)))
    | OutPrf, [Proof t, s] ->
      output_xml stdout (Xml_of_prf.certificate (prf_of_proof_file t s))
    | OutCoq, [Problem t, s] -> coq_of_pb (pb_of_problem_file t s)
    | OutCoq, [Problem tpb, spb; Proof tprf, sprf] ->
      coq_of_prf (pb_of_problem_file tpb spb) (prf_of_proof_file tprf sprf)
    | OutCoq, [Proof Cpf, s] ->
      let cpf = parse_file parse_cpf s in
      coq_of_prf (Pb_of_newcpf.problem cpf)
	(Prf_of_newcpf.certificate cpf)
    | _, _ -> error "invalid combination of options";;
