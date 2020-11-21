  
(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-08-31

converting a cpf proof into a rainbow proof
******************************************************************************)

open Problem;;
open Proof;;
open Error;;
open Util;;
open Cpf0;;

(******************************************************************************
symbols, terms and rules
******************************************************************************)

(* b indicates if symbols are marked *)

let rec symbol b = function
  | Symbol_name n when b -> Int (Ident n)
  | Symbol_name n -> Ident n
  | Symbol_sharp (Symbol_name n) -> Hd (Ident n)
  | Symbol_sharp f -> Hd (symbol b f)
  | Symbol_labeledSymbol (f, l) -> Label (symbol b f, label b l)

and label b = function
  | Label_numberLabel [] -> []
  | Label_numberLabel _ -> not_supported "integer labels"
  | Label_symbolLabel fs -> List.map (symbol b) fs;;

let rec term b = function
  | Term_var n -> Var (Util.var n)
  | Term_funapp (f, ts) -> App (symbol b f, List.map (term b) ts);;

let trs_rule b (l, r) = Util.init_var_map ();
  canonical_rule { trs_lhs = term b l; trs_rhs = term b r; trs_conds = [] };;

let trs_rules b = List.map (trs_rule b);;

(******************************************************************************
counter-examples
******************************************************************************)

(* positions are counted from 1 in CPF and from 0 in Rainbow *)

(* int list -> int list *)
let position = List.map (fun p -> p-1);;

let rec loop steps mod_steps = function
  | [] | (((_, _), None), _) :: _ -> List.rev steps, mod_steps
  | (((ps, r), (Some true)), _) :: rs ->
      let s = { cet_mod_step_pos = position ps;
		cet_mod_step_rule = trs_rule false r }
      in loop steps (s :: mod_steps) rs
  | (((ps, r), (Some false)), _) :: rs ->
      let s = { cet_step_mod_steps = List.rev mod_steps;
		cet_step_pos = position ps;
		cet_step_rule = trs_rule false r }
      in loop (s :: steps) [] rs;;

(* Cpf0.context -> positive list *)

let rec position_of_context = function
  | Context_box -> []
  | Context_funContext (_, l, c, _) ->
      List.length l :: position_of_context c;;

let trs_counter_example = function
  | TrsNonterminationProof_variableConditionViolated ->
      CET_var_cond
  | TrsNonterminationProof_loop (((_, []), _), _) ->
      error_fmt "empty rewrite sequence"
  | TrsNonterminationProof_loop (((t, l), _), c) ->
      let steps, mod_steps = loop [] [] l in
	CET_loop { cet_start = term false t;
		   cet_steps = steps;
		   cet_mod = mod_steps;
		   cet_pos = position_of_context c }
  | _ -> not_supported "non termination techniques other than \
     variable condition and loops";;

let rel_counter_example = function
  | RelativeNonterminationProof_variableConditionViolated ->
      CET_var_cond
  | RelativeNonterminationProof_loop (((_, []), _), _) ->
      error_fmt "empty rewrite sequence"
  | RelativeNonterminationProof_loop (((t, l), _), c) ->
      let steps, mod_steps = loop [] [] l in
	CET_loop { cet_start = term false t;
		   cet_steps = steps;
		   cet_mod = mod_steps;
		   cet_pos = position_of_context c }
  | _ -> not_supported "non termination techniques other than \
     variable condition and loops";;

let dp_counter_example = function
  | DpNonterminationProof_loop (((_, []), _), _) ->
      error_fmt "empty rewrite sequence"
  | DpNonterminationProof_loop (((t, l), _), c) ->
      let steps, mod_steps = loop [] [] l in
	CET_loop { cet_start = term false t;
		   cet_steps = steps;
		   cet_mod = mod_steps;
		   cet_pos = position_of_context c }
  | _ -> not_supported "non termination techniques other than \
     variable condition and loops";;

(******************************************************************************
polynomials
******************************************************************************)

let poly_num = function
  | Number_integer i -> i
  | Number_rational (_, _) ->
      not_supported "numbers other than integers in polynomials";;

let poly_coef = function
  | Coefficient_number n -> poly_num n
  | Coefficient_minusInfinity
  | Coefficient_plusInfinity
  | Coefficient_vector _
  | Coefficient_matrix _ -> not_supported "polynomial coefficients other than numbers";;

let rec polynomial n = function
  | Polynomial_coefficient c -> poly_const n (poly_coef c)
  | Polynomial_variable i -> poly_xi n i
  | Polynomial_sum ps -> poly_sums (List.map (polynomial n) ps)
  | Polynomial_product ps -> poly_prods n (List.map (polynomial n) ps)
  | Polynomial_max _
  | Polynomial_min _ -> not_supported "min and max in polynomial interpretations";;

let poly_int b = function
  | ((f, arity), p) -> symbol b f, polynomial arity p

(******************************************************************************
matrices
******************************************************************************)

let int_of_num = function
  | Number_integer i -> i
  | Number_rational (_, _) -> error_fmt
      "matrix interpretation with non-integer coefficients";;

let int_of_coef = function
  | Coefficient_number n -> int_of_num n
  | Coefficient_minusInfinity
  | Coefficient_plusInfinity
  | Coefficient_vector _
  | Coefficient_matrix _ -> error_fmt
      "matrix interpretation with non-integer coefficients";;

let arctic_of_coef = function
  | Coefficient_number n -> Fin (int_of_num n)
  | Coefficient_minusInfinity -> MinusInf
  | Coefficient_plusInfinity
  | Coefficient_vector _
  | Coefficient_matrix _ -> error_fmt
      "arctic interpretation with non-arctic number coefficients";;

let vector = List.map;;

(* WARNING: in CPF, matrices are represented with column vectors
while in Rainbow, matrices are represented with row vectors *)

let comp f g x = f (g x);;

let transpose ci =
  let rec aux = function
    | [] | [] :: _ -> []
    | cs -> List.map (comp ci List.hd) cs :: aux (List.map List.tl cs)
  in aux;;

let matrix ci m =
  try transpose ci m
  with Failure _ -> error_fmt "ill-formed matrix";;

let arctic_add x y =
  match x, y with
    | Fin p, Fin q -> Fin (p+q)
    | _, _ -> MinusInf;;

let vec_add add v1 v2 =
  try List.map2 add v1 v2
  with Invalid_argument _ ->
    error_fmt "sum of two vectors of different size";;

let mat_add add m1 m2 =
  try List.map2 (vec_add add) m1 m2
  with Invalid_argument _ ->
    error_fmt "sum of two matrices of different size";;

let vec_0 z dim = clist z dim;;

let mat_0 z dim = clist (vec_0 z dim) dim;;

let mi_pol z add ci =
  let rec aux const args = function
    | [] -> { mi_const = const; mi_args = Array.to_list args }
    | Polynomial_sum qs :: ps -> aux const args (qs @ ps)
    | Polynomial_coefficient (Coefficient_matrix (Matrix_matrix [v])) :: ps
    | Polynomial_coefficient (Coefficient_vector (Vector_vector v)) :: ps -> 
      aux (vec_add add const (vector ci v)) args ps
    | Polynomial_product [p] :: ps -> aux const args (p :: ps)
    | Polynomial_product [Polynomial_coefficient (Coefficient_matrix (Matrix_matrix m)); 
                          Polynomial_variable i] :: ps ->
      args.(i-1) <- mat_add add args.(i-1) (matrix ci m);
      aux const args ps
    | _ -> not_supported "such matrix interpretations"
  in fun dim n -> function
    | Polynomial_sum ps -> aux (vec_0 z dim) (Array.make n (mat_0 z dim)) ps
    | _ -> not_supported
      "matrix interpretations not defined as a polynomial sum";;

let mi_fun z add ci b dim ((f, n), p) =
  symbol b f, mi_pol z add ci dim n p;;

(* Addition of type coq_Z *)

let mi_int = mi_fun 0 (+) int_of_coef;;

let mi_arctic = mi_fun (Fin 0) arctic_add arctic_of_coef;;

(******************************************************************************
 arguments filterings
******************************************************************************)

let rec nats_decr_lt n =
  if n <= 0 then [] else let p = n-1 in p :: nats_decr_lt p;;

let nats_incr_lt n = List.rev (nats_decr_lt n);;

let filter b = function
  | ((f, _), T11_collapsing k) ->
    symbol b f, Some (Proj (k-1))
  | ((f, n), T11_nonCollapsing ks) ->
    symbol b f,
      if ks = nats_incr_lt n then None else Some (Perm ks);;

let arg_filter b af = List.map (filter b) af;;

let is_filter : (Problem.symbol * Proof.filter option) list -> bool =
  List.exists (function _, None -> false
              | _, Some _ -> true);;

let proj b = function
  | ((f, _), T11_collapsing k) -> symbol b f, (k-1)
  | ((_f, _n), T11_nonCollapsing _ks) ->
      error_fmt "non-collapsing arguments filter";;

let simple_proj b af = List.map (proj b) af;;

(******************************************************************************
rpo
******************************************************************************)

let list_option f = function
  | None -> []
  | Some x -> f x;;

let status = function
  | T10_lex -> Lex
  | T10_mul -> Mul;;

let status_precedence b (((f, _), p), s) = symbol b f, (status s, p);;

let rpo b l af =
  let ro = Rpo (List.map (status_precedence b) l)
  and af = list_option (arg_filter b) af in
    if is_filter af then ArgFilterOrd (af, ro)
    else (warning "useless argument filter"; ro);;

(******************************************************************************
proofs
******************************************************************************)

let red_ord b = function
  | RedPair_interpretation (Type_t9_polynomial (Domain_naturals, _n), ls) ->
    (*ignored "polynomial maximal degrees";*)
      PolyInt (List.map (poly_int b) ls)
  | RedPair_interpretation (Type_t9_polynomial (_, _), _)                 ->
      not_supported "polynomial interpretations on domains different \
                     from naturals"
  | RedPair_interpretation (Type_t9_matrixInterpretation
                           (Domain_naturals, dim, 1), ls) ->
      MatrixInt { mi_dim = dim; mi_int = List.map (mi_int b dim) ls }
  | RedPair_interpretation (Type_t9_matrixInterpretation
                           (Domain_arctic Domain_naturals, dim, 1), ls) ->
      ArcticInt { mi_dim = dim; mi_int = List.map (mi_arctic b dim) ls }
  | RedPair_interpretation (Type_t9_matrixInterpretation
                           (Domain_arctic Domain_integers, dim, 1), ls) ->
      ArcticBZInt { mi_dim = dim; mi_int = List.map (mi_arctic b dim) ls }
  | RedPair_interpretation (Type_t9_matrixInterpretation (_, _, sdim), _)
                           when sdim > 1                                   ->
      not_supported "matrix interpretations with a strict dimension \
                     greater than 1"
  | RedPair_interpretation (Type_t9_matrixInterpretation (_,_,_), _)       ->
      not_supported "matrix interpretations on domains different from naturals \
                     and arctic numbers"
  | RedPair_pathOrder (l, af)                                              ->
      rpo b l af
  | _ -> not_supported "Todo"
  
let ord_cons b = function
  | OrderingConstraintProof_redPair rp              -> red_ord b rp
  | OrderingConstraintProof_satisfiableAssumption _ -> not_supported "satisfiableAssumption";;

let rec dp_proof b = function
  | DpProof_pIsEmpty                        -> Trivial
  | DpProof_depGraphProc cs                 -> Decomp    (Unif, List.rev_map (component b) cs)
  | DpProof_redPairUrProc (_, ocp, _, _, p) -> MannaNess (true, ord_cons b ocp, dp_proof b p)
  | DpProof_redPairProc (_, ocp, _, p)      -> MannaNess (false, ord_cons b ocp, dp_proof b p)
  | DpProof_monoRedPairUrProc (_, ocp, _, _, _, p) ->
      if get_hack() then
	(warning "monoRedPairUrProc is handled like redPairProc";
	 MannaNess (true, ord_cons b ocp, dp_proof b p))
      else not_supported "monoRedPairUrProc"
  | DpProof_monoRedPairProc (_, ocp, _, _, p) ->
      if get_hack() then
	(warning "monoRedPairProc is handled like redPairProc";
	 MannaNess (false, ord_cons b ocp, dp_proof b p))
      else not_supported "monoRedPairProc"
  | DpProof_subtermProc (af, [], _, p) -> SubtermCrit (simple_proj b af, dp_proof b p)
  | DpProof_subtermProc (_, _, _, _)   -> not_supported "projectedRewriteSequence"
  | DpProof_semlabProc (Model_rootLabeling _, _, _, _, p) -> RootLab (dp_proof b p)
  | DpProof_semlabProc (_, _, _, _, _) ->
      not_supported "semantic labellings other than root labelling"
  | DpProof_unlabProc (_, _, p)   -> Unlab (dp_proof b p)
  | DpProof_sizeChangeProc (_, _) -> not_supported "sizeChangeProc"
  | DpProof_flatContextClosureProc (_, _, _, _, p) -> FlatCC (dp_proof b p)
  | DpProof_argumentFilterProc (af, _, _, p)       -> ArgFilter (arg_filter b af, dp_proof b p)
  | DpProof_finitenessAssumption _ -> not_supported "finitenessAssumption"
  | _ -> not_supported "Todo"

(*WARNING: the list of DPs is reversed since in CPF, all forward arcs
are given while in Rainbow, there must be no forward arcs *)
and component b (((dps, _), _is), po) = 
  List.rev_map (trs_rule b) dps, opt_dp_proof b po

and opt_dp_proof b = function
  | None   -> None
  | Some p -> Some (dp_proof b p);;

let rec proof = function
  | TrsTerminationProof_rIsEmpty                    -> Trivial
  | TrsTerminationProof_ruleRemoval (_, ocp, _, p)  ->
      MannaNess (false, ord_cons false ocp, proof p)
  | TrsTerminationProof_dpTrans (_, false, dp)      -> DP (dp_proof false dp)
  | TrsTerminationProof_dpTrans (_, true, dp)       -> DP (MarkSymb (dp_proof true dp))
  | TrsTerminationProof_semlab (Model_rootLabeling _, _, _, p) -> RootLab (proof p)
  | TrsTerminationProof_semlab (_, _, _, _) ->
      not_supported "semantic labelling other than root labelling"
  | TrsTerminationProof_unlab (_, p)                 -> Unlab (proof p)
  | TrsTerminationProof_stringReversal (_, p)        -> TrsRev (proof p)
  | TrsTerminationProof_flatContextClosure (_, _, p) -> FlatCC (proof p)
  | TrsTerminationProof_terminationAssumption _      -> not_supported "terminationAssumption"
  | _ -> not_supported "Todo"

let rec rel_proof = function
  | RelativeTerminationProof_rIsEmpty
  | RelativeTerminationProof_sIsEmpty _ -> Trivial
  | RelativeTerminationProof_ruleRemoval (_, ocp, _, _, p) ->
      MannaNess (false, ord_cons false ocp, rel_proof p)
  | RelativeTerminationProof_semlab (Model_rootLabeling _, _, _, p) -> RootLab (rel_proof p)
  | RelativeTerminationProof_semlab (_, _, _, _) ->
      not_supported "semantic labelling other than root labelling"
  | RelativeTerminationProof_unlab (_, _, p) -> Unlab (rel_proof p)
  | RelativeTerminationProof_stringReversal (_, _, p) -> TrsRev (rel_proof p)
  | RelativeTerminationProof_relativeTerminationAssumption _ ->
      not_supported "relativeTerminationAssumption"
  | _ -> not_supported "Todo";;
  
let certificate_aux = function
  | Proof_trsTerminationProof p -> Proof (proof p)
  | Proof_relativeTerminationProof p -> Proof (rel_proof p)
  | Proof_dpProof p -> Proof (dp_proof true p)
  | Proof_trsNonterminationProof p -> Counter_example (CE_trs (trs_counter_example p))
  | Proof_relativeNonterminationProof p -> Counter_example (CE_trs (rel_counter_example p))
  | Proof_dpNonterminationProof p -> Counter_example (CE_trs (dp_counter_example p))
  | Proof_orderingConstraintProof _ -> not_supported "orderingConstraintProof"
  | _ -> not_supported "Todo";;
  
let certificate (((_, _), p), _) =
  ignored "sets of rules and dps (except for defining components)";
  certificate_aux p;;
