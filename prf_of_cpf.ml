(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-08-31

converting a cpf proof into a rainbow proof
******************************************************************************)

open Cpf;;
open Problem;;
open Proof;;
open Util;;
open Error;;

(******************************************************************************
symbols, terms and rules
******************************************************************************)

(* b indicates if symbols are marked *)

let rec symbol b = function
  | SymbName n when b -> Int (Ident n)
  | SymbName n -> Ident n
  | SymbSharp (SymbName n) -> Hd (Ident n)
  | SymbSharp f -> Hd (symbol b f)
  | SymbLab (f, l) -> Label (symbol b f, label b l)

and label b = function
  | LabNone
  | LabInt [] -> []
  | LabInt _ -> not_supported "integer labels"
  | LabSymb fs -> List.map (symbol b) fs;;

let rec term b = function
  | TermVar n -> Var (Util.var n)
  | TermApp (f, ts) -> App (symbol b f, List.map (term b) ts);;

let trs_rule b (l, r) = Util.init_var_map ();
  canonical_rule { trs_lhs = term b l; trs_rhs = term b r; trs_conds = [] };;

(*UNUSED:let trs_rules b = List.map (trs_rule b);;*)

(******************************************************************************
counter-examples
******************************************************************************)

(* positions are counted from 1 in CPF and from 0 in Rainbow *)
let position = List.map (fun p -> p-1);;

let rec loop steps mod_steps = function
  | [] -> List.rev steps, mod_steps
  | (ps, r, true, _) :: rs ->
      let s = { cet_mod_step_pos = position ps;
		cet_mod_step_rule = trs_rule false r }
      in loop steps (s :: mod_steps) rs
  | (ps, r, false, _) :: rs ->
      let s = { cet_step_mod_steps = List.rev mod_steps;
		cet_step_pos = position ps;
		cet_step_rule = trs_rule false r }
      in loop (s :: steps) [] rs;;

let rec position_of_context = function
  | ContEmpty -> []
  | ContApp (_, l, c, _) -> List.length l :: position_of_context c;;

let trs_counter_example = function
  | TrsNTVarCond -> CET_var_cond
  | TrsNTLoop ((_t, []), _s, _c) -> error_fmt "empty rewrite sequence"
  | TrsNTLoop ((t, l), _s, c) ->
      let steps, mod_steps = loop [] [] l in
	CET_loop { cet_start = term false t;
		   cet_steps = steps;
		   cet_mod = mod_steps;
		   cet_pos = position_of_context c }
  | _ -> not_supported "non termination techniques other than \
     variable condition and loops";;

let rel_counter_example = function
  | RelNTVarCond -> CET_var_cond
  | RelNTLoop ((_t, []), _s, _c) -> error_fmt "empty rewrite sequence"
  | RelNTLoop ((t, l), _s, c) ->
      let steps, mod_steps = loop [] [] l in
	CET_loop { cet_start = term false t;
		   cet_steps = steps;
		   cet_mod = mod_steps;
		   cet_pos = position_of_context c }
  | _ -> not_supported "non termination techniques other than \
     variable condition and loops";;

let dp_counter_example = function
  | DpNTLoop ((_t, []), _s, _c) -> error_fmt "empty rewrite sequence"
  | DpNTLoop ((t, l), _s, c) ->
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
  | NumInt i -> i
  | NumRat (_n, _d) ->
      not_supported "numbers other than integers in polynomials";;

let poly_coef = function
  | CoefNum n -> poly_num n
  | CoefMinusInf
  | CoefPlusInf
  | CoefVec _
  | CoefMat _ -> not_supported "polynomial coefficients other than numbers";;

let rec polynomial n = function
  | PolCoef c -> poly_const n (poly_coef c)
  | PolVar i -> poly_xi n i
  | PolSum ps -> poly_sums (List.map (polynomial n) ps)
  | PolProd ps -> poly_prods n (List.map (polynomial n) ps)
  | PolMax _
  | PolMin _ -> not_supported "min and max in polynomial interpretations";;

let poly_int b = function
  | f, arity, FunPol p -> symbol b f, polynomial arity p

(******************************************************************************
matrices
******************************************************************************)

let int_of_num = function
  | NumInt i -> i
  | NumRat (_n, _d) -> error_fmt
      "matrix interpretation with non-integer coefficients";;

let int_of_coef = function
  | CoefNum n -> int_of_num n
  | CoefMinusInf
  | CoefPlusInf
  | CoefVec _
  | CoefMat _ -> error_fmt
      "matrix interpretation with non-integer coefficients";;

let arctic_of_coef = function
  | CoefNum n -> Fin (int_of_num n)
  | CoefMinusInf -> MinusInf
  | CoefPlusInf
  | CoefVec _
  | CoefMat _ -> error_fmt
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
    | PolSum qs :: ps -> aux const args (qs @ ps)
    | PolCoef (CoefMat [v]) :: ps
    | PolCoef (CoefVec v) :: ps ->
	aux (vec_add add const (vector ci v)) args ps
    | PolProd [p] :: ps -> aux const args (p :: ps)
    | PolProd [PolCoef (CoefMat m); PolVar i] :: ps ->
	args.(i-1) <- mat_add add args.(i-1) (matrix ci m);
	aux const args ps
    | _ -> not_supported "such matrix interpretations"
  in fun dim n -> function
    | PolSum ps -> aux (vec_0 z dim) (Array.make n (mat_0 z dim)) ps
    | _ -> not_supported
	"matrix interpretations not defined as a polynomial sum";;

let mi_fun z add ci b dim (f, n, FunPol p) =
  symbol b f, mi_pol z add ci dim n p;;

let mi_int = mi_fun 0 (+) int_of_coef;;
let mi_arctic = mi_fun (Fin 0) arctic_add arctic_of_coef;;

(******************************************************************************
arguments filterings
******************************************************************************)

let filter b = function
  | f, _, ArgFilCollaps k -> symbol b f, Some (Proj (k-1))
  | f, n, ArgFilNonCollaps ks -> symbol b f, let ks = position ks in
      if ks = nats_incr_lt n then None else Some (Perm ks);;

let arg_filter b af = List.map (filter b) af;;

let is_filter = List.exists (function _, None -> false | _, Some _ -> true);;

let proj b = function
  | f, _, ArgFilCollaps k -> symbol b f, k-1
  | _f, _n, ArgFilNonCollaps _ks ->
      error_fmt "non-collapsing arguments filter";;

let simple_proj b af = List.map (proj b) af;;

(******************************************************************************
rpo
******************************************************************************)

let status = function
  | StatLex -> Lex
  | StatMul -> Mul;;

let status_precedence b (f, _, p, s) = symbol b f, (status s, p);;

let rpo b l af =
  let ro = Rpo (List.map (status_precedence b) l)
  and af = arg_filter b af in
    if is_filter af then ArgFilterOrd (af, ro)
    else (warning "useless argument filter"; ro);;

(******************************************************************************
proofs
******************************************************************************)

let red_ord b = function

(* polynomial interpretations *)
  | RedInt (TypPol (DomNat, _n), ls) ->
      (*ignored "polynomial maximal degrees";*)
      PolyInt (List.map (poly_int b) ls)
  | RedInt (TypPol (_, _), _) -> not_supported
      "polynomial interpretations on domains different from naturals"

(* matrix interpretations *)
  | RedInt (TypMat (DomNat, dim, 1), ls) ->
      MatrixInt { mi_dim = dim; mi_int = List.map (mi_int b dim) ls }
  | RedInt (TypMat (DomArctic DomNat, dim, 1), ls) ->
      ArcticInt { mi_dim = dim; mi_int = List.map (mi_arctic b dim) ls }
  | RedInt (TypMat (DomArctic DomInt, dim, 1), ls) ->
      ArcticBZInt { mi_dim = dim; mi_int = List.map (mi_arctic b dim) ls }
  | RedInt (TypMat (_, _, sdim), _) when sdim > 1 -> not_supported
      "matrix interpretations with a strict dimension greater than 1"
  | RedInt (TypMat (_,_,_), _) -> not_supported
      "matrix interpretations on domains different from naturals \
      and arctic numbers"

(* RPO *)
  | RedRPO (l, af) -> rpo b l af;;

let ord_cons b = function
  | OrdRedPair rp -> red_ord b rp
  | OrdHyp _ -> not_supported "satisfiableAssumption";;

let rec dp_proof b = function
  | DpEmpty -> Trivial
  | DpGraph cs -> Decomp (Unif, List.rev_map (component b) cs)
  | DpRedUR (_, ocp, _, _, p) -> MannaNess (true, ord_cons b ocp, dp_proof b p)
  | DpRed (_, ocp, _, p) -> MannaNess (false, ord_cons b ocp, dp_proof b p)
  | DpRedMonoUR (_, ocp, _, _, _, p) ->
      if get_hack() then
	(warning "monoRedPairUrProc is handled like redPairProc";
	 MannaNess (true, ord_cons b ocp, dp_proof b p))
      else not_supported "monoRedPairUrProc"
  | DpRedMono (_, ocp, _, _, p) ->
      if get_hack() then
	(warning "monoRedPairProc is handled like redPairProc";
	 MannaNess (false, ord_cons b ocp, dp_proof b p))
      else not_supported "monoRedPairProc"
  | DpSubterm (af, [], _, p) -> SubtermCrit (simple_proj b af, dp_proof b p)
  | DpSubterm (_, _, _, _) -> not_supported "projectedRewriteSequence"
  | DpSemLab (ModRootLab, _, _, p) -> RootLab (dp_proof b p)
  | DpSemLab (_, _, _, _) ->
      not_supported "semantic labellings other than root labelling"
  | DpUnlab (_, _, p) -> Unlab (dp_proof b p)
  | DpSC (_, _) -> not_supported "sizeChangeProc"
  | DpFlatCC (_, _, _, _, p) -> FlatCC (dp_proof b p)
  | DpArgFilter (af, _, _, p) -> ArgFilter (arg_filter b af, dp_proof b p)
  | DpHyp _ -> not_supported "finitenessAssumption"

(*WARNING: the list of DPs is reversed since in CPF, all forward arcs
are given while in Rainbow, there must be no forward arcs *)
and component b (dps, _, _is, po) =
  List.rev_map (trs_rule b) dps, opt_dp_proof b po

and opt_dp_proof b = function
  | None -> None
  | Some p -> Some (dp_proof b p);;

let rec proof = function
  | TrsEmpty -> Trivial
  | TrsRuleRemoval (_, ocp, _, p) ->
      MannaNess (false, ord_cons false ocp, proof p)
  | TrsDpTrans (_, false, dp) -> DP (dp_proof false dp)
  | TrsDpTrans (_, true, dp) -> DP (MarkSymb (dp_proof true dp))
  | TrsSemLab (ModRootLab, _, p) -> RootLab (proof p)
  | TrsSemLab (_, _, _p) ->
      not_supported "semantic labelling other than root labelling"
  | TrsUnlab (_, p) -> Unlab (proof p)
  | Cpf.TrsRev (_, p) -> Proof.TrsRev (proof p)
  | TrsFlatCC (_, _, p) -> FlatCC (proof p)
  | TrsHyp _ -> not_supported "terminationAssumption";;

let rec rel_proof = function
  | RelEmptyR
  | RelEmptyS -> Trivial
  | RelRuleRemoval (_, ocp, _, _, p) ->
      MannaNess (false, ord_cons false ocp, rel_proof p)
  | RelSemLab (ModRootLab, _, _, p) -> RootLab (rel_proof p)
  | RelSemLab (_, _, _, _) ->
      not_supported "semantic labelling other than root labelling"
  | RelUnlab (_, _, p) -> Unlab (rel_proof p)
  | RelRev (_, _, p) -> Proof.TrsRev (rel_proof p)
  | RelHyp _ -> not_supported "relativeTerminationAssumption";;

let certificate_aux = function
  | Prf p -> Proof (proof p)
  | PrfRel p -> Proof (rel_proof p)
  | PrfDp p -> Proof (dp_proof true p)
  | PrfNT p -> Counter_example (CE_trs (trs_counter_example p))
  | PrfRelNT p -> Counter_example (CE_trs (rel_counter_example p))
  | PrfDpNT p -> Counter_example (CE_trs (dp_counter_example p))
  | PrfOrd _ -> not_supported "orderingConstraintProof";;

let certificate (_, _, p, _) =
  ignored "sets of rules and dps (except for defining components)";
  certificate_aux p;;
