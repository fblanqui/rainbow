(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-10-20

convert a tpdb id into a valid coq id
******************************************************************************)

open Char;;
open String;;
open Util;;
open Problem;;
open Proof;;

(****************************************************************************)
(* generic renaming function *)
(****************************************************************************)

(*UNUSED: let id _rmap x = x;;*)

let rename_opt rename = function
  | None -> None
  | Some x -> Some (rename x);;

let rename_list rename rmap = List.map (rename rmap);;

let rename_mapping rename rmap (x,y) = (rename rmap x, y);;

let rename_mapping_list rename = rename_list (rename_mapping rename);;

(****************************************************************************)
(* test functions on char codes *)
(****************************************************************************)

let is_valid_coq_beginning_id_char_code i =
  is_alpha_char_code i || is_Alpha_char_code i || (* _ *) i = 95;;

let is_valid_coq_other_id_char_code i =
  is_digit_char_code i || (* ' *) i = 39;;

let is_valid_coq_id_char_code i =
  is_valid_coq_beginning_id_char_code i || is_valid_coq_other_id_char_code i;;

(* test functions on chars *)

(*UNUSED:
let is_valid_coq_beginning_id_char c =
  is_valid_coq_beginning_id_char_code (code c);;*)

let is_valid_coq_other_id_char c = is_valid_coq_other_id_char_code (code c);;

let is_valid_coq_id_char c = is_valid_coq_id_char_code (code c);;

(* generic functions on chars and strings *)

let underscored s = "_" ^ s ^ "_";;

(****************************************************************************)
(* function building a valid coq id from a non valid coq id char *)
(****************************************************************************)

let convert_char = function
  | '|' -> "bar"
  | '+' -> "plus"
  | '-' -> "minus"
  | '*' -> "times"
  | '/' -> "div"
  | '#' -> "sharp"
  | '%' -> "percent"
  | '$' -> "dollar"
  | '!' -> "exclamation_mark"
  | '&' -> "ampersand"
  | '<' -> "lt"
  | '>' -> "gt"
  | '=' -> "eq"
  | '.' -> "dot"
  | ',' -> "comma"
  | ':' -> "colon"
  | '?' -> "question_mark"
  | '@' -> "aroba"
  | ';' -> "semi_colon"
  | '^' -> "caret"
  | '\\' -> "back_slash"
  | '~' -> "tilde"
  | c -> string_of_int (code c);;

(* function building a valid coq id from a tpdb id (this function must
   be injective) *)

let coq_keywords = (*List.sort Pervasives.compare*)
  ["as"; "at"; "cofix"; "else"; "end"; "exists"; "exists2"; "fix"; "for";
   "forall"; "fun"; "if"; "IF"; "in"; "let"; "match"; "mod"; "Prop"; "return";
   "Set"; "then"; "Type"; "using"; (*CoLoR notation*)"U"; "where"; "with"];;

let coq_id_of_tpdb_id =
  let new_id = counter () in
  let rec aux s i sacc =
    if i < 0 then sacc
    else
      let c = s.[i] in
      let ns =
	if is_valid_coq_id_char c then String.make 1 c
	else underscored (convert_char c)
      in aux s (i-1) (ns ^ sacc)
  in fun s ->
    let ns = aux s (length s - 1) "" in
    let ns =
      if ns <> "" && is_valid_coq_other_id_char ns.[0]
      then "_" ^ ns
      else ns in
    let ns =
      if List.mem ns coq_keywords
      then "_" ^ ns
      else ns in
    (* keep at the end ! *)
    let ns =
      if ns <> s
      then ns ^ "_" ^ (string_of_int (new_id ()))
      else ns in
    ns;;

let renaming_of_problem pb =
  renaming_map coq_id_of_tpdb_id (idents_of_symbols (symbols_of_problem pb));;

(****************************************************************************)
(* problem renaming *)
(****************************************************************************)

let rename_name rmap s = try StrMap.find s rmap with Not_found -> s;;

let rename_symbol rmap =
  let rec aux = function
    | Ident s -> Ident (rename_name rmap s)
    | Hd f -> Hd (aux f)
    | Int f -> Int (aux f)
    | Label (f, ss) -> Label (aux f, List.map aux ss)
  in aux;;

let rename_symbol_mapping rmap = rename_mapping_list rename_symbol rmap;;

let rename_set rmap =
  let aux f s = SymbSet.add (rename_symbol rmap f) s in
    fun set -> SymbSet.fold aux set SymbSet.empty;;

let rename rmap =
  let aux f x m = SymbMap.add (rename_symbol rmap f) x m in
    fun smap -> SymbMap.fold aux smap SymbMap.empty;;

(*UNUSED:
let rename_and_map rmap fmap =
  let aux f x m = SymbMap.add (rename_symbol rmap f) (fmap x) m in
    fun smap -> SymbMap.fold aux smap SymbMap.empty;;*)

let rename_term rmap =
  let rec aux = function
    | App (f, ts) -> App (rename_symbol rmap f, List.map aux ts)
    | Var _ as x -> x
  in aux;;

let rename_word rmap = rename_list rename_symbol rmap;;

let rename_condition rmap c =
  { cond_lhs = rename_term rmap c.cond_lhs;
    cond_test = c.cond_test;
    cond_rhs = rename_term rmap c.cond_rhs };;

let rename_trs_rule rmap r =
  { trs_lhs = rename_term rmap r.trs_lhs;
    trs_rhs = rename_term rmap r.trs_rhs;
    trs_conds = rename_list rename_condition rmap r.trs_conds };;

let rename_trs_rules rmap = rename_list rename_trs_rule rmap;;

let rename_srs_rule rmap r =
  { srs_lhs = rename_word rmap r.srs_lhs;
    srs_rhs = rename_word rmap r.srs_rhs };;

let rename_axiom rmap = function
  | Builtin (s, x) -> Builtin (rename_symbol rmap s, x)
  | Equation (t1, t2) -> Equation (rename_term rmap t1, rename_term rmap t2);;

let rename_algebra rmap = function
  | Signature amap -> Signature (rename rmap amap)
  | Varyadic as x -> x;;

let rename_trs_strategy rmap = function
  | ContextSensitive repl_map -> ContextSensitive (rename rmap repl_map)
  | (Innermost | Outermost) as x -> x;;

let rename_trs rmap pb =
    { trs_symbols = rename_set rmap pb.trs_symbols;
      trs_algebra = rename_algebra rmap pb.trs_algebra;
      trs_axioms = rename_list rename_axiom rmap pb.trs_axioms;
      trs_strategy = rename_opt (rename_trs_strategy rmap) pb.trs_strategy;
      trs_rules = rename_list rename_trs_rule rmap pb.trs_rules;
      trs_le_rules = rename_list rename_trs_rule rmap pb.trs_le_rules };;

let rename_srs rmap pb =
    { srs_symbols = rename_set rmap pb.srs_symbols;
      srs_strategy = pb.srs_strategy;
      srs_rules = rename_list rename_srs_rule rmap pb.srs_rules;
      srs_le_rules = rename_list rename_srs_rule rmap pb.srs_le_rules };;

let rename_problem rmap = function
  | Trs p -> Trs (rename_trs rmap p)
  | Srs p -> Srs (rename_srs rmap p);;

(****************************************************************************)
(* proof renaming *)
(****************************************************************************)

let rename_matrix_based_int rmap mi = 
  { mi_dim = mi.mi_dim;
    mi_int = rename_symbol_mapping rmap mi.mi_int};;

let rec rename_red_ord rmap = function
  | PolyInt pi -> PolyInt (rename_symbol_mapping rmap pi)
  | MatrixInt mi -> MatrixInt (rename_matrix_based_int rmap mi)
  | ArcticInt mi -> ArcticInt (rename_matrix_based_int rmap mi)
  | ArcticBZInt mi -> ArcticBZInt (rename_matrix_based_int rmap mi)
  | TropicalInt mi -> TropicalInt (rename_matrix_based_int rmap mi)
  | ArgBoolOrd (af, ro) -> ArgBoolOrd
      (rename_symbol_mapping rmap af, rename_red_ord rmap ro)
  | ArgProjOrd (af, ro) -> ArgProjOrd
      (rename_symbol_mapping rmap af, rename_red_ord rmap ro)
  | ArgPermOrd (af, ro) -> ArgPermOrd
      (rename_symbol_mapping rmap af, rename_red_ord rmap ro)
  | ArgFilterOrd (af, ro) -> ArgFilterOrd
      (rename_symbol_mapping rmap af, rename_red_ord rmap ro)
  | Rpo l -> Rpo (rename_symbol_mapping rmap l);;

let rename_proof rmap =
  let rec aux = function
    | Trivial -> Trivial
    | MannaNess (b, ro, p) -> MannaNess (b, rename_red_ord rmap ro, aux p)
    | MarkSymb p -> MarkSymb (aux p)
    | DP p -> DP (aux p)
    | ArgBool (af, p) -> ArgBool (rename_symbol_mapping rmap af, aux p)
    | ArgProj (af, p) -> ArgProj (rename_symbol_mapping rmap af, aux p)
    | ArgPerm (af, p) -> ArgPerm (rename_symbol_mapping rmap af, aux p)
    | ArgFilter (af, p) -> ArgFilter (rename_symbol_mapping rmap af, aux p)
    | AsTrs p -> AsTrs (aux p)
    | AsSrs p -> AsSrs (aux p)
    | SrsRev p -> SrsRev (aux p)
    | TrsRev p -> TrsRev (aux p)
    | Decomp (og, l) ->	Decomp (og,
      List.map (fun (rs, p) -> rename_trs_rules rmap rs, rename_opt aux p) l)
    | FlatCC p -> FlatCC (aux p)
    | RootLab p -> RootLab (aux p)
    | Unlab p -> Unlab (aux p)
    | SubtermCrit (af, p) -> SubtermCrit (rename_symbol_mapping rmap af, aux p)
  in aux;;

let rename_cet_mod_step rmap cet = {
  cet_mod_step_pos = cet.cet_mod_step_pos;
  cet_mod_step_rule = rename_trs_rule rmap cet.cet_mod_step_rule };;

let rename_cet_step rmap cet = {
  cet_step_mod_steps =
    rename_list rename_cet_mod_step rmap cet.cet_step_mod_steps;
  cet_step_pos = cet.cet_step_pos;
  cet_step_rule = rename_trs_rule rmap cet.cet_step_rule };;

let rename_trs_loop rmap cet = {
  cet_start = rename_term rmap cet.cet_start;
  cet_steps = rename_list rename_cet_step rmap cet.cet_steps;
  cet_mod = rename_list rename_cet_mod_step rmap cet.cet_mod;
  cet_pos = cet.cet_pos };;

let rename_trs_counter_example rmap = function
  | CET_var_cond -> CET_var_cond
  | CET_loop l -> CET_loop (rename_trs_loop rmap l);;

let rename_ces_mod_step rmap ces = {
  ces_mod_step_pos = ces.ces_mod_step_pos;
  ces_mod_step_rule = rename_srs_rule rmap ces.ces_mod_step_rule };;

let rename_ces_step rmap ces = {
  ces_step_mod_steps =
    rename_list rename_ces_mod_step rmap ces.ces_step_mod_steps;
  ces_step_pos = ces.ces_step_pos;
  ces_step_rule = rename_srs_rule rmap ces.ces_step_rule };;

let rename_srs_loop rmap ces = {
  ces_start = rename_word rmap ces.ces_start;
  ces_steps = rename_list rename_ces_step rmap ces.ces_steps;
  ces_mod = rename_list rename_ces_mod_step rmap ces.ces_mod;
  ces_pos = ces.ces_pos };;

let rename_srs_counter_example rmap = function
  | CES_loop l -> CES_loop (rename_srs_loop rmap l);;

let rename_counter_example rmap = function
  | CE_trs ce -> CE_trs (rename_trs_counter_example rmap ce)
  | CE_srs ce -> CE_srs (rename_srs_counter_example rmap ce);;

let rename_certificate rmap = function
  | Proof p -> Proof (rename_proof rmap p)
  | Counter_example ce -> Counter_example (rename_counter_example rmap ce);;

