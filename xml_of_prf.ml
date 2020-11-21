(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

from the internal representation of proofs to xml
******************************************************************************)

open Proof;;
open Xml_of_pb;;
open Libxml;;

let option f = function
  | Some x -> f x
  | None -> pc "";;

let elt_opt t f l = if l = [] then [] else [elt t (f l)];;

let coef = elt_int "coef";;
let var = elt_int "var";;
(*UNUSED:let power = elt_int "power";;*)
let mi_dimension = elt_int "dimension";;
let arg = elt_int "arg";;

let mapping f (s,x) = elt "mapping" [fun_symbol s; f x];;

let vector = List.map;;

let matrix xml_of_elt = List.map (fun v -> elt "row" (vector xml_of_elt v));;

let monomial (c,is) = elt "monomial" (coef c :: List.map var is);;

let polynomial ms = elt "polynomial" (List.map monomial ms);;

let poly_int = List.map (mapping polynomial);;

let mi_const xml_of_elt c = elt "const" (vector xml_of_elt c);;

let mi_arg xml_of_elt arg = elt "arg" (matrix xml_of_elt arg);;

let mi_fun xml_of_elt m = elt "mi_fun"
  (mi_const xml_of_elt m.mi_const :: List.map (mi_arg xml_of_elt) m.mi_args);;

let matrix_int_mapping xml_of_elt = mapping (mi_fun xml_of_elt);;

let matrix_int xml_of_elt mi =
  [ mi_dimension mi.mi_dim;
    elt "mi_map" (List.map (matrix_int_mapping xml_of_elt) mi.mi_int) ];;

let intMatrix2str = elt_int "velem";;

let arcticMatrix2str = function
  | Fin p    -> elt "velem" [elt_int "finite" p]
  | MinusInf -> elt "velem" [elt "minus_infinite" []];;

let tropicalMatrix2str = function
  | TroFin p    -> elt "velem" [elt_int "finite" p]
  | PlusInf -> elt "velem" [elt "plus_infinite" []];;

let string_of_bool = function true -> "true" | false -> "false";;

let elt_bool b = elt (string_of_bool b) [];;

let bool l = elt "bool" (List.map elt_bool l);;

let proj = function
  | None -> elt "proj" []
  | Some k -> elt_int "proj" k;;

let perm l = elt "perm" (List.map arg l);;

let arg_bool = List.map (mapping bool);;
let arg_proj = List.map (mapping proj);;
let arg_perm = List.map (mapping perm);;

let filter = function
  | Bool l -> bool l
  | Proj k -> proj (Some k)
  | Perm l -> perm l;;

let arg_filter = List.map (mapping (option filter));;

let simple_proj = List.map (mapping arg);;

let string_of_status = function Lex -> "lex" | Mul -> "mul";;

let status s = elt (string_of_status s) [];;

let status_mapping (f, (s, i)) =
  elt "mapping" [fun_symbol f; elt "status" [status s]; elt_int "prec" i];;

let rpo = List.map status_mapping;;

let rec red_ord = function
  | PolyInt pmap -> elt "poly_int" (poly_int pmap)
  | MatrixInt mi -> elt "matrix_int" (matrix_int intMatrix2str mi)
  | ArcticInt ai -> elt "arctic_int" (matrix_int arcticMatrix2str ai)
  | TropicalInt ai -> elt "tropical_int" (matrix_int tropicalMatrix2str ai)
  | ArcticBZInt ai -> elt "arctic_bz_int" (matrix_int arcticMatrix2str ai)
  | ArgBoolOrd (af, ro) -> elt "arg_bool"
      [elt "def" (arg_bool af); elt "order" [red_ord ro]]
  | ArgProjOrd (af, ro) -> elt "arg_proj"
      [elt "def" (arg_proj af); order ro]
  | ArgPermOrd (af, ro) -> elt "arg_perm"
      [elt "def" (arg_perm af); order ro]
  | ArgFilterOrd (af, ro) -> elt "arg_filter"
      [elt "def" (arg_filter af); order ro]
  | Rpo l -> elt "rpo" (rpo l)

and order ro = elt "order" [red_ord ro];;

let string_of_graph_type = function
  | HDE -> "hde"
  | HDE_Marked -> "hde_marked"
  | Unif -> "unif";;

let over_graph_type og = elt (string_of_graph_type og) [];;

let over_graph og = elt "graph" [over_graph_type og];;

let trs_rules rs = elt "rules" (List.map trs_rule rs);;
(*UNUSED:let srs_rules rs = elt "rules" (List.map srs_rule rs);;*)

let rec proof p = elt "proof" [proof_aux p]

and proof_aux = function
  | Trivial -> elt "trivial" []
  | MannaNess (false, ro, p) ->
      elt "manna_ness" [elt "order" [red_ord ro]; proof p]
  | MannaNess (true, ro, p) -> elt "manna_ness"
      [elt "order" [red_ord ro]; proof p; elt "usable_rules" []]
  | DP p -> elt_proof "dp" p
  | MarkSymb p -> elt_proof "mark_symbols" p
  | ArgBool (af, p) -> elt "arg_bool" [elt "def" (arg_bool af); proof p]
  | ArgProj (af, p) -> elt "arg_proj" [elt "def" (arg_proj af); proof p]
  | ArgPerm (af, p) -> elt "arg_perm" [elt "def" (arg_perm af); proof p]
  | ArgFilter (af, p) -> elt "arg_filter" [elt "def" (arg_filter af); proof p]
  | AsTrs p -> elt_proof "as_trs" p
  | AsSrs p -> elt_proof "as_srs" p
  | SrsRev p -> elt_proof "srs_rev" p
  | TrsRev p -> elt_proof "trs_rev" p
  | Decomp (og, l) -> elt "decomp" (over_graph og :: List.map component l)
  | FlatCC p -> elt_proof "flat_cc" p
  | RootLab p -> elt_proof "root_lab" p
  | Unlab p -> elt_proof "unlab" p
  | SubtermCrit (sp, p) ->
      elt "subterm_crit" [elt "proj" (simple_proj sp); proof p]

and elt_proof t p = elt t [proof p]

and component (rs, po) = elt "component"
  (match po with
    | Some p -> [trs_rules rs; proof p]
    | None -> [trs_rules rs]);;

let term_pos p = elt "position" (List.map arg p);;

let cet_mod_step s = elt "step"
  [term_pos s.cet_mod_step_pos; trs_rule s.cet_mod_step_rule];;

let cet_mod_steps = List.map cet_mod_step;;

let cet_step s = elt "step"
  (elt_opt "modulo" cet_mod_steps s.cet_step_mod_steps
   @ term_pos s.cet_step_pos :: trs_rule s.cet_step_rule :: []);;

let cet_steps = List.map cet_step;;

let trs_counter_example = function
  | CET_var_cond -> elt "var_cond" []
  | CET_loop c -> elt "loop"
      (elt "start" [term c.cet_start] :: elt "steps"
	 (cet_steps c.cet_steps)
       :: elt_opt "modulo" cet_mod_steps c.cet_mod @
	 term_pos c.cet_pos :: []);;

let word_pos = elt_int "position";;

let ces_mod_step s = elt "step"
  [word_pos s.ces_mod_step_pos; srs_rule s.ces_mod_step_rule];;

let ces_mod_steps = List.map ces_mod_step;;

let ces_step s = elt "step"
  (elt_opt "modulo" ces_mod_steps s.ces_step_mod_steps
   @ [word_pos s.ces_step_pos; srs_rule s.ces_step_rule]);;

let ces_steps = List.map ces_step;;

let srs_counter_example = function
  | CES_loop c -> elt "loop"
      (elt "start" (word c.ces_start) :: elt "steps" (ces_steps c.ces_steps)
       :: elt_opt "modulo" ces_mod_steps c.ces_mod @ [word_pos c.ces_pos]);;

let counter_example = function
  | CE_trs c -> elt "trs_counter_example" [trs_counter_example c]
  | CE_srs c -> elt "srs_counter_example" [srs_counter_example c];;

let certificate = function
  | Proof p -> proof p
  | Counter_example ce -> elt "counter_example" [counter_example ce];;
