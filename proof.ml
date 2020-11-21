(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Ducas Leo, 2007-08-10
- Frederic Blanqui, 2006-05-31, 2009-10-27 (polynomials)
- Adam Koprowski, 2007-04-18 (matrix interpretations)

internal representation of termination proofs
******************************************************************************)

open Problem;;
open Error;;

(*****************************************************************************)
(* domains *)
(*****************************************************************************)

type arctic_dom = MinusInf | Fin of int;;

type tropical_dom = PlusInf | TroFin of int;;

(*****************************************************************************)
(* matrices *)
(*****************************************************************************)

type 'a vector = 'a list;;
type 'a matrix = 'a (*raw*) vector list;;

(*****************************************************************************)
(* polynomials *)
(*****************************************************************************)

type monom = int list;;
type polynom = (int * monom) list;;

(*****************************************************************************)
(* polynomial interpretations *)
(*****************************************************************************)

type poly_int = (symbol * polynom) list;;

(*****************************************************************************)
(* matrix interpretations *)
(*****************************************************************************)

type 'a mi_fun = { mi_const : 'a vector; mi_args : 'a matrix list };;

type 'a matrix_based_int =
    { mi_dim : int; mi_int : (symbol * 'a mi_fun) list };;

type matrix_int = int matrix_based_int;;

type arctic_int = arctic_dom matrix_based_int;;

type tropical_int = tropical_dom matrix_based_int;;

(*****************************************************************************)
(* dependency graph approximations *)
(*****************************************************************************)

type over_graph = HDE | HDE_Marked | Unif;;

(*****************************************************************************)
(* arguments filterings *)
(*****************************************************************************)

type arg_bool = (symbol * bool list) list;;

type arg_proj   = (symbol * int option) list;;

type arg_perm   = (symbol * int list) list;;

type filter = Proj of int | Bool of bool list | Perm of int list;;

type arg_filter = (symbol * filter option) list;;

type simple_proj = (symbol * int) list;;

(*****************************************************************************)
(* RPO precedence and status *)
(*****************************************************************************)

type status = Lex | Mul;;

type status_precedence = (symbol * (status * int)) list;;

(*****************************************************************************)
(* reduction orderings *)
(*****************************************************************************)

type red_ord =
  | PolyInt of poly_int
  | MatrixInt of matrix_int
  | ArcticInt of arctic_int
  | ArcticBZInt of arctic_int
  | TropicalInt of tropical_int
  | ArgBoolOrd of arg_bool * red_ord
  | ArgProjOrd of arg_proj * red_ord
  | ArgPermOrd of arg_perm * red_ord
  | ArgFilterOrd of arg_filter * red_ord
  | Rpo of status_precedence;;

(*****************************************************************************)
(* termination certificates *)
(*****************************************************************************)

type proof =
  | Trivial
  | MannaNess of bool (*with usable rules?*) * red_ord * proof
  | MarkSymb of proof
  | DP of proof
  | ArgBool of arg_bool * proof
  | ArgProj of arg_proj * proof
  | ArgPerm of arg_perm * proof
  | ArgFilter of arg_filter * proof
  | AsTrs of proof
  | AsSrs of proof
  | SrsRev of proof
  | TrsRev of proof
  | Decomp of over_graph * component list
  | FlatCC of proof
  | RootLab of proof
  | Unlab of proof
  | SubtermCrit of simple_proj * proof

and component = trs_rule list * proof option;;

(*****************************************************************************)
(* TRS non-termination certificates *)
(*****************************************************************************)
(* FIXME: use this section for the old rainbow used int type *)


type position = int list;;

type cet_mod_step = {
  cet_mod_step_pos : position;
  cet_mod_step_rule : trs_rule };;

type cet_step = {
  cet_step_mod_steps : cet_mod_step list;
  cet_step_pos : position;
  cet_step_rule : trs_rule };;

type trs_loop = {
  cet_start : term;
  cet_steps : cet_step list;
  cet_mod : cet_mod_step list;
  cet_pos : position };;

type trs_counter_example =
  | CET_var_cond
  | CET_loop of trs_loop;;

(*****************************************************************************)

(*****************************************************************************)
(* SRS non-termination certificates *)
(*****************************************************************************)

type ces_mod_step = {
  ces_mod_step_pos : int;
  ces_mod_step_rule : srs_rule };;

type ces_step = {
  ces_step_mod_steps : ces_mod_step list;
  ces_step_pos : int;
  ces_step_rule : srs_rule };;

type srs_loop = {
  ces_start : word;
  ces_steps : ces_step list;
  ces_mod : ces_mod_step list;
  ces_pos : int };;

type srs_counter_example =
  | CES_loop of srs_loop;;

type counter_example =
  | CE_trs of trs_counter_example
  | CE_srs of srs_counter_example;;

(*****************************************************************************)
(* certificates *)
(*****************************************************************************)

type certificate =
  | Proof of proof
  | Counter_example of counter_example;;

(*****************************************************************************)
(* constructors for and operations on polynomials *)
(*****************************************************************************)

type nb_vars = int;;

(* constructors for monomials *)

let clist x =
  let rec aux k = if k <= 0 then [] else x :: aux (k-1) in aux;;

let monom_1 = clist 0;;

let monom_xi n i =
  if i <= 0 then error_fmt
    (Printf.sprintf "non-positive polynomial variable number %d" i)
  else if i > n then error_fmt
    (Printf.sprintf "polynomial variable %d greater than arity %d" i n)
  else clist 0 (i-1) @ 1 :: clist 0 (n-i);;

(* constructors for polynomials *)

let poly_const n k = [(k, monom_1 n)];;
let poly_xi n i = [(1, monom_xi n i)];;

(*****************************************************************************)

let poly_sum = List.append;;
let poly_sums = List.flatten;;

(* product *)

let poly_prod_monom m1 m2 =
  try List.map2 (+) m1 m2
  with Invalid_argument _ -> error_fmt
    "multiplication of two monomials of different arities";;

let poly_prod_coef_monom (c1,m1) (c2,m2) = c1 * c2, poly_prod_monom m1 m2;;

(*UNUSED:
let poly_prod_coef_monoms =
  let rec aux cm1 = function
    | [] -> cm1
    | cm2 :: p -> aux (poly_prod_coef_monom cm1 cm2) p
  in fun n -> aux (1, monom_1 n);;*)

let poly_prod_aux cm = List.map (poly_prod_coef_monom cm);;

let poly_prod p =
  let rec aux r = function
    | [] -> r
    | cm :: q -> aux (poly_sum (poly_prod_aux cm p) r) q
  in aux [];;

let poly_prods =
  let rec aux r = function
    | [] -> r
    | p :: ps -> aux (poly_prod p r) ps
  in fun n -> aux (poly_const n 1);;



