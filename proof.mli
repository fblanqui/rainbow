(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Ducas Leo, 2007-08-10
- Frederic Blanqui, 2006-05-31, 2009-10-27 (polynomials)
- Adam Koprowski, 2007-04-18 (matrix interpretations)

internal representation of termination proofs
******************************************************************************)

(*open Util;;*)
open Problem;;

(*****************************************************************************)
(* domains *)
(*****************************************************************************)

(* FIXME: integer in cpf has type coq_Z *)

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

type arg_proj = (symbol * int option) list;;

type arg_perm = (symbol * int list) list;;

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
  | MannaNess of bool * red_ord * proof
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

(* monomials *)
val clist : 'a -> int -> 'a list
val monom_1 : int -> int list
val monom_xi : int -> int -> int list

(* polynomials *)
val poly_const : nb_vars -> int -> polynom
val poly_xi : nb_vars -> int -> polynom

(*****************************************************************************)

val poly_sum : polynom -> polynom -> polynom;;
val poly_sums : polynom list -> polynom;;
val poly_prod : polynom -> polynom -> polynom;;
val poly_prods : nb_vars -> polynom list -> polynom;;
