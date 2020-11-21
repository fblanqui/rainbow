(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-09-22

proof check based on CoLoR extracted code
******************************************************************************)

open Util;;
open Problem;;
open Proof;;
open Error;;

open Problem0;;
open ATrs;;
open ATerm;;
open Bvector;;
open Datatypes;;
open Proof0;;
open BinPos;;
open BinInt;;
open ASignature;;

(*****************************************************************************)
(* convert a Rainbow/OCaml type into Coq/CoLoR type *)
(*****************************************************************************)

let nat = (*FIXME: extract nat to a private data type?*)
  let rec aux = function
    | 0 -> O
    | k -> S (aux (k-1))
  in fun k ->
    if k < 0 then invalid_arg "not a nat"
    else aux k;;

let rec positive = function
  | x when x <= 0 -> invalid_arg "not a positive"
  | 1 -> Coq_xH
  | x when x mod 2 = 0 -> Coq_xO (positive (x/2))
  | x -> Coq_xI (positive (x/2));;

let coq_Z = function
  | 0 -> Z0
  | x when x < 0 -> Zneg (positive (-x))
  | x -> Zpos (positive x);;

let vector elt =
  let rec aux = function
    | [] -> Vnil
    | x :: xs -> Vcons (elt x, O (*FIXME?*), aux xs)
  in aux;;

(*****************************************************************************)
(* convert a Rainbow problem into a CoLoR problem *)
(*****************************************************************************)

let symbol = Obj.repr;;

let rec term = function
  | Problem.Var k -> Var (nat k)
  | App (f, ts) -> Fun (symbol f, vector term ts);;

let rule r = { lhs = term r.trs_lhs; rhs = term r.trs_rhs };;

let rules = List.map rule;;

let trs t =
  let s = match t.trs_algebra with
    | Varyadic -> not_supported "varyadic signatures"
    | Signature m ->
	(*FIXME: precompute conversions*)
	let ar f = nat (SymbMap.find (Obj.obj f) m) in
	let beq f g = Obj.obj f = Obj.obj g in
	  { arity = ar; beq_symb = beq } in
  let r =
    if t.trs_strategy <> None then not_supported "strategies";
    (*FIXME: convert in relative rules*)
    if t.trs_axioms <> [] then not_supported "axioms";
    if t.trs_le_rules = [] then FullTerm (rules t.trs_rules)
    else RelTerm (rules t.trs_le_rules, rules t.trs_rules)
  in s, r;;

let problem = function
  | Trs t -> trs t
  | Srs _ -> not_supported "SRS";;

(*****************************************************************************)
(* convert a Rainbow proof into a CoLoR proof *)
(*****************************************************************************)

let monom = List.map nat;;

let monomial (c, m) = coq_Z c, monom m;;

let polynomial = List.map monomial;;

let poly_int_mapping (f, p) = symbol f, polynomial p;;

let poly_int = List.map poly_int_mapping;;

let rec proof = function
  | Trivial -> TP_ProblemEmpty
  | MannaNess (_, PolyInt pi, p) -> TP_PolyInt (poly_int pi, proof p)
  | _ -> not_supported "proof kind";;

let certificate = function
  | Proof p -> proof p
  | Counter_example _ -> not_supported "counter examples";;
