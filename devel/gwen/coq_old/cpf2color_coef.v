(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2011-04-06

* Translate CPF type into CoLoR type.

*)

Set Implicit Arguments.

Require Import ZUtil cpf cpf_util SemiRing2 cpf2color_number QArith.

(***********************************************************************)
(** Translate [coefficient] of CPF type into CoLoR type. *)

Section coef.

  (***********************************************************************)
  (** Domain natural numbers. *)
  
  Definition color_coef c : result integer :=
    match c with
      | Coefficient_number i => color_number i
      | Coefficient_minusInfinity => Ko _ TcoefMinusInf
      | Coefficient_plusInfinity => Ko _ TcoefPlusInf
      | Coefficient_vector _ => Ko _ TcoefVector
      | Coefficient_matrix _ => Ko _ TcoefMatrix
    end.

  (***********************************************************************)
  (** Domain rational numbers. *)

  Definition color_coef_Q (c: coefficient) : result Q :=
    match c with
      | Coefficient_number i => color_number_rationals i
      | Coefficient_minusInfinity => Ko _ TcoefMinusInf
      | Coefficient_plusInfinity => Ko _ TcoefPlusInf
      | Coefficient_vector _ => Ko _ TcoefVector
      | Coefficient_matrix _ => Ko _ TcoefMatrix
    end.

  (***********************************************************************)
  (** Domain Arctic natural numbers. *)
  
  (* TODO: example *)
  
  (* In SemiRingType.v: A0 = minusInf; A1 = Pos 0 *)
  
  Definition color_coef_arcnat (c: coefficient) : result ArcticDom :=
    match c with
      | Coefficient_number i =>
        match color_number i with
          | Ok i => Match int_to_nat i With i ===> Ok (Pos i)
          | Ko e => Ko _ ENotArcNat
        end
      | Coefficient_minusInfinity => Ok MinusInf
      | Coefficient_plusInfinity => Ko _ TcoefPlusInf
      | Coefficient_vector _ => Ko _ TcoefVector_arc
      | Coefficient_matrix _ => Ko _ TcoefMatrix_arc
    end.

  (***********************************************************************)
  (** Domain Arctic integer numbers (below zero). *)
 
  Definition color_coef_arcbz c : result ArcticBZDom :=
    match c with
      | Coefficient_number i =>
        match color_number i with
          | Ok i => Ok (Fin i)
          | Ko e => Ko _ ENotArcBZ
        end
      | Coefficient_minusInfinity => Ok MinusInfBZ
      | Coefficient_plusInfinity => Ko _ TcoefPlusInf
      | Coefficient_vector _ => Ko _ TcoefVector_arcbz
      | Coefficient_matrix _ => Ko _ TcoefMatrix_arcbz
    end.

  (***********************************************************************)
  (** Domain Tropical numbers. *)

  Definition color_coef_trop c : result TropicalDom :=
    match c with
      | Coefficient_number i =>
        match color_number i with
          | Ok i => Ok (TPos (Z.to_nat i))
          | Ko e => Ko _ ENotTrop
        end
      | Coefficient_minusInfinity => Ko _ TcoefMinusInf
      | Coefficient_plusInfinity => Ok PlusInf
      | Coefficient_vector _ => Ko _ TcoefVector_trop
      | Coefficient_matrix _ => Ko _ TcoefMatrix_trop
    end.

End coef.
