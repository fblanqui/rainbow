(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2011-04-06

* Translate CPF type into CoLoR type.

*)

Set Implicit Arguments.

Require Import cpf cpf_util cpf2color_poly AMatrixBasedInt2_Nat
  AMatrixBasedInt2_ArcticNat AMatrixBasedInt2_ArcticBZ
  AMatrixBasedInt2_Trop Polynom Matrix2.

(***********************************************************************)
(** Translate CPF polynomial [interpret] into CoLoR interpret. *)

Section interpret.
    
  Variable arity : symbol -> nat.
  
  (** Polynomial interpretation domain natural numbers. *)

  Definition color_interpret_poly (is: symbol * cpf.arity * function) :
    result {f : symbol & poly (arity f)} :=
    let '(f, _, fn) := is in
      Match color_function (arity f) fn With p ===>
      Ok (existT f p).

  (***********************************************************************)
  (** Polynomial interpretation domain rational numbers. *)
  
  Require Import NewPolynom2.

  Definition color_interpret_polyQ (is: symbol * cpf.arity * function):
    result {f : symbol & Qpoly (arity f)} :=
  let '(f, _, fn) := is in
    Match color_functionQ (arity f) fn With p ===>
    Ok (existT f p).

  (***********************************************************************)
  (** Matrix interpretation domain natural numbers. *)
  
  Variable dim: nat.
  
  Notation mint := (matrixInt matrix dim).

  Implicit Arguments color_matrix_function [dim].  

  Definition color_interpret_matrix (is : symbol * cpf.arity * function) :
    result {f : symbol & mint (arity f)} :=
    let '(f, _, fn) := is in
      Match (color_matrix_function (arity f) fn) With m ===>
      Ok (existT f m).

  (***********************************************************************)
  (** Matrix interpretation domain arctic natural numbers. *)

  Implicit Arguments color_matrix_arcnat_function [dim].  
  
  Definition color_matrix_arc_interpret (is : symbol * cpf.arity * function) :
    result {f : symbol & matrixInt_arcnat matrix_arcnat dim (arity f)} :=
    let '(f, _, fn) := is in
      Match (color_matrix_arcnat_function (arity f) fn) With mi ===>
      Ok (existT f mi).
  
  (***********************************************************************)
  (** Matrix interpretation domain arctic integer numbers. *)

  Implicit Arguments color_matrix_arcbz_function [dim].

  Definition color_matrix_arcbz_interpret
    (is : symbol * cpf.arity * function) :
    result {f : symbol & matrixInt_arcbz matrix_arcbz dim (arity f)} :=
    let '(f, _, fn) := is in
      Match (color_matrix_arcbz_function (arity f) fn) With mi ===>
      Ok (existT f mi).
  
  (***********************************************************************)
  (** Matrix interpretation domain tropical numbers. *)
  
  Implicit Arguments color_matrix_trop_function [dim].

  Definition color_matrix_tropical_interpret
    (is : symbol * cpf.arity * function) :
    result {f : symbol & matrixInt_trop matrix_trop dim (arity f)} :=
    let '(f, _, fn) := is in
      Match (color_matrix_trop_function (arity f) fn) With mi ===>
      Ok (existT f mi).
  
End interpret.