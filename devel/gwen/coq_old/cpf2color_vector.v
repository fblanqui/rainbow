(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2011-04-06

* Translate CPF type into CoLoR type.

*)

Set Implicit Arguments.

Require Import VecArith2 cpf2color_coef SemiRing2 cpf_util cpf.

(***********************************************************************)
(** Translate [vector] of CPF type into CoLor type. *)

Section vector.

  (* Assuming a dimension of type natural numbers.*)
  
  Variable dim : nat.

  (****************************************************************************)
  (** Domain natural numbers *)

  (** REMARK: in CPF, matrices are represented with column vectors
     while in Rainbow, matrices are represented with row vectors;
     index of rows and columns starting from [0]. *)
  
  (** [color_column_of_cpf_column] define a function convert CPF
     type to CoLoR type, that take a column matrix of size [dim] of
     integer and convert it into a result vector of size [dim] of
     natural numbers. First check each element in the list is indeed an
     natural numbers. If there is an negative number in this list it
     will return an error "ENotANat". Otherwise it returns an [Ok
     cols], start to build this list to a list of result vector of size
     [dim]. 
     
     For example: given a list [col_int: 1 :: 0 :: nil, dimension = 2].
     
     Result: [vector = Ok 1, Ok 0, Ok nil].
     
     For example: given a list [col_int: -1 :: 0 :: nil, dimension = 2.]
     Result: [ENotANat]. *)
  
  Definition color_column_of_cpf_column (col: list coefficient):
    result (VecUtil.vector nat dim) :=
    Match map color_coef col With col_int ===> (* FIXME *)
    Match list_int_to_list_nat col_int With col_nat ===>
    vector_of_list col_nat dim.
  
  Definition color_vector (v : vector):
    result (VecUtil.vector nat dim) :=
    match v with
      | Vector_vector cs => color_column_of_cpf_column cs
    end.

  (****************************************************************************)
  (** Domain Arctic natural numbers. *)

  (** [color_column_of_cpf_column_arcnat] define a function convert
     CPF type to CoLoR type, that take a column matrix of size [dim]
     of integer and convert it into a result vector of size [dim] of
     arctic natural numbers. First check each element in the list is
     indeed an natural numbers, then convert it to ArcticDom
     type. If there is an negative number in this list it will
     return an error "ENotANat". Otherwise it returns an [Ok cols],
     start to build this list to a list of result vector of size
     [dim]. 
     For example: given a list col_arcnat: 1 :: MinusInf :: nil,
     dimension = 2.
     Result: vector = Ok (Pos 1), Ok MinusInf, Ok nil.
     For example: given a list col_int: -1 :: 0 :: nil, dimension = 2.
     Result: ENotANat. *)
  
  (* FIXME: this is a different here from matrix nat: *)

  Definition color_column_of_cpf_column_arcnat (col: list coefficient) :
    result (VecUtil.vector ArcticDom dim) :=
    Match map color_coef_arcnat col With col_nat ===>
    vector_of_list col_nat dim.
  
  (*Definition color_column_of_cpf_column_arcnat (col: list coefficient) :
     result (VecUtil.vector ArcticDom dim) :=
     Match map color_coef_arcnat col With col_arcnat ==>
     vector_of_list col_arcnat dim.*)

  Definition color_vector_arcnat (v : vector) :
    result (VecUtil.vector ArcticDom dim) :=
    match v with
      | Vector_vector cs => color_column_of_cpf_column_arcnat cs
    end.
  
  (****************************************************************************)
  (** Domain Arctic below zero. *)
  
  (** [color_column_of_cpf_column_arcbz] define a function convert
     CPF type to CoLoR type, that take a column matrix of size [dim]
     of integer and convert it into a result vector of size [dim] of
     arctic integer numbers. Convert it to domain [ArcticBZDom]. It
     returns an [Ok cols], start to build this list to a list of
     result vector of size [dim].
     
     For example: given a list [col_arcnat: 1 :: MinusInfBZ :: nil],
     [dimension = 2].
     Result: [vector = Ok (Fin 1), Ok MinusInfBZ, Ok nil]. *)
  
  Definition color_column_of_cpf_column_arcbz (col: list coefficient) :
    result (VecUtil.vector ArcticBZDom dim) :=
    Match map color_coef_arcbz col With col_arcbz ===>
    vector_of_list col_arcbz dim.
 
  Definition color_vector_arcbz (v : vector) :
    result (VecUtil.vector ArcticBZDom dim) :=
    match v with
      | Vector_vector cs => color_column_of_cpf_column_arcbz cs
    end.

  (****************************************************************************)
  (** Domain Tropical *)
  
  (* TODO: example *)
  
  Definition color_column_of_cpf_column_trop (col: list coefficient) :
    result (VecUtil.vector TropicalDom dim) :=
    Match map color_coef_trop col With col_trop ===>
    vector_of_list col_trop dim.
  
  Definition color_vector_trop (v : vector) :
    result (VecUtil.vector TropicalDom dim) :=
    match v with
      | Vector_vector cs => color_column_of_cpf_column_trop cs
    end.
  
End vector.