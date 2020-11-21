(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2011-04-06

* Translate CPF type into CoLoR type.

*)

Set Implicit Arguments.

Require Import cpf cpf_util Matrix2 cpf2color_vector.

(***********************************************************************)
(** Translate [matrix] of CPF type into CoLor type. *)

Section matrix.

  (* Assuming a dimension of type natural numbers. *)

  Variable dim: nat.
    
  (** [color_matrix_of_cpf_matrix] define a function convert CPF
     type to CoLoR type, first map a list of column integer to a list
     of result vector of size [dim], then build each vector to each
     column matrix of size [dimxdim], the use the matrix transpose to
     convert rows matrix to columns matrix.
     
     For example: Given a list of list int name [cols: (1 :: 0 :: nil)
     :: (2 :: 0 :: nil) :: nil, dimension 2].
     
     Check the lenght of the list [vector_of_list] if it is not equal
     to the size [dim] then return an error [EVector_of_list],
     otherwise return an [Ok e], where [e] is a result vector of size
     [dim]. Finally, return an matrix transpose because matrix in CoLoR
     representated by row matrix where in CPF matrix represented by
     column matrix.
     
     Result from list [cols], [dimension = 2]
     
     [M^T = |1 0 |
     |2 0 |] *)
  
  Definition color_matrix_of_cpf_matrix (cols: list (list coefficient)) 
    : result (matrix dim dim) :=
    Match map (color_column_of_cpf_column dim) cols With cols ===>
    Match vector_of_list cols dim With M ===>
    Ok (mat_transpose M).
  
  Definition color_matrix (m : cpf.matrix) : result (matrix dim dim) :=
    match m with
      | Matrix_matrix vs => color_matrix_of_cpf_matrix vs
    end.

  (***********************************************************************)
  (* Domain Arctic natural numbers. *)

  (** [color_matrix_of_cpf_matrix_arcnat] define a function convert
     CPF type to CoLoR type, first map a list of column integer to a
     list of result vector of size [dim], then convert it to
     [ArcticDom] domain, then build each vector to each column
     matrix of size [dimxdim], then use the matrix transpose of
     matrix arctic to get the convert rows matrix to columns matrix.
     
     For example: Given a list of list int name [cols: (1 ::
     MinusInf :: nil) :: (2 :: MinusInf :: nil) :: nil, dimension
     2].
       
     Convert to a list of domain [ArcticDom: (Pos 1 :: MinusInf ::
     nil) :: (Pos 2 :: MinusInf :: nil) :: nil].
     
     Check the lenght of the list [vector_of_list] if it is not equal
     to the size [dim] then return an error [EVector_of_list],
     otherwise return an [Ok e], where [e] is a result vector of size
     [dim]. Finally, return an matrix transpose because matrix in CoLoR
     representated by row matrix where in CPF matrix represented by
     column matrix.
     
     Result from list [cols], [dimension = 2],   
     
     [M^T = |1 MinusInf |
     |2 MinusInf |] *)
  
  Definition color_matrix_of_cpf_matrix_arcnat (cols: list (list coefficient)) :
    result (matrix_arcnat dim dim) :=
    Match map (color_column_of_cpf_column_arcnat dim) cols With cols ===>
    Match vector_of_list cols dim With M ===>
    Ok (mat_transpose_arcnat M).
  
  Definition color_matrix_arcnat (m : cpf.matrix) :
    result (matrix_arcnat dim dim) :=
    match m with
      | Matrix_matrix vs => color_matrix_of_cpf_matrix_arcnat vs
    end.

  (***********************************************************************)
  (* Domain Arctic integer numbers (below zero). *)

  (** [color_matrix_of_cpf_matrix_arcbz] define a function convert
     CPF type to CoLoR type, first map a list of column integer to a
     list of result vector of size [dim], then convert it to
     [ArcticBZDom] domain, then build each vector to each column matrix
     of size [dimxdim], the use the matrix transpose of matrix
     arctic to get the convert rows matrix to columns matrix.
     
     For example: Given a list of list int name [cols: (1 ::
     MinusInfBZ :: nil) :: (2 :: MinusInfBZ :: nil) :: nil,
     dimension 2].
     
     Convert to a list of domain [ArcticDom: (Fin 1 :: MinusInfBZ ::
     nil) :: (Fin 2 :: MinusInfBZ :: nil) :: nil].
     
     Check the lenght of the list [vector_of_list] if it is not equal
     to the size [dim] then return an error [EVector_of_list],
     otherwise return an [Ok e], where [e] is a result vector of size
     [dim]. Finally, return an matrix transpose because matrix in CoLoR
     representated by row matrix where in CPF matrix represented by
     column matrix.
     
     Result from list [cols], [dimension = 2],   
     [M^T = |1 MinusInfBZ |
     |2 MinusInfBZ |] *)
  
  Definition color_matrix_of_cpf_matrix_arcbz (cols: list (list coefficient)) :
    result (matrix_arcbz dim dim) :=
    Match map (color_column_of_cpf_column_arcbz dim) cols With cols ===>
    Match vector_of_list cols dim With M ===> 
    Ok (mat_transpose_arcbz M).
    
  Definition color_matrix_arcbz (m : cpf.matrix) :
    result (matrix_arcbz dim dim) :=
    match m with
      | Matrix_matrix vs => color_matrix_of_cpf_matrix_arcbz vs
    end.

  (***********************************************************************)
  (* Domain Tropical numbers. *)

  Definition color_matrix_of_cpf_matrix_trop (cols: list (list coefficient)) :
    result (matrix_trop dim dim) :=
    Match map (color_column_of_cpf_column_trop dim) cols With cols ===>
    Match vector_of_list cols dim With M ===> 
    Ok (mat_transpose_trop M).

  Definition color_matrix_trop (m : cpf.matrix) :
    result (matrix_trop dim dim) :=
    match m with
      | Matrix_matrix vs => color_matrix_of_cpf_matrix_trop vs
    end.

End matrix.