(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2011-04-06

* Translate CPF type into CoLoR type.

*)

Set Implicit Arguments.

Require Import List Polynom cpf cpf_ind cpf_util cpf2color_coef
  AMatrixInt2 AMatrixBasedInt2_Nat Matrix2 cpf2color_matrix
  cpf2color_vector VecUtil VecArith2 AMatrixBasedInt2_ArcticNat
  AMatrixBasedInt2_ArcticBZ AMatrixBasedInt2_Trop.

(***********************************************************************)
(** ** Translate  [polynomial] of cpf type into  [poly] of CoLoR type.
   
   Polynomial function over domain natural numbers.
   
   In CoLoR the type of polynomials depends on the maximum number of
   [n] variables. *)

(** REMARK: in Coq [Positive integer] starting from [1], list of
   variables in CoLoR starting from [0] *)

Section poly.

  Variable n : nat.
  
  Fixpoint color_poly p : result (poly n) :=
    match p with
      | Polynomial_coefficient c =>
        Match color_coef c With d ===>
        Ok (pconst n d)
      | Polynomial_variable x =>
        let x := (nat_of_P x) - 1 in
          match lt_dec x n with
            | left h => Ok (pxi h)
            | _ => Ko _ EpolyVarTooBig
          end
      | Polynomial_sum l =>
        let fix color_poly_sum acc l :=
          match l with
            | nil => Ok acc
            | p :: l' =>
              Match color_poly p With p ===>
              color_poly_sum (pplus p acc) l'
          end in color_poly_sum (pzero n) l
      | Polynomial_product l =>
        let fix color_poly_prod acc l :=
          match l with
            | nil => Ok acc
            | p :: l' =>
              Match color_poly p With p ===>
              color_poly_prod (pmult p acc) l'
          end in color_poly_prod (pconst n 1) l
      | Polynomial_max _ => Ko _ TpolyMax
      | Polynomial_min _ => Ko _ TpolyMin
    end.
  
  Definition color_function f := color_poly f.

  (****************************************************************************)
  (** ** Polynomial function over domain rational numbers. *)
  
  Open Scope Q_scope.

  Require Import NewPolynom2.

  Fixpoint color_polyQ (p: polynomial) : result (Qpoly n) :=
    match p with
      | Polynomial_coefficient c =>
        Match color_coef_Q c With d ===>
        Ok (Qpconst n d)
      | Polynomial_variable x =>
        match lt_dec ((nat_of_P x) - 1) n with
          | left h => Ok (Qpxi h) (* x < y *)
          | _ => Ko _ EpolyVarTooBig (* ~ x < y *)
        end
      | Polynomial_sum l =>
        let fix color_poly_sum acc l :=
          match l with
            | nil => Ok acc
            | p :: l' =>
              Match color_polyQ p With p ===>
              color_poly_sum (padd p acc) l'
          end in color_poly_sum (Qpzero n) l
      | Polynomial_product l =>
        let fix color_poly_prod acc l :=
          match l with
            | nil => Ok acc
            | p :: l' =>
              Match color_polyQ p With p ===>
              color_poly_prod (pmult p acc) l'
          end in color_poly_prod (Qpconst n 1) l
      | Polynomial_max _ => Ko _ TpolyMax
      | Polynomial_min _ => Ko _ TpolyMin
    end.

  Definition color_functionQ (f: polynomial) := color_polyQ f.

  (****************************************************************************)
  (** ** Polynomial function for matrix interpretation over domain
     natural numbers. In CoLoR the type of polynomials depends on the
     maximum of number of [n] variables. Assuming a maximum number [n] of
     variables.  Define polynomial function for matrix interpretation
     over domain natural numbers. *)
  
  (** Matrix interpretations where the elements are
     vectors. Example: if the domain is naturals, then the
     coefficients in front of variables have to be matrices and the
     constants should be vectors over the naturals.
     
     Note that when using polynomials over a vector-domain, then the
     "constant coefficient" is a vector whereas the other
     coefficients are matrices. Moreover, in this case only linear
     polynomials are allowed. For dimension [d = 1], the matrix
     interpretaions coincide with linear polynomial interpretations.
     
     Polynomial function for matrix interpretation over natural numbers:
     Formula of matrix interpretation:
     [f (v1,...,vn) = F1.v1 + ... + Fn.vn + f0; (1)]
     (where [v1,...,vn, f0]: are vector)
     
     [Variable] return a position [i-th] of variable called [x] that
     attached to matrix coefficient where [arity > 1]; if variable [x]
     does not occurs then this coefficient is [0] (the zero matrix);
     REMARK: [Variable] [i] has type positive integer starting from
     [1], list of variables in CoLoR starting from [0].
     
     [Polynomial_sum]/[Polynomial_product]: [v + \sum Mi * xi; i \in
     (1, k)]; where [v] is a vector, a polynomial function: [M2.x2 + v
     + M1.x1] is also a certificate.
     
     [Coefficient]: for each function symbol [F] of arity [n] from
     the signature, declare variables [F1, ..., Fn] for square
     matrices [(d x d)] (in the case of [Coefficient_matrix]); and a
     variable [f] for a (column) vector of [(d x 1)] (in the case of
     [Coefficient_vector)].
     
     Standard polynomial orders over a specified domain (a semiring
     or something else). Note that if the domain is "matrices of
     naturals" then everything has to be a matrix, even the
     constants. This is in contrast to "matrixInterpretations" where
     the constants are vectors.*)
  
  Variable dim : nat.

  Notation mint := (matrixInt matrix dim).

  Implicit Arguments color_matrix [dim].
  Implicit Arguments color_vector [dim].

  Open Scope nat_scope.

  Fixpoint color_poly_matrixInt (p: polynomial) mi: result (mint n) :=
    match p with
      | Polynomial_sum l =>
        let fix color_sum_mint acc l :=
          match l with
            | nil => Ok acc
            | p1 :: l' =>
              Match color_poly_matrixInt p1 acc With Mi ===>
              color_sum_mint Mi l'
          end in color_sum_mint mi l
      | Polynomial_product
        (Polynomial_variable i ::
          Polynomial_coefficient (Coefficient_matrix m) :: nil)
      | Polynomial_product 
        (Polynomial_coefficient (Coefficient_matrix m) ::
          Polynomial_variable i :: nil) =>
        let i := (nat_of_P i) - 1 in
          Match color_matrix m With M ===>
          match lt_dec i n with
            | left h => Ok ({|const := (const mi); (* n < m *)
              args := Vreplace (args mi) h M|}) (* ~n < m*)
            | _ => Ko _ EpolyVarTooBig_matrix
          end
      | Polynomial_product
        (Polynomial_coefficient (Coefficient_vector v) :: nil) =>
        Match color_vector v With v ===>
        Ok {| const := v; args := (args mi)|}
      | Polynomial_product nil => Ok mi
    (* | Polynomial_coefficient (Coefficient_matrix m) =>
       Match color_matrix m With M ==>
       Ok ({|const := (const mi); args := Vconst M n |})*)
    (* Rainbow does not support the const is a matrix; this one should
       return const is M and args is (args mi) *)
      | _ => Ko _ TPoly_MatrixNatInt
    end.

  Definition color_matrix_function (f:polynomial) :=
    let mi :={|const := zero_vec dim;
      args := Vconst (zero_matrix dim dim) n|} in
    color_poly_matrixInt f mi.
  
  (****************************************************************************)
  (** Polynomial function for matrix interpretation over arctic
     natural numbers: Formula of matrix interpretation: [f
     (v1,...,vn) = F1.v1 + ... + Fn.vn + f0; (1)] (where [v1,...,vn,
     f0]: are vectors).
     
     [Variable] return a position [i-th] of variable called [x] that
     attached to matrix coefficient where [arity > 1]; if variable [x]
     does not occurs then this coefficient is [0] (the zero matrix);
     REMARK: [Variable] [i] has type positive integer starting from
     [1], list of variables in CoLoR starting from [0].
     
     [Polynomial_sum]/[Polynomial_product]: [v + \sum Mi * xi; i \in
     (1, k)]; where [v] is a vector, a polynomial function: [M2.x2 + v
     + M1.x1] is also a certificate.
     
     [Coefficient]: for each function symbol [F] of arity [n] from
     the signature, declare variables [F1, ..., Fn] for square
     matrices [(d x d)] (in the case of [Coefficient_matrix]); and a
     variable [f] for a (column) vector of [(d x 1)] (in the case of
     [Coefficient_vector)]. *)

  Implicit Arguments color_matrix_arcnat [dim].
  Implicit Arguments color_vector_arcnat [dim].

  Fixpoint color_poly_arcnat_matrixInt (p : polynomial) mi :
    result (matrixInt_arcnat matrix_arcnat dim n) :=
    match p with
      | Polynomial_sum l =>
        let fix color_sum_mint acc l :=
          match l with
            | nil => Ok acc
            | p1 :: l' =>
              Match color_poly_arcnat_matrixInt p1 acc With Mi ===>
              color_sum_mint Mi l'
          end in color_sum_mint mi l
      | Polynomial_product
        (Polynomial_variable i ::
          Polynomial_coefficient (Coefficient_matrix m) :: nil)
      | Polynomial_product 
        (Polynomial_coefficient (Coefficient_matrix m) ::
          Polynomial_variable i :: nil) =>
        let i := (nat_of_P i) - 1 in
          Match color_matrix_arcnat m With M ===>
          match lt_dec i n with
            | left h => Ok ({|const_arcnat := (const_arcnat mi);
              args_arcnat := Vreplace (args_arcnat mi) h M|})
            | _ => Ko _ EpolyVarTooBig_matrix
          end
      | Polynomial_product
        (Polynomial_coefficient (Coefficient_vector v) :: nil) =>
        Match color_vector_arcnat v With v ===>
        Ok {| const_arcnat := v; args_arcnat := (args_arcnat mi)|}
      | Polynomial_product nil => Ok mi
      | _ => Ko _ TPoly_MatrixInt_ArcNat
    end.
  
  Definition color_matrix_arcnat_function f :=
    let mi :={|const_arcnat := zero_vec_arcnat dim;
      args_arcnat := Vconst (zero_matrix_arcnat dim dim) n|} in
    color_poly_arcnat_matrixInt f mi.

  (****************************************************************************)
   (** Polynomial function for matrix interpretation over arctic
       integer numbers: Formula of matrix interpretation: [f
       (v1,...,vn) = F1.v1 + ... + Fn.vn + f0; (1)] (where [v1,...,vn,
       f0]: are vectors).
       
       [Variable] return a position [i-th] of variable called [x] that
       attached to matrix coefficient where [arity > 1]; if variable [x]
       does not occurs then this coefficient is [0] (the zero matrix);
       REMARK: [Variable] [i] has type positive integer starting from
       [1], list of variables in CoLoR starting from [0].
    
       [Polynomial_sum]/[Polynomial_product]: [v + \sum Mi * xi; i \in
       (1, k)]; where [v] is a vector, a polynomial function: [M2.x2 + v
       + M1.x1] is also a certificate.
       
       [Coefficient]: for each function symbol [F] of arity [n] from
       the signature, declare variables [F1, ..., Fn] for square
       matrices [(d x d)] (in the case of [Coefficient_matrix]); and a
       variable [f] for a (column) vector of [(d x 1)] (in the case of
       [Coefficient_vector)]. *)

  Implicit Arguments color_matrix_arcbz [dim].
  Implicit Arguments color_vector_arcbz [dim].

  Fixpoint color_poly_arcbz_matrixInt p mi :
    result (matrixInt_arcbz matrix_arcbz dim n) :=
    match p with
      | Polynomial_sum l =>
        let fix color_sum_mint acc l :=
          match l with
            | nil => Ok acc
            | p1 :: l' =>
              Match color_poly_arcbz_matrixInt p1 acc With Mi ===>
              color_sum_mint Mi l'
          end in color_sum_mint mi l
      | Polynomial_product
        (Polynomial_variable i ::
          Polynomial_coefficient (Coefficient_matrix m) :: nil)
      | Polynomial_product 
        (Polynomial_coefficient (Coefficient_matrix m) ::
          Polynomial_variable i :: nil) =>
        let i := (nat_of_P i) - 1 in
          Match color_matrix_arcbz m With M ===>
          match lt_dec i n with
            | left h => Ok ({|const_arcbz := (const_arcbz mi);
              args_arcbz := Vreplace (args_arcbz mi) h M|})
            | _ => Ko _ EpolyVarTooBig_matrix
          end
      | Polynomial_product
        (Polynomial_coefficient (Coefficient_vector v) :: nil) =>
        Match color_vector_arcbz v With v ===>
        Ok {| const_arcbz := v; args_arcbz := (args_arcbz mi)|}
      | Polynomial_product nil => Ok mi
    (* missing coef matrix and vector *)
    (*| Polynomial_coefficient (Coefficient_matrix m) =>
       Match color_matrix_arcbz m With M ==>
       Ok ({| const_arcbz := (const_arcbz mi);
       args_arcbz := Vconst M n |})
       | Polynomial_coefficient (Coefficient_vector v) =>
       Match color_vector_arcbz v With v ==>
       Ok {| const_arcbz := v; args_arcbz := (args_arcbz mi)|}*)
      | _ => Ko _ TPoly_MatrixInt_ArcBZ
    end.
  
  Definition color_matrix_arcbz_function f :=
    let mi :={|const_arcbz := zero_vec_arcbz dim;
      args_arcbz := Vconst (zero_matrix_arcbz dim dim) n|} in
    color_poly_arcbz_matrixInt f mi.

  (****************************************************************************)
  (** Polynomial function for matrix interpretation over arctic
     integer numbers: Formula of matrix interpretation: [f
     (v1,...,vn) = F1.v1 + ... + Fn.vn + f0; (1)] (where [v1,...,vn,
     f0]: are vectors).
     
     [Variable] return a position [i-th] of variable called [x] that
     attached to matrix coefficient where [arity > 1]; if variable
     [x] does not occurs then this coefficient is [0] (the zero
     matrix); REMARK: [Variable] [i] has type positive integer
     starting from [1], list of variables in CoLoR starting from
     [0].
     
     [Polynomial_sum]/[Polynomial_product]: [v + \sum Mi * xi; i \in
     (1, k)]; where [v] is a vector, a polynomial function: [M2.x2 + v
     + M1.x1] is also a certificate.
     
     [Coefficient]: for each function symbol [F] of arity [n] from
     the signature, declare variables [F1, ..., Fn] for square
     matrices [(d x d)] (in the case of [Coefficient_matrix]); and a
     variable [f] for a (column) vector of [(d x 1)] (in the case of
     [Coefficient_vector)]. *)

  Implicit Arguments color_matrix_trop [dim].
  Implicit Arguments color_vector_trop [dim].
  
  Fixpoint color_poly_trop_matrixInt p mi :
    result (matrixInt_trop matrix_trop dim n) :=
    match p with
      | Polynomial_sum l =>
        let fix color_sum_mint acc l :=
          match l with
            | nil => Ok acc
            | p1 :: l' =>
              Match color_poly_trop_matrixInt p1 acc With Mi ===>
              color_sum_mint Mi l'
          end in color_sum_mint mi l
      | Polynomial_product
        (Polynomial_variable i ::
          Polynomial_coefficient (Coefficient_matrix m) :: nil)
      | Polynomial_product 
        (Polynomial_coefficient (Coefficient_matrix m) ::
          Polynomial_variable i :: nil) =>
        let i := (nat_of_P i) - 1 in
          Match color_matrix_trop m With M ===>
          match lt_dec i n with
            | left h => Ok ({|const_trop := (const_trop mi);
              args_trop := Vreplace (args_trop mi) h M|})
            | _ => Ko _ EpolyVarTooBig_matrix
          end
      | Polynomial_product
        (Polynomial_coefficient (Coefficient_vector v) :: nil) =>
        Match color_vector_trop v With v ===>
        Ok {| const_trop := v; args_trop := (args_trop mi)|}
      | Polynomial_product nil => Ok mi
    (* missing coef matrix and vector *)
        (* | Polynomial_coefficient (Coefficient_matrix m) =>
          Match color_matrix_trop m With M ==>
           Ok ({|const_trop := (const_trop mi);
             args_trop := Vconst M n|})
        | Polynomial_coefficient (Coefficient_vector v) =>
          Match color_vector_trop v With v ==>
          Ok {| const_trop := v; args_trop := (args_trop mi)|}*)
      | _ => Ko _ TPoly_MatrixInt_Trop
    end.
  
  Definition color_matrix_trop_function f :=
    let mi :={|const_trop := zero_vec_trop dim;
      args_trop := Vconst (zero_matrix_trop dim dim) n|} in
    color_poly_trop_matrixInt f mi.

End poly.