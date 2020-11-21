open Pervasives;;
open Cpf0;;
open Vector;;
open SemiRing;;

(****************************************************************************)
(* Natural numbers *)

(* Print vector of type int in column format. *)

let rec print_vec_int_column = function 
  | Coq_nil -> print_string "nil \n"
  | Coq_cons (i, n, ts) -> 
    print_int i; print_string " (d = ";
    print_int n; print_string ")\n"; print_vec_int_column ts;;

(* Print vector of type int in row format. *)

let rec print_vec_int_row = function 
  | Coq_nil -> print_string "nil \n"
  | Coq_cons (i, n, ts) -> 
    print_int i; print_string " (d = ";
    print_int n; print_string ") "; print_vec_int_row ts;;

(* [vec_iter] function print a list of vector *)

let rec vec_iter f = function
  | Coq_nil -> ()
  | Coq_cons (a, _, l) -> f a; print_string " "; vec_iter f l;;

(* [print_matrix] print a matrix of type int with column format. *)

let print_matrix i = vec_iter (print_vec_int_column) i;;

(* [vec_iter_args] is a function that print an [arg] (square matrix)
   in matrix interpretation *)

let rec vec_iter_args f = function
  | Coq_nil -> ()
  | Coq_cons (a, _, l) -> f a; print_string "\n"; vec_iter_args f l;; 

(* [print_define_args] is a function that print a list of [args] (list
   of square matrix) in matrix interpretation over domain natural
   numbers. *)

let print_define_args args =
  vec_iter_args (vec_iter_args (print_vec_int_column)) args;;

(* [print_matrixInt] is a function that print [const] and [args] in
   matrix interpretation. *)

(*
let print_matrixInt p =
  let () = print_string "\n~~~~~~~~~~~~~~~~~~~~~\n";
    print_string "\n MatrixInt both const and args are: " in
  print_string "\n - const: \n";
  print_vec_int_column p.const;
  print_string "\n - args: \n" ;
  print_define_args p.args;;*)

(****************************************************************************)
(* Arctic natural numbers *)

(* [print_coqArcInt] function print a type ArcInt where MinusInf
   output as '-00' *)

let print_coqArcInt i = 
  match i with
    | Pos n -> print_string "Pos "; print_int n
    | MinusInf -> print_string "MinusInf";;

(* [print_vec_arc_column] is a function print vector of type arctic
   int in the column format. *)

let rec print_vec_arc_column = function 
  | Coq_nil -> print_string "nil \n"
  | Coq_cons (i, n, ts) -> print_coqArcInt i; print_string " (d= ";
    print_int n; print_string ")\n"; print_vec_arc_column ts;;

(* [print_matrix_arc] is a function print matrix of type arctic int in
   a column format. *)

let print_matrix_arc i = vec_iter (print_vec_arc_column) i;;

(* [print_define_args_arcnat] is a function that print a list of
   [args_arcnat] (list of square matrix) in matrix interpretation over
   domain arctic natural numbers. *)

let print_define_args_arcnat args =
  vec_iter_args (vec_iter_args (print_vec_arc_column)) args;;

(* [print_matrixArcNat] is a function that print [const_arcnat] and
   [args_arcnat] in matrix interpretation over arctic natural numbers *)
(*
let print_matrixArcNat p =
  let () = print_string "\n~~~~~~~~~~~~~~~~~~~~~\n";
    print_string "\n MatrixArcnat both const and args are: " in
  print_string "\n - const: \n";
  print_vec_arc_column p.const;
  print_string "\n - args: \n" ;
  print_define_args_arcnat p.args;;*)

(****************************************************************************)
(* Arctic integer numbers *)

let print_coqArcBZ i = 
  match i with
    | SemiRing.Fin n -> print_string "Fin "; print_int n
    | SemiRing.MinusInfBZ -> print_string "MinusInfBZ";;

(* [print_vec_arc_column] is a function print vector of type arctic
   int in the column format. *)

let rec print_vec_arcbz_column = function 
  | Coq_nil -> print_string "nil \n"
  | Coq_cons (i, n, ts) -> print_coqArcBZ i; print_string " (d= ";
    print_int n; print_string ")\n"; print_vec_arcbz_column ts;;

(* [print_matrix_arc] is a function print matrix of type arctic int in
   a column format. *)

let print_matrix_arcbz i = vec_iter (print_vec_arcbz_column) i;;

(* [print_define_args_arcnat] is a function that print a list of
   [args_arcnat] (list of square matrix) in matrix interpretation over
   domain arctic natural numbers. *)

let print_define_args_arcbz args =
  vec_iter_args (vec_iter_args (print_vec_arcbz_column)) args;;

(* [print_matrixArcNat] is a function that print [const_arcnat] and
   [args_arcnat] in matrix interpretation over arctic natural numbers *)

(*
let print_matrixArcBZ p =
  let () = print_string "\n~~~~~~~~~~~~~~~~~~~~~\n";
    print_string "\n MatrixArcBZ both const and args are: " in
  print_string "\n - const: \n";
  print_vec_arcbz_column p.const;
  print_string "\n - args: \n" ;
  print_define_args_arcbz p.args;;*)

(****************************************************************************)
(* Polynomial function *)

let print_poly (i, v) = 
  print_string " Coefficient: ";
  print_int i; print_string "\n monom n:  "; print_vec_int_column v;;

(* [print_list_poly] print a list of coefficient. *)

let rec print_list_poly l = 
  match l with
    | [] -> print_string " Empty list\n"
    | x :: l' -> print_poly x; print_string " :: "; print_list_poly l';;

(****************************************************************************)
(* Define value for polynomial function for polynomial interpretation over
   domain natural numbers *)

open Polynom2;;
open Peano;;
open BinPos;;
open Cpf_util;;
open Cpf2color;;

(** Coefficient *)

let define_poly_coefficient_3 =
  Polynomial_coefficient (Coefficient_number (Number_integer 3));;

let define_poly_coefficient_4 =
  Polynomial_coefficient (Coefficient_number (Number_integer 4));;

let poly_coef_poly n = function
  | Polynomial_coefficient c ->
    (match color_coef_N c with
   | Ok d -> Ok (pconst n d)
   | Ko e -> Ko e)
  | _ -> Ko TpolyMax;;

(*
let convert_poly_coef_poly n =
  match poly_coef_poly n define_poly_coefficient_3 with
    | Ok p -> p
    | Ko _ -> (pzero 0);;*)

(* where n = 1 *)
(*
let print_convert_poly_test_coef_poly_color =
   let () = print_string "\n---------------------\n";
     print_string "\n Print [Polynomial_coefficient]\n" in
   print_list_poly (convert_poly_coef_poly 1);;*)

(** Variable *)

let define_poly_variable_0 = Polynomial_variable 0;;
let define_poly_variable_1 = Polynomial_variable 1;;
let define_poly_variable_2 = Polynomial_variable 2;;

(* [Polynomial_variable] in [color_poly] in [poly.v] *)
(*
let poly_variable_poly n = function
  | Polynomial_variable x ->
    let x0 = minus (Pos.to_nat x) (succ 0) in
    if lt_dec x0 n then Ok (pxi n x0) else Ko EpolyVarTooBig
  | _ -> Ko TpolyMax;;*)

(* [color_poly] in the case of [Polynomial_variable]; convert
   polynomial Cpf0 type to [poly] of CoLoR type *)
(*
let convert_poly_variable_0_poly n =
  match poly_variable_poly n define_poly_variable_0 with
    | Ok p -> p
    | Ko _ -> (pzero 0);; (* If it is error it will return pzero *)*)

(*
let convert_poly_variable_1_poly n =
  match poly_variable_poly n define_poly_variable_1 with
    | Ok p -> p
    | Ko _ -> (pzero 0);;*)

(* where n = 1 *)
(*
let print_convert_poly_variable_0_poly_color =
  let () = print_string "\n---------------------\n";
    print_string "\n Print [Polynomial_variable] variable 0: " in
  print_list_poly (convert_poly_variable_0_poly 1);;*)

(* where n = 1 *)
(*
let print_convert_poly_variable_1_poly_color =
  let () = print_string "\n---------------------\n";
    print_string "\n Print [Polynomial_variable] variable 1: \n" in
  print_list_poly (convert_poly_variable_1_poly 1);;*)

(* Polynomial sum *)
(* list p = 3 :: 4 :: nil *)
(*
let define_poly_list_sum =
  Polynomial_sum (define_poly_coefficient_3 :: define_poly_coefficient_4 :: []);;

(* [Polynomial_sum] in [poly.v] *)

let poly_sum_poly n = function
  | Polynomial_sum l ->
  let rec color_poly_sum acc = function
    | [] -> Ok acc
    | p0 :: l' ->
      (match color_poly n p0 with
	| Ok p1 -> color_poly_sum (pplus n p1 acc) l'
	| Ko e -> Ko e)
  in color_poly_sum (pzero n) l
    | _ -> Ko TpolyMax;;

(* Convert [poly_sum_poly] into poly of Color type *)

let convert_poly_sum_poly_color n =
  match poly_sum_poly n define_poly_list_sum with
    | Ok p -> p
    | Ko _ -> (pzero 0);;

let print_convert_poly_test_sum_poly_color =
   let () = print_string "\n---------------------\n";
     print_string "\n Print [Polynomial_sum] where coef = 4 + 3: \n" in
   print_list_poly (convert_poly_sum_poly_color 1);;

(* Polynomial multiplication *)
(* list p = 3 :: 4 :: nil *)

let define_poly_list_prod =
  Polynomial_product (define_poly_coefficient_3 :: define_poly_coefficient_4 :: []);;

(* [Polynomial_product] in [poly.v] *)

let poly_prod_poly n = function
  | Polynomial_product l ->
  let rec color_poly_prod acc = function
    | [] -> Ok acc
    | p0 :: l' ->
      (match color_poly n p0 with
	| Ok p1 -> color_poly_prod (pmult n p1 acc) l'
	| Ko e -> Ko e)
  in color_poly_prod (pconst n 1) l
  | _ -> Ko TpolyMax;;

(* convert [poly_prod_poly] into poly of Color type *)

let convert_poly_prod_poly n =
  match poly_prod_poly n define_poly_list_prod with
    | Ok p -> p
    | Ko _ -> (pzero 0);; (* when it is error return pzero *)

let print_convert_poly_prod_poly_color =
   let () = print_string "\n---------------------\n";
     print_string "\n Print [Polynomial_product] where coef = 4 * 3: \n" in
   print_list_poly (convert_poly_prod_poly 1);;

(* Test the function [color_poly] in [poly.v] *)

let define_poly = Polynomial_sum
  (define_poly_coefficient_3 ::
     (Polynomial_product
	(define_poly_coefficient_4 :: define_poly_variable_1 :: [])) :: []);;

let convert_color_poly n =
   match color_poly n define_poly with
    | Ok p -> p
    | Ko _ -> (pzero 0);;

let print_color_poly = 
  let () = print_string "\n---------------------\n";
    print_string "\n [color_poly]: \n" in
  print_list_poly (convert_color_poly 1);;

(****************************************************************************)
(* Define value for polynomial function for matrix interpretation over
   domain natural numbers *)

(* Coefficient *)

let define_coef0 = Coefficient_number (Number_integer 0);;
let define_coef1 = Coefficient_number (Number_integer 1);;
let define_coef2 = Coefficient_number (Number_integer 2);;

(* Vector *)
(* v = 0 :: 1 :: nil *)

let define_coef_vector01 = Polynomial_coefficient
  (Coefficient_vector (Vector_vector (define_coef0 :: define_coef1 :: [])));;

(* Matrix *)
(* m = (2 :: 2 :: nil) :: (0 :: 0 :: nil) :: nil *)

let define_matrix_coef2200 = Polynomial_coefficient
  (Coefficient_matrix (Matrix_matrix 
			 ((define_coef2 :: define_coef2 :: []) :: 
			     (define_coef0:: define_coef0 :: []) :: [])));;		   

let define_matrix_coef2201 = Polynomial_coefficient
  (Coefficient_matrix (Matrix_matrix 
			 ((define_coef2 :: define_coef2 :: []) :: 
			     (define_coef1:: define_coef1 :: []) :: [])));;

let matrix_coef2200 = Matrix_matrix 
  ((define_coef2 :: define_coef2 :: []) :: 
      (define_coef0:: define_coef0 :: []) :: []);;		   

(* Polynomial *)
(* p (x1) = |0| + |2 2|.x1
            |1|   |0 0| *)

let define_poly_sum_prod =
  Polynomial_sum (define_matrix_coef2200 :: Polynomial_product
		     (define_matrix_coef2201 :: define_poly_variable_1 :: []) :: []);;

let define_poly_matrix =
  Polynomial_sum (Polynomial_product
		    (define_matrix_coef2200 :: define_poly_variable_1 :: []) :: []);;

(* Test function [color_matrix_function] in [color_matrix_nat.v]; dim
   = 2, n = 1 *)

(* Test [color_matrix_function] with poly_sum and poly_prod both coef
   vector and matrix. *)

let print_define_color_matrix_function =
  match color_matrix_function 2 1 define_poly_sum_prod with
    | Ok p -> print_string "\n---------------------\n";
      print_string "\n Print [color_matrix_function]: \n";
      print_matrixInt p
    | Ko _ -> print_string "Error [color_matrix_function]!";;

(* Test [color_matrix_function] alone with poly_sum and coef_matrix *)

let print_define_color_matrix_function2 =
  match color_matrix_function 2 1 define_poly_matrix with
    | Ok p -> print_string "\n---------------------\n";
      print_string "\n Print [color_matrix_function] with matrix : \n";
      print_matrixInt p
    | Ko _ -> print_string "Error [color_matrix_function] with matrix1!";;

(* Test [color_matrix_function] alone with coef_matrix *)

let print_define_color_matrix_function3 =
  match color_matrix_function 2 1 define_matrix_coef2200 with
    | Ok p -> print_string "\n---------------------\n";
      print_string "\n Print [color_matrix_function] with matrix : \n";
      print_matrixInt p
    | Ko _ -> print_string "\nError [color_matrix_function] with matrix!";;

open VecUtil;;
open NatUtil;;
open Matrix2;;
open Cpf2color_vector;;

(* Test [bgt_nat] in [type_matrix_naturals]  *)
let is_bgt_nat =
  match color_matrix 2 matrix_coef2200 with
    | Ok m ->
      print_string "\n---------------------\n";
      print_string "bgt_nat: ";
      let bm  = bVforall (fun _ -> bgt_nat (get_elem 2 2 m 0 0)0) 1 m in
      print_string (string_of_bool bm);
      print_string "\n---------------------\n"
    | _ -> print_string " Error [is_bgt_nat] ";;


(****************************************************************************)
(* Define value for polynomial function for matrix interpretation over
   domain Arctic natural numbers *)

(* Coefficient *)
(* MinusInf *)

let define_coef_minusInf = Coefficient_minusInfinity;;

(* Pos 1 *)

let define_coef_Pos1 = Coefficient_number (Number_integer 1);;

(* Negative *)

let define_coef_negative = Coefficient_number (Number_integer (-1));;

(* Test function [color_coef_arcnat] in [color_matrix_arc_nat.v],
   print minusInf *)

let print_color_coef_arcnat_minusInf =
  match color_coef_arcnat define_coef_minusInf with
    | Ok i -> print_string "\n---------------------\n";
      print_string "\n Print [color_coef_arcnat] coefficient MinusInf: ";
      print_coqArcInt i
    | Ko _ -> print_string "Error [color_coef_arcnat]!";;

let print_color_coef_arcnat_Pos1 =
  match color_coef_arcnat define_coef_Pos1 with
    | Ok i -> print_string "\n---------------------\n";
      print_string "\n Print [color_coef_arcnat] coefficient (Pos 1): ";
      print_coqArcInt i; print_newline()
    | Ko _ -> print_string "Error [color_coef_arcnat]!\n";;

let print_color_coef_arcnat_negative =
  match color_coef_arcnat define_coef_negative with
    | Ok i -> print_string "\n---------------------\n";
      print_string "\n Print [color_coef_arcnat] coefficient Negative: ";
      print_coqArcInt i
    | Ko _ -> print_string "\n---------------------\n";
      print_string "Error [color_coef_arcnat]!";;

(* Vector *)
(* v = minusInf :: minusInf :: minusInf :: nil *)

let define_coef_vector =
  Vector_vector(Coefficient_minusInfinity
		:: Coefficient_minusInfinity :: Coefficient_minusInfinity :: []);;

(* v = minusInf *)

let define_vector_minus = Vector_vector (Coefficient_minusInfinity :: []);;

(* Matrix *)
(* m = (1::0::0::nil)::(m :: m :: m:: nil) :: (m :: m :: m::nil) :: nil
   | 1 0 0 |
   | m m m |
   | m m m | *)

let define_coef_list_arc_1_0_0 =
Coefficient_number (Number_integer 1) :: Coefficient_number (Number_integer 0)
 :: Coefficient_number (Number_integer 0) :: [];;

let define_coef_list_arc_minus_minus =
Coefficient_minusInfinity :: Coefficient_minusInfinity :: Coefficient_minusInfinity :: [];;

let list_list_matrix = define_coef_list_arc_1_0_0 :: define_coef_list_arc_minus_minus ::
  define_coef_list_arc_minus_minus :: [];;

let define_matrix_arc = Matrix_matrix list_list_matrix;;

(* Define matrix with dimension = 1 *)

let define_list_minus = Coefficient_minusInfinity :: [];;
let define_matrix_dim1 = Matrix_matrix (define_list_minus :: []);;

(* Test [color_vector_arcnat] in [color_matrix_arctic_nat.v], dim = 3 *)

let print_color_vector_arcnat =
  match color_vector_arcnat 3 define_coef_vector with
    | Ok i ->
      let () = print_string "\n---------------------\n";
	print_string "v = minusInf :: minusInf :: minusInf :: nil\n";
	print_string "Print [color_vector_arcnat]: \n" in
      print_vec_arc_column i;
      print_string "---------------------\n"
    | Ko _ -> print_string " Error [color_vector_arcnat]!\n";;

(* Test [color_vector_arcnat] when dim = 1 *)

let print_color_vector_arcnat_dim1 =
  match color_vector_arcnat 1 define_vector_minus with
    | Ok i ->
      let () = print_string "\n---------------------\n";
	print_string "v = minusInf :: nil\n";
	print_string "Print [color_vector_arcnat] when dim=1: \n" in
      print_vec_arc_column i;
      print_string "---------------------\n"
    | Ko _ -> print_string " Error [color_vector_arcnat]!\n";;


(* Test [color_matrix_arcnat] in [color_matrix_arctic_nat.v], dim = 3 *)

let print_color_matrix_arcnat =
  match color_matrix_arcnat 3 define_matrix_arc with
    | Ok i ->
      let () = print_string "\n---------------------\n";
	print_string "\n m = [1::0::0] :: [MinusInf :: MinusInf :: MinusInf]\
          :: [MinusInf :: MinusInf :: MinusInf]: \n";
	print_string "Print [color_matrix_arcnat]: \n"
      in
      print_matrix_arc i;
      print_string "---------------------\n"
    | Ko _ -> print_string " Error [color_matrix_arcnat]!\n";;

(* Test [color_matrix_arcnat] when dim = 1 *)

let print_color_matrix_arcnat_dim1 =
  match color_matrix_arcnat 1 define_matrix_dim1 with
    | Ok i ->
      let () = print_string "\n---------------------\n";
	print_string "\n m = (MinusInf :: nil) :: nil \n";
	print_string "Print [color_matrix_arcnat] when dim = 1: \n"
      in
      print_matrix_arc i;
      print_string "---------------------\n"
    | Ko _ -> print_string " Error [color_matrix_arcnat] when dim = 1!\n";;

(* Define [polynomial] *)
(* p (x1) = | 0 | + |1 m|.x1
            | m |   |0 m|

*)

(* Vector v = (0, m) *)

let define_vector_0m = Polynomial_coefficient (Coefficient_vector (
  Vector_vector (Coefficient_number (Number_integer 0) :: Coefficient_minusInfinity :: [])));;

(* Vector v = (1, m) *)

let define_vector_1m = Polynomial_coefficient (Coefficient_vector (
  Vector_vector (Coefficient_number (Number_integer 1) :: Coefficient_minusInfinity :: [])));;

(* Matrix m = (m :: m :: nil) :: (0 :: m :: nil) :: nil) *)

let define_list1 = Coefficient_minusInfinity :: Coefficient_minusInfinity :: [];;
let define_list2 = Coefficient_number (Number_integer 0) :: Coefficient_minusInfinity :: [];;

let define_matrix_1m = Polynomial_coefficient (
  (Coefficient_matrix (Matrix_matrix (define_list1 :: define_list2 :: []))));;

(* Matrix m = (m :: m :: nil) :: (0 :: m :: nil) :: nil) *)

let define_list_m1 = Coefficient_minusInfinity :: Coefficient_minusInfinity :: [];;
let define_list_m2 = Coefficient_number (Number_integer 0) :: Coefficient_minusInfinity :: [];;

let define_matrix_2m = Polynomial_coefficient (
  (Coefficient_matrix (Matrix_matrix (define_list_m1 :: define_list_m2 :: []))));;

let define_poly_matrix_arcnat = Polynomial_sum (
  Polynomial_product (define_vector_0m :: []) ::
    Polynomial_product (define_matrix_1m :: define_poly_variable_1 :: []) :: []);;

(* |1| + |m m|. x1
   |m|   |0 m|
*)
let define_poly_matrix_arcnat2 = Polynomial_sum (
  Polynomial_product (define_vector_1m :: []) ::
    Polynomial_product (define_matrix_2m :: define_poly_variable_1 :: []) :: []);;

let print_color_matrix_arcnat_function =
  match color_matrix_arcnat_function 2 1 define_poly_matrix_arcnat with
    | Ok p -> print_string "\n---------------------\n";
      print_string "\n Print [color_matrix_arcnat_function]: \n";
      print_matrixArcNat p
    | Ko _ -> print_string "Error [color_matrix_arcnat_function]!\n";;

(* Test [color_matrix_arcnat_function], dim = 2, n = 1 *)
(*
  |m| + |m|.x1 + |3|.x2
*)
 
let define_vector_m = Polynomial_coefficient (Coefficient_vector (Vector_vector (Coefficient_minusInfinity :: [])));;

let define_matrix_m = Polynomial_coefficient
  (Coefficient_matrix (Matrix_matrix ((Coefficient_minusInfinity :: []) :: [])));;

let define_matrix_3 = Polynomial_coefficient
  (Coefficient_matrix (Matrix_matrix ((Coefficient_number (Number_integer 3) :: []) :: [])));;

let define_poly_matrix_arcnat_dim1 = Polynomial_sum (
  Polynomial_product (define_vector_m :: []) ::
    Polynomial_product (define_matrix_3 :: define_poly_variable_1 :: []) :: []);;

(*    Polynomial_product (define_matrix_3 :: define_poly_variable_2 :: []) :: []);;*)

let print_color_matrix_arcnat_function_dim1 =
  match color_matrix_arcnat_function 1 1 define_poly_matrix_arcnat_dim1 with
    | Ok p -> print_string "\n---------------------\n";
      print_string "\n Print [color_matrix_arcnat_function] dim 1: \n";
      print_matrixArcNat p
    | Ko _ -> print_string "Error [color_matrix_arcnat_function] dim 1!\n";;

(* Test [bmint_arc_gt] *)
(* p1(x1) = |1| + |m m|.x1
            |m|   |0 m|

   p2(x1) = |0| + |m m|.x1
            |m|   |0 m| *)

let print_bmint_arc_gt =
  match color_matrix_arcnat_function 2 1 define_poly_matrix_arcnat2,
    color_matrix_arcnat_function 2 1 define_poly_matrix_arcnat with
      | Ok p1, Ok p2 ->
	(match bmint_arc_gt 2 1 p1 p2 with
	  | true -> print_string "[bmint_arc_gt]: ";
	    print_string "true"
	  | false ->
	    print_string "[bmint_arc_gt]: ";
	    print_string "false")
      | _, _ -> print_string "Error [bmint_arc_gt]!";;
	
(* Test the condition [is_finite], dim = 3, n = 1 *)

open VecUtil;;
open SemiRing2;;
open Matrix2;;

(* v = minusInf :: minusInf :: minusInf :: nil *)
(* m = (1::0::0::nil)::(m :: m :: m:: nil) :: (m :: m :: m::nil) :: nil
   | 1 0 0 |
   | m m m |
   | m m m | *)

let is_finite_of_vector_and_matrix =
  match color_vector_arcnat 3 define_coef_vector,
    color_matrix_arcnat 3 define_matrix_arc with
    | Ok v, Ok m ->
      print_string "\n---------------------\n";
      print_string "Is vector and matrix finite: ";
      let bm  = bVexists (fun _ -> is_finite (get_elem_arcnat 3 3 m 0 0)) 1 m in
      let bv = 	is_finite (coq_Vnth 3 v 0) in
      print_string (string_of_bool ((||) bm bv));
      print_string "\n---------------------\n"
    | _, _ -> print_string " Error [is_finite] vector and matrix";;

(* Test [is_finite] with dim = 1, n = 1, matrix = |-00|, vector = |-00| *)

let is_finite_of_vector_and_matrix_dim1 =
  match color_vector_arcnat 1 define_vector_minus,
    color_matrix_arcnat 1 define_matrix_dim1 with
    | Ok v, Ok m ->
      print_string "\n---------------------\n";
      print_string "Is vector and matrix finite when dim = 1: ";
      let bm  = bVexists (fun _ -> is_finite (get_elem_arcnat 1 1 m 0 0)) 1 m in
      let bv = 	is_finite (coq_Vnth 1 v 0) in
      print_string (string_of_bool ((||) bm bv));
      print_string "\n\n"
    | _, _ -> print_string " Error [is_finite] vector and matrix when dim = 1";
      print_string "\n---------------------\n";;

(* Test [bgt_arc] in [color_matrix_arctic_nat.v] *)
(* true case *)

let print_bgt_arc =
  match bgt_arc (Pos 1) (MinusInf) with
    | true -> print_string "Pos 1 >_arc MinusInf: "; print_string "true";
      print_newline()
    | false -> print_string "Pos 1 >_arc MinusInf: "; print_string "false";
      print_newline();;

let print_bgtx2 =
  match bgtx (MinusInf) (MinusInf) with
    | true -> print_string "MinusInf >> MinusInf: "; print_string "true";
      print_newline()
    | false -> print_string "MinusInf >> MinusInf: "; print_string "false";
      print_newline();;

(* false case *)

let print_bgt_arc1 =
  match bgt_arc (MinusInf) (Pos 1) with
    | true -> print_string "MinusInf >_arc Pos 1: "; print_string "true";
      print_newline()
    | false -> print_string "MinusInf >_arc Pos 1: "; print_string "false";
      print_newline();;

(* Test [bge_arc] in [color_matrix_arctic_nat.v] *)

let print_bge_arc =
  match bge_arc (Pos 1) (MinusInf) with
    | true -> print_string "Pos 1 >=_arc MinusInf: "; print_string "true";
      print_newline()
    | false -> print_string "Pos 1 >=_arc MinusInf: "; print_string "false";
      print_newline();;

(* false case *)

let print_bge_arc2 =
  match bge_arc (MinusInf) (Pos 1) with
    | true -> print_string "MinusInf >=_arc Pos 1: "; print_string "true";
      print_newline()
    | false -> print_string "MinusInf >=_arc Pos 1: "; print_string "false";
      print_newline();;

(* Test [bmint_arc_ge] *)


(****************************************************************************)
(* Define value for polynomial function for matrix interpretation over
   domain Arctic integer numbers *)

(* v = -1 :: minusInf :: 1 :: nil *)

let define_coef_vector_arcbz = Vector_vector(
  Coefficient_number (Number_integer (-1)) :: Coefficient_minusInfinity ::
    Coefficient_number (Number_integer 1) :: []);;

(* m = (0 :: 0 :: -1) :: (m :: 0 :: m) :: (-1 :: -1 :: 0) :: nil
   | 0   0   -1 |
   | m   0   m  |
   | -1  -1  0  | *)

let define_list1_arcbz = Coefficient_number (Number_integer 0) ::
  Coefficient_number (Number_integer 0) :: Coefficient_number (Number_integer (-1)) :: [];;

let define_list2_arcbz = Coefficient_minusInfinity :: Coefficient_number (Number_integer 0) ::
  Coefficient_minusInfinity :: [];;

let define_list3_arcbz = Coefficient_number (Number_integer (-1))
  :: Coefficient_number (Number_integer (-1)) :: Coefficient_number (Number_integer 0) :: [];;

let list_list_arcbz = define_list1_arcbz :: define_list2_arcbz :: define_list3_arcbz :: [];;

let define_coef_matrix_arcbz = Matrix_matrix list_list_arcbz;;

let define_coef_vector_true = Vector_vector define_list1_arcbz;;

(* Test [color_coef_arcbz] in [color_matrix_arctic_below_zero.v] *)

let print_color_coef_arcbz =
  match color_coef_arcbz define_coef_negative with
    | Ok i -> print_string  "\n---------------------\n";
      print_string "\n Print [color_coef_arcbz] coefficient negative: ";
      print_coqArcBZ i
    | Ko _ -> print_string "Error [color_coef_arcbz]!";;

(* Test [color_vector_arcbz] *)

let print_color_vector_arcbz =
  match color_vector_arcbz 3 define_coef_vector_arcbz with
    | Ok i ->
      let () = print_string "\n---------------------\n";
	print_string "v = -1 :: minusInf :: 1 :: nil\n";
	print_string "Print [color_vector_arcbz]: \n" in
      print_vec_arcbz_column i;
      print_string "---------------------\n"
    | Ko _ -> print_string " Error [color_vector_arcbz]!\n";;

(* Test [color_matrix_arcbz] *)

let print_color_matrix_arcbz =
  match color_matrix_arcbz 3 define_coef_matrix_arcbz with
    |  Ok i ->
      let () = print_string "\n---------------------\n";
	print_string "\n m = [0::0::-1] :: [MinusInf :: 0 :: MinusInf]\
          :: [-1 :: -1 :: 0]: \n";
	print_string "Print [color_matrix_arcbz]: \n"
      in print_matrix_arcbz i;
      print_string "---------------------\n"
    | Ko _ -> print_string " Error [color_matrix_arcnat]!\n";;

(* p (x1) =
   |-1 | + | 0   0   -1 |
   | m |   | m   0   m  |
   | 1 |   | -1  -1  0  | *)

let poly_vector = Polynomial_coefficient (Coefficient_vector define_coef_vector_arcbz);;

let poly_matrix = Polynomial_coefficient (Coefficient_matrix (
      define_coef_matrix_arcbz));;

let define_poly_matrix_arcbz = Polynomial_sum (
  Polynomial_product (poly_vector :: []) ::
    Polynomial_product ( poly_matrix :: define_poly_variable_1 :: []) :: []);;

(* Test [color_matrix_arcbz_function] *)

let print_color_matrix_arcbz_function =
  match color_matrix_arcbz_function 3 1 define_poly_matrix_arcbz with
    | Ok p -> print_string "\n---------------------\n";
      print_string "\n Print [color_matrix_arcbz_function]: \n";
      print_matrixArcBZ p
    | Ko _ -> print_string "Error [color_matrix_arcbz_function]!";;
  
open OrdSemiRing2;;

(* Test [is_above] *)

let is_above_zero_of_vector =
  match color_vector_arcbz 3 define_coef_vector_arcbz with
    | Ok v ->
      print_string "\n---------------------\n";
      print_string "Is vector above zero: ";
      let is_above = is_above_zero (coq_Vnth 3 v 0) in
      print_string (string_of_bool is_above);
      print_string "\n---------------------\n"
    | _ -> print_string " Error [is_above] vector";;

let is_above_zero_of_vector_true =
  match color_vector_arcbz 3 define_coef_vector_true with
    | Ok v ->
      print_string "\n---------------------\n";
      print_string "Is vector above zero: ";
      let is_above = is_above_zero (coq_Vnth 3 v 0) in
      print_string (string_of_bool is_above);
      print_string "\n---------------------\n"
    | _ -> print_string " Error [is_above] vector";;
*)

(****************************************************************************)
(* [vector_of_list] in [cpf2color.v] *)

(*
let define_list = 1 :: 0 :: 0 :: 0 :: [];;

let print_length =
  print_string "\n- Length of the list: ";
  print_int (length define_list); print_newline();;

(* Test the function [vector_of_list] *)

let print_vector_of_list =
  match vector_of_list define_list 4 with
    | Ok l -> print_string "- Print [vector_of_list]:";
      print_vec_int_column l
    | _ -> print_string " Error of vector_of_list! \n";;

(* Test the function [int_to_nat] in [cpf2color.v] *)

let print_int_nat i =
  match int_to_nat i with
    | Ok i ->
      let () = print_string "\n - Print [int_to_nat]: \n" in printf "%i " i
    | Ko _ -> print_string "error";;

(* Test the function [list_int_to_list_nat]. *)

let define_list2 = 0 :: 0 :: 1 :: 0 :: [];;

let print_list_int_to_nat =
  match list_int_to_list_nat define_list2 with
    | Ok l -> print_string "- Print [list_int_to_list_nat]: ";
      List.iter print_int l
    | _ -> print_string " Error of list_int_to_list_nat! \n";;

(* [list_int_to_list_map] testing a list using [map] *)
let list_int_to_list_nat l =
  Cpf_util.map int_to_nat l;;

let print_list_int_to_nat' =
  match list_int_to_list_nat define_list2 with
    | Ok l -> print_string "- Print [list_int_to_list_nat]: ";
      List.iter print_int l
    | _ -> print_string " Error of list_int_to_list_nat! \n";;


(* TEST: [list_int_to_list_map_rev] by using [map_rev] *)
let list_int_to_list_nat_rev l =
  map_rev int_to_nat l;;

let print_list_int_to_nat_rev =
  match list_int_to_list_nat_rev define_list2 with
    | Ok l -> print_string "- Print [list_int_to_list_nat_rev]: ";
      List.iter print_int l
    | _ -> print_string " Error of list_int_to_list_nat! \n";;

(* Function testing convert integer number to an ArcticDom. *)
let int_to_arcnat i0 =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (Pos 0))
        (fun i1 -> (Pos (Pos.to_nat i1)))
        (fun _i1 -> MinusInf)
        i0;;

let map_int_to_arcnat l = map int_to_arcnat l;;

let print_int_to_arcnat1 = print_string "print negative: ";
  print_coqArcInt (int_to_arcnat (-1)); print_newline();;

let print_int_to_arcnat2 = print_string "print 1:";
  print_coqArcInt (int_to_arcnat (1)); print_newline();;

let print_int_to_arcnat3 =  print_string "print 0:"; 
  print_coqArcInt (int_to_arcnat 0); print_newline();;

(* Test [vec_of_list] in [VecUtil.v] *)

let print_define_vec_of_list = 
  print_string "\n- Print vec_of_list\n:";
  print_vec_int_column (VecUtil.vec_of_list define_list2);;

(* Test [map] function in [cpf2color.v] *)

let print_map f = 
  match map f define_list with
    | l -> List.iter print_int l;;*)

(* Test [split_list] in [cpf2color.v] *)

let define_list_tuple = (((1, 0), 0), 0) :: (((2, 0), 0), 0) :: [];;

let print_split_list =
  print_string "\nPrint [split_list]: ";
  List.iter print_int (split_list define_list_tuple); print_newline();;

(***************************************************)
(* Pmult_nat *)

let print_pos_to_nat  = print_string " positive to nat: ";
  print_int (Pos.to_nat 1); print_newline();;

let print_pos_to_nat_minus = print_string "postive to nat minus: ";
  print_int (minus (Pos.to_nat 1) (succ 0)); print_newline();;

let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      op a (iter_op op p0 (op a a)))
      (fun p0 ->
      iter_op op p0 (op a a))
      (fun _ ->
      a)
      p;;

let to_nat x = iter_op plus x (succ 0);; (* succ 0 = 1 *)

let print_my_to_nat = print_string "my to nat: ";
  print_int (to_nat (succ 0)); print_newline();;

(*********************************************************)
(* Print xsd list *)



(*********************************************************)
(* TEST [nats_incr_lt] in ListUtil.v *)
(*
open Prf_of_newcpf;;

let nat_lt =
  let n = nats_incr_lt 4 in
  print_string "print nats_incr_lt of n=4 : ";
  List.iter print_int n;;

let p = 1 :: 2 :: 3 :: 4 :: [];;

let print_color_position =
  print_string "\n print color_positive 3: \n";
  print_int (color_positiveInteger 3);;

let list_position_nat2 p =
  let p2 = position p in
  if p2 = nats_incr_lt 4 then []
  else p2;;

let list_position_nat3 p =
  let p2 = position p in
  if equiv beq_nat p2 (nats_incr_lt 3) then []
  else p2;;

let print_list_position_nat3 =
  print_string "Print list_position_nat3: \n";
  List.iter print_int (list_position_nat3 p);;


let print_list_position_nat2 =
  print_string "\nPrint list_position_nat2: \n";
  List.iter print_int (list_position_nat2 p);;

let print_list_position_nat =
  let n = list_position_nat p in
  print_string "\nprint list position nat: 1 2 3 4: \n";
  List.iter print_int n;;

let nat_incr ps n = 
  if equiv beq_nat (list_position_nat ps)(nats_incr_lt n)
  then []
  else list_position_nat ps;;

let print_nat_incr =
  let n = nat_incr p 4 in
  print_string "print_nat_incr: \n";
  List.iter print_int n;;*)


(***************************************************)
(* Test [list position] in result type. *)

let l1 = 1 :: 2 :: 3 :: 4 :: [];;
let l2 = 1 :: [];;

(*
let print_list_color_position  = 
  match color_result_position p2 with
    | Ok p -> print_string "\n list position with result type :";
      List.iter print_int p;
      print_string "\nList rev of p2: ";
      List.iter print_int (List.rev p)
    | Ko _ -> print_string "";;*)

let fix def c =
  List.length l1 :: def c;;

let print_test_length =
  let l = List.length l2 in
  print_string "\nthe length of this list is: ";
  print_int l;  print_string "\n"


(*************************************************************)
(* Test the function map in [cpf_util.ml] *)


let print_list l =
  match l with
    | [] -> ()
    | x :: l -> print_int x; List.iter print_int l; print_string "\n"

let print_list_result l =
  match l with
    | Cpf_util.Ok l -> print_string " "; List.iter print_int l; print_string "\n"
    | Cpf_util.Ko _ -> ()

let map_l = Cpf_util.map (fun x -> Cpf_util.Ok (x*2)) l1;;

let print_map_l = print_string "Result of [1,2,3,4]: "; print_list_result map_l;;

let map_list_l = List.map (fun x -> (x*2)) l1;;

let print_map_list = print_string "Result of [1,2,3,4]: "; print_list_result map_l;;
 
let map_rev_l = Cpf_util.map_rev (fun x -> Cpf_util.Ok (x*2)) l1;;

let print_map_rev_result_l = print_string "Result of [1,2,3,4] reverse: ";
  print_list_result map_rev_l;;

let map_rev_list = List.rev (map_list_l);;

let print_map_rev_l = print_string "Result of [1,2,3,4]: "; print_list map_rev_list;;
