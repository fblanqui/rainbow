(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2011-04-06

* Translate CPF type into CoLoR type.

*)


Set Implicit Arguments.

Require Import ATrs SN ZArith EqUtil String List ListDec ListForall
  ListUtil ZUtil LogicUtil BoolUtil ARelation NatUtil ADuplicateSymb
  AMorphism cpf cpf_ind error_monad VecUtil Polynom2 OrdSemiRing2
  SemiRing APolyInt2 APolyInt_MA2 PositivePolynom2 MonotonePolynom2
  ARedPair2 AMatrixBasedInt2 Matrix2 VecUtil VecArith2 AProj Equality.

(***********************************************************************)
(** ** Computing the arity in initial signature for all symbol
corresponding to a certification problem by examining rules in a list
of funtion symbol. *)

Fixpoint arity_in_term t f :=
  match t with
    | Term_var _       => None
    | Term_funapp g ts =>
      if beq_symbol f g
      then Some (List.length ts)
      else
        let fix arity_in_list_term ts :=
          match ts with
            | nil      => None
            | t :: ts' =>
              match arity_in_term t f with
                | None => arity_in_list_term ts'
                | o    => o
              end
          end
        in arity_in_list_term ts
  end.

Fixpoint arity_in_list A (F : A -> symbol -> option nat) xs f :=
  match xs with
    | nil      => None
    | x :: xs' =>
      match F x f with
        | None => arity_in_list F xs' f
        | o    => o
      end
  end.

Lemma arity_in_term_fun : forall f g ts,
  arity_in_term (Term_funapp g ts) f =
  if   beq_symbol f g
  then Some (List.length ts)
  else arity_in_list arity_in_term ts f.

Proof.
intros; simpl. destruct (beq_symbol f g). refl.
induction ts; simpl. refl. 
rewrite IHts. refl.
Qed.

Definition arity_in_rule (r:rule) f :=
match r with
  | (a, b)   =>
    match arity_in_term a f with
      | None => arity_in_term b f
      | o    => o
    end
end.

Definition arity_in_rules (rs: rules) f :=
  arity_in_list arity_in_rule rs f.

Definition arity_in_trs (rs: trs) f := arity_in_rules rs f.

Definition arity_in_dps (rs: dps) f := arity_in_rules rs f.

(* Search the arity in symbol of trsInput. *)

Definition arity_in_trsInput (p: trsInput) f :=
  match p with
    | (t, _, _, _)  => arity_in_trs t f
  end.

(* Search the arity in symbol of dpInput. *)

Definition arity_in_dpInput (p: dpInput) f :=
  match p with
    | (t, d, _, _) =>
      match arity_in_trs t f with
        | None     => arity_in_dps d f
        | o        => o
      end
  end.

(* Only search in the symbol of trsInput and dpInput, others input are
not support yet. *)

Definition arity_in_input i f :=
  match i with
    | Input_trsInput x => arity_in_trsInput x f
    | Input_dpInput x  => arity_in_dpInput x f
    | _                => None
  end.

(* Return the arity is zero (0) when there is none arity in the
symbol. *)

Definition arity_in_pb_input (i : input) f : nat :=
  match arity_in_input i f with
    | Some k => k
    | None   => O
  end.

Definition arity_in_pb (c: certificationProblem) :=
  match c with
    | (i, _, _, _) => arity_in_pb_input i
  end.

(*KEEP?
Definition sig_of_pb c := mkSignature (arity_in_pb c) beq_symbol_ok.*)

Definition Sig a := mkSignature a beq_symbol_ok.
Definition equiv_rules a := equiv (@ATrs.beq_rule (Sig a)).
Definition aterm a  := ATerm.term (Sig a).
Definition arule a  := ATrs.rule (Sig a).
Definition arules a := ATrs.rules (Sig a).
Definition abrule a := @ATrs.brule (Sig a).

Implicit Arguments abrule [a].

(**************************************************************************)

Section Top.

  (* Assume the arity of function symbol. *)

  Variable arity : symbol -> nat.
  Notation Sig   := (Sig arity).

  (* Translate a variable of type string into nat. *)

  Variable nat_of_string : string -> nat.

  Notation aterm  := (aterm arity).
  Notation arule  := (arule arity).
  Notation arules := (arules arity).
  Notation abrule := (abrule arity). 

  Implicit Type R : arules.

  (***********************************************************************)  
  (** Translate CPF [term] into CoLoR term. *)
  (***********************************************************************)

  Definition color_term : term -> result aterm.
  
  Proof.
    apply new_term_rect with
    (Q := fun ts => { o : result (list aterm) |
                      forall l, o = Ok l -> length l = length ts }).
    (* var *)
    intro s. exact (Ok (@Var Sig (nat_of_string s))).
    (* fun *)
    intros f ts [[ts'|] h'].
    (* Ok: all arguments could be translated *)
    case (eq_nat_dec (arity f) (length ts)); intro h.
    (* arity f = length ts *)
    apply Ok. apply (@Fun Sig f).
    eapply Vcast. apply (vec_of_list ts').
    transitivity (length ts). apply h'. refl. auto.
    (* arity f <> length ts *)
    exact (Ko _ (Error EtermUnfixedArity)).
    (* Ko: some argument could not be translated *)
    exact (Ko _ m).
    (* nil *)
    exists (Ok nil). intros l hl. inversion hl. refl.
    (* cons *)
    intros t ts [t'|] [[ts'|] h'].
    exists (Ok (t'::ts')). intros l hl. inversion hl. simpl.
    rewrite h'; refl.
    exists (Ko _ m). intros l hl. discr.
    exists (Ko _ m). intros l hl. discr.
    exists (Ko _ m). intros l hl. discr.
  Defined.

  (***********************************************************************)
  (** Translate CPF [rule] into CoLoR [arule]. *)
  (***********************************************************************)  

  Definition color_rule (r : rule) : result arule :=
    let (a, b) := r in
    match color_term a with
      | Ok l'  =>  Match color_term b With r' ===> Ok (mkRule l' r')
      | Ko m   =>  Match color_term b With _  ===> Ko _ m
    end.
  
  (***********************************************************************)
  (** Translate CPF [rules] into CoLoR [arules] *)
  (***********************************************************************)

  Definition color_rules (rs : rules) : result arules :=
    map color_rule rs.
  
  (***********************************************************************)
  (** ** Data type representing (intermediate) termination problems, and
         mathematical relation corresponding to it.                      *)
  (***********************************************************************)
  
  Inductive system : Type :=
  | Red        : arules -> system
  | Red_mod    : arules -> arules -> system
  | Hd_red_mod : arules -> arules -> system.
  
  Definition rel_of_sys s :=
    match s with
      | Red R          => red R (* Standard rewrite step. *)
      | Red_mod E R    => red_mod E R (* Relative rewrite step. *)
      | Hd_red_mod E R => hd_red_mod E R (* Relative head rewrite step. *)
    end.
  
  (***********************************************************************)
  (** Translate a [certificationProblem] into a [system].                *
     No strategy means standard rewriting without restriction.           *)
  (***********************************************************************)
  
  Definition input_trsInput (t: trsInput) :=
    match t with
      | (_, (Some stra), _, _)        => Ko _ (Todo TinputStrategy)
      | (rs, None, oeqs, orels)       =>
        match list_of_option color_rules oeqs,
              list_of_option color_rules orels,
              color_rules rs with
          | Ok nil, Ok nil, Ok rs     => Ok (Red rs)
          | Ok nil, Ok rels, Ok rs    => Ok (Red_mod rels rs)
          | Ok eqs, Ok rels, Ok rs    => Ko _ (Todo TinputEquations)
          | Ko m, _, _                => Ko _ m
          | _, Ko m, _                => Ko _ m
          | _, _, Ko m                => Ko _ m
        end
    end.

  Definition dpInput (d: dpInput) :=
    match d with
      | (_, _, (Some stra), _)         =>   Ko _ (Todo TinputStrategy)
      | (rs, dps, None, b) =>
        Match color_rules rs With rs   ===>
        Match color_rules dps With dps ===> Ok (Hd_red_mod rs dps)
    end.

  Definition sys_of_input (i : input) :=
    match i with
      | Input_trsInput t => input_trsInput t
      | Input_dpInput d  => dpInput d
      | Input_orderingConstraints _        =>
        Ko _ (Todo TInput_orderingConstraints)
      | _  => Ko _ (Todo Todo1)
    end.
  
  Definition sys_of_pb (c: certificationProblem) :=
    match c with
        | (i, _, _, _) => sys_of_input i
    end.
 
  (***********************************************************************)
  (** Translation function of [number] and [coefficient].                *)
  (***********************************************************************)
      
  (* Translation function of [number] -> [nat]. *)
  
  Definition color_number_N n : result nat :=
    match n with
      | Number_integer i      => (int_to_nat i)
      | Number_rational i pos => Ko _ (Todo TnumberRational)
    end.
  
  (* Translation function of [coefficient] -> [nat]. *)
  
  Definition color_coef_N c : result nat :=
    match c with
      | Coefficient_number i      => color_number_N i
      | Coefficient_minusInfinity => Ko _ (Todo TcoefMinusInf)
      | Coefficient_plusInfinity  => Ko _ (Todo TcoefPlusInf)
      | Coefficient_vector _      => Ko _ (Todo TcoefVector)
      | Coefficient_matrix _      => Ko _ (Todo TcoefMatrix)
    end.
  
  (* Translation function of [number] -> [integer]. *)
  
  Definition color_number_Z n : result integer :=
    match n with
      | Number_integer i      => Ok i
      | Number_rational i pos => Ko _ (Todo TnumberRational)
    end.
  
  (* Translation function of [coefficient] -> [integer]. *)
  
  Definition color_coef_Z c : result integer :=
    match c with
      | Coefficient_number i      => color_number_Z i
      | Coefficient_minusInfinity => Ko _ (Todo TcoefMinusInf)
      | Coefficient_plusInfinity  => Ko _ (Todo TcoefPlusInf)
      | Coefficient_vector _      => Ko _ (Todo TcoefVector)
      | Coefficient_matrix _      => Ko _ (Todo TcoefMatrix)
    end.
  
  (* Translation function of [number] -> [Q]. *)
  
  Require Import QArith. Open Scope Q_scope.
  
  Definition color_number_Q n : result Q :=
    match n with
      | Number_integer i      => Ok (inject_Z i) (* i/1 *)
      | Number_rational i pos => Ok (Qmake i pos)
    end.
  
  (* Translation function of [coefficient] -> [Q]. *)
  
  Definition color_coef_Q (c: coefficient) : result Q :=
    match c with
      | Coefficient_number i      => color_number_Q i
      | Coefficient_minusInfinity => Ko _ (Todo TcoefMinusInf)
      | Coefficient_plusInfinity  => Ko _ (Todo TcoefPlusInf)
      | Coefficient_vector _      => Ko _ (Todo TcoefVector)
      | Coefficient_matrix _      => Ko _ (Todo TcoefMatrix)
    end.
  
  Close Scope Q_scope.
  
  (* Translation function of [coefficient] -> [ArcticDom] (Arctic
    natural numbers).  *)
  
  Definition number_aux i :=
    match color_number_Z i with
      | Ok i => Match int_to_nat i With i ===> Ok (Pos i)
      | Ko e => Ko _ (Error ENotArcNat)
    end.

  Definition color_coef_Arcnat (c: coefficient) : result ArcticDom :=
    match c with
      | Coefficient_number i      => number_aux i
      | Coefficient_minusInfinity => Ok MinusInf
      | Coefficient_plusInfinity  => Ko _ (Todo TcoefPlusInf)
      | Coefficient_vector _      => Ko _ (Todo TcoefVector_arc)
      | Coefficient_matrix _      => Ko _ (Todo TcoefMatrix_arc)
    end.
  
  (* Translation function of [coefficient] -> [ArcticBZDom] (Arctic
    integer numbers or below zero). *)
  
  Definition number_arc_aux i :=
    match color_number_Z i with
      | Ok i => Ok (Fin i)
      | Ko e => Ko _ (Error ENotArcBZ)
    end.
    
  Definition color_coef_ArcInt c : result ArcticBZDom :=
    match c with
      | Coefficient_number i      => number_arc_aux i
      | Coefficient_minusInfinity => Ok MinusInfBZ
      | Coefficient_plusInfinity  => Ko _ (Todo TcoefPlusInf)
      | Coefficient_vector _      => Ko _ (Todo TcoefVector_arcbz)
      | Coefficient_matrix _      => Ko _ (Todo TcoefMatrix_arcbz)
    end.
  
  (* Translation function of [coefficient] -> [TropicalDom]
    (Tropical numbers). *)
  
  Definition number_trop_aux i :=
    match color_number_Z i with
      | Ok i => Ok (TPos (Z.to_nat i))
      | Ko e => Ko _ (Error ENotTrop)
    end.
      
  Definition color_coef_Trop c : result TropicalDom :=
    match c with
      | Coefficient_number i      => number_trop_aux i
      | Coefficient_minusInfinity => Ko _ (Todo TcoefMinusInf)
      | Coefficient_plusInfinity  => Ok PlusInf
      | Coefficient_vector _      => Ko _ (Todo TcoefVector_trop)
      | Coefficient_matrix _      => Ko _ (Todo TcoefMatrix_trop)
    end.
  
  (***********************************************************************)
  (** ** POLYNOMIAL INTERPRETATIONS                                      *)
  (***********************************************************************)

  (* The translation funciton for polynomials should be parameterized by
     a ring strucutre and a function for translating coefficients into this
     structure.
     Translation function for coefficients for each ring structure, and a
     function converting a domain into the corresponding ring structure. *)

  Class CPFRing  :=
    { or       :> OrderedRing;
      cpf_coef : coefficient -> result s_typ}.
 
  Import SR_Notations.

  Context {cpf_ring : CPFRing}.

  (***********************************************************************)
  (* The translation function of [polynomial] -> [poly].
     - Polynomials depends on the maximum number of [n] variables.
     - Assume that n is a variable in a polynomial. 
  COQ REMARK: in COQ [positive_integer] starting from 1, the list of
      variables in CoLoR starting from 0. *)
  (***********************************************************************)

  Section poly.
    
    Variable n : nat.

    Definition coef_aux c :=
      Match cpf_coef c With c ===> Ok (pconst n c).

    Definition variable_aux x :=
      let x := ((nat_of_P x) - 1)%nat in
      match lt_dec x n with
        | left h =>   Ok (pxi h)
        | _      =>   Ko _ (Error EpolyVarTooBig)
      end.

    Definition sum_aux l (P: polynomial -> result (poly n)) :=
      let fix color_poly_sum acc l :=
          match l with
            | nil     =>   Ok acc
            | p :: l' =>
              Match P p With p ===> color_poly_sum (padd p acc) l'
          end
      in color_poly_sum (pzero n) l.

    Definition product_aux l (P: polynomial -> result (poly n)) :=
      let fix color_poly_prod acc l :=
          match l with
            | nil     =>  Ok acc
            | p :: l' =>  Match P p With p  ===>
            color_poly_prod (pmult p acc) l'
          end
      in color_poly_prod (pconst n 1) l.

    Fixpoint color_poly p : result (poly n) :=
      match p with
        |  Polynomial_coefficient c => coef_aux c
        | Polynomial_variable x     => variable_aux x
        | Polynomial_sum l          => sum_aux l color_poly
        | Polynomial_product l      => product_aux l color_poly
        | Polynomial_max _          => Ko _ (Todo TpolyMax)
        | Polynomial_min _          => Ko _ (Todo TpolyMin)
      end.
    
    Definition color_function f := color_poly f.
    
  End poly.

  (***********************************************************************)
  (** Translate CPF polynomial [interpret] into CoLoR interpret. *)
  (***********************************************************************)
 
  Section poly_interpret.

    Definition color_interpret (is: symbol * cpf.arity * function) :
      result {f: symbol & poly (arity f)} :=
      let '(f, _, fn) := is in
      Match color_function (arity f) fn With p ===> Ok (existT f p).
    
    Context {Ord: OrderedRing}.
    
    (***********************************************************************)
    (** [fun_of_pairs_list] is a representation for an interpretation
     associating to every function symbol of arity [n], an integer
     polynomial with [n] variables. It is represented by a list of pairs
     [(g, pi)], where [g] is a function symbol and [pi] is its
     interpretation *)

    Section fun_pairs.
      
      Variable f: symbol.
      
      Fixpoint fun_of_pairs_list (l : list {g: symbol & poly (arity g)}) :
        poly (arity f) :=
        match l with
          | existT g p :: l' =>
            match @eq_symb_dec Sig g f with
              | left h  => poly_cast (f_equal arity h) p (* g = f *)
              | right _ => fun_of_pairs_list l' (* g <> f *)
            end
          | nil => default_poly (arity f) (* coefficent is equal to 1 *)
        end.
      
    End fun_pairs.
    
    (***************************************************************************)
    (* Polynomial weak monotone and polynomial strogn monotone related
    to reduction pair *)

    Section poly_redPair.
      
      (* Assume these variables to be use in the proof of polynomial
      are weak monotone. It will help the correctness proof of
      polynomial is simpler. *)

      Variable l : list {g : symbol & poly (arity g)}.
      Variable H : forallb (fun x : {f : symbol & poly (arity f)} =>
                   let (f, p) := x in bcoef_not_neg p) l = true.
      
      (* Polynomial interpretations function. *)

      Definition trsInt f := fun_of_pairs_list f l.
      
      (***********************************************************************)
      (** The proof of polynomial are weakly monotone. It is a weak
      monotone when the coefficient of polynomial is positive. *)
      
      Lemma trsInt_wm_poly : forall f, pweak_monotone (trsInt f).
      
      Proof.
        intro f.
        unfold pweak_monotone, trsInt, fun_of_pairs_list.
        induction l.
        (* nil *)
        apply pcoef_default_check.
        (* cons *)
        simpl in *. destruct a as [g].
        destruct (@eq_symb_dec Sig g f).
        (* f = g *)
        unfold poly_cast. simpl_eq.
        rewrite andb_eq in H. destruct H.
        rewrite <- bcoef_not_neg_ok. hyp.
        (* f <> g *)
        apply IHl0.
        rewrite andb_eq in H. destruct H. hyp.
      Qed.
      
      (***********************************************************************)
      (** Polynomial interpretations in the setting of monotone
      algebras of domain natural numbers. *)
      
      Definition TPolyInt_poly := mkbTPolyInt Sig trsInt trsInt_wm_poly.
      Definition MonPoly       := @MonotoneAlgebra Sig _ TPolyInt_poly.
      Definition WP            := @WP_MonAlg Sig MonPoly.
  
      (***********************************************************************)
      (** Polynomial interpretations in the setting of monotone algebras
         of domain rational. *)
      
      Definition MonPolyQ      := @MonotoneAlgebraQ _ _ TPolyInt_poly.
      Definition WP_Q del      := @WP_MonAlg Sig (MonPolyQ del).
      
    End poly_redPair.
    
    (***************************************************************************)

    Section poly_strong.
    
    (** Polynomial interpretations in the setting of monotone algebras.
     In CoLoR library for proving polynomial interpretation uses [modules]
     and [functors]. Modules cannot be defined inside sections. These files
     are redefine and reproof from CoLoR library for polynomial
     interpretation use [records] instead. *)
     
      Variable l : list {g : symbol & poly (arity g)}.
      Variable H : forallb (fun x : {f : symbol & poly (arity f)} =>
                            let (f, p) := x in bcoef_not_neg p) l &&
                   forallb (fun x : {f : symbol & poly (arity f)} =>
                            let (f, p) := x in
                   forallb (fun x0 : nat_lt (arity f) =>
                            or_bgt (coef (mxi (prf x0)) p) 0)
                           (mk_nat_lts (arity f))) l = true.
      
      Lemma pstrong_monotone_default : PolyStrongMonotone (default_pi Sig).
      
      Proof.
        intros. split. apply pweak_monotone_default.
        (* coef p >> 0*)
        intros i Hi. unfold default_pi.
        assert (Hin: List.In (1, mxi Hi)(default_poly (arity f))).
        apply default_poly_mxi_1.
        set (w := coef_not_In_coef (default_poly (arity f)) (mxi Hi) 1
                                   (pcoef_default_check (arity f)) Hin).
        (* auto with zarith.*)
        unfold or_ge in w. rewrite <- or_one_gt_zero.
        intuition.
      (* TODO *)
      Admitted.

      (* Prove that polynomial interpretations are strong monotone. It
      is a strong monotone when it is a weak monotone and each
      coefficient is greater than 0. *)

      Lemma trsInt_pw_poly : forall f, pstrong_monotone (trsInt l f).

      Proof.
        intro f.
        unfold pstrong_monotone, trsInt, fun_of_pairs_list.
        induction l.
        (* nil *)  
        split.
        (* Default polynomial is weak monotone. *)
        apply pcoef_default_check.
        (* Default polynomial is strong monotone. *)
        intros i Hi. 
        apply pstrong_monotone_default.
        (* cons *)
        simpl in *. destruct a as [g]. split.
        (* Polynomial is weak monotone. *)
        destruct (@eq_symb_dec Sig g f).
        (* g = f *)
        change (coef_not_neg (poly_cast (f_equal arity e)p)).
        unfold poly_cast. simpl_eq.
        repeat rewrite andb_eq in H. intuition.
        rewrite <- bcoef_not_neg_ok. auto.
        (* g <> f *)
        apply IHl0. rewrite andb_eq. intuition.
        repeat rewrite andb_eq in H. destruct H.
        destruct H0. hyp.
        repeat rewrite andb_eq in H. destruct H.
        destruct H1. hyp.
        (* pstrong_monotone *)
        destruct IHl0. repeat rewrite andb_eq in H. intuition.
        intros i Hi. destruct (@eq_symb_dec Sig g f).
        (* f = g *)
        repeat rewrite andb_eq in H. subst.
        destruct H.
        assert (In (mk_nat_lt Hi) (mk_nat_lts (arity f))).
        apply mk_nat_lts_complete. intuition.
        rewrite forallb_forall in H5. ded (H5 _ H4).
        rewrite or_bgt_ok in H6. simpl in *. hyp.
        (* f <> g *)
        ded (H1 i Hi). hyp.
      Qed.
      
    End poly_strong.

  End poly_interpret.

  (***********************************************************************)
  (** ** MATRIX INTERPRETATIONS                                          *)
  (***********************************************************************)
   
  (* Define a coefficient into SemiRing structure. Matrix build on
    SemiRing. *)
  
  Class CPFSRing :={
    OSR         :> OrderedSemiRing;
    cpf_sr_coef : coefficient -> result s_typ}.

  (* Assume the dimension of matrices. *)

  Variable dim     : nat.
  Notation dim_pos := (dim_pos dim).
  Notation mint    := (@matrixInt _ dim).

  Context {cpf_sring : CPFSRing}.
  
  (****************************************************************************)
  (* Translation function for [vector]. Vector in CPF represents as
     column, while in Color it represents as row. *)
  (****************************************************************************)

  Definition color_column_of_cpf_column col :
    result (VecUtil.vector s_typ dim)       :=
    Match map cpf_sr_coef col With col      ===> vector_of_list col dim.
  
  Definition color_vector (v: cpf.vector) : result (vector s_typ dim) :=
    match v with
      | Vector_vector cs => color_column_of_cpf_column cs
    end.
  
  (****************************************************************************)
  (** Translation function for [matrix]. Matrix builds on
        SemiRing so it needs a coefficient build on SemiRing structure.       *)
  (****************************************************************************)

  Definition color_matrix_of_cpf_matrix (cols: list (list coefficient)):
    result (matrix dim dim ):=
    Match map color_column_of_cpf_column cols With cols ===>
    Match vector_of_list cols dim  With M ===> Ok (mat_transpose M).
  
  Definition color_matrix (m: cpf.matrix) : result (Matrix2.matrix dim dim) :=
    match m with
      | Matrix_matrix vs => color_matrix_of_cpf_matrix vs
    end.
   
  (****************************************************************************)
  (* Polynomial function for matrices.  In CoLoR the type of polynomials
  depends on the maximum of number of [n] variables. Assuming a
  maximum number [n] of variables.  Define polynomial function for
  matrix interpretation over domain natural numbers.

  Matrix interpretations where the elements are vectors. Example: if
  the domain is naturals, then the coefficients in front of variables
  have to be matrices and the constants should be vectors over the
  naturals.
     
  Note that when using polynomials over a vector-domain, then the
  "constant coefficient" is a vector whereas the other coefficients
  are matrices. Moreover, in this case only linear polynomials are
  allowed. For dimension [d = 1], the matrix interpretaions coincide
  with linear polynomial interpretations.
     
  Polynomial function for matrix interpretation over natural numbers:
  Formula of matrix interpretation: [f (v1,...,vn) = F1.v1 + ... +
  Fn.vn + f0; (1)] (where [v1,...,vn, f0]: are vector)
     
  [Variable] return a position [i-th] of variable called [x] that
  attached to matrix coefficient where [arity > 1]; if variable [x]
  does not occurs then this coefficient is [0] (the zero matrix);
  REMARK: [Variable] [i] has type positive integer starting from [1],
  list of variables in CoLoR starting from [0].
     
  [Polynomial_sum]/[Polynomial_product]: [v + \sum Mi * xi; i \in (1,
  k)]; where [v] is a vector, a polynomial function: [M2.x2 + v +
  M1.x1] is also a certificate.
     
  [Coefficient]: for each function symbol [F] of arity [n] from the
  signature, declare variables [F1, ..., Fn] for square matrices [(d x
  d)] (in the case of [Coefficient_matrix]); and a variable [f] for a
  (column) vector of [(d x 1)] (in the case of [Coefficient_vector)].
     
  Standard polynomial orders over a specified domain (a semiring or
  something else). Note that if the domain is "matrices of naturals"
  then everything has to be a matrix, even the constants. This is in
  contrast to "matrixInterpretations" where the constants are
  vectors. *)

  Section poly_matrix.

    Variable n : nat.

    Definition sum_mat_aux l mi
      (P: polynomial -> matrixInt dim n -> result (matrixInt dim n)):=
      let fix color_sum_mint acc l :=
          match l with
            | nil      => Ok acc
            | p1 :: l' => Match P p1 acc With Mi
                       ===> color_sum_mint Mi l'
          end
      in color_sum_mint mi l.

    Definition product_mat_aux m i mi :=
      let i := ((nat_of_P i) - 1)%nat in
      Match color_matrix m With M ===>
      match lt_dec i n with
        | left h  => Ok ({|const := (const mi); (* n < m *)
                           args  := Vreplace (args mi) h M|})
        | _       => Ko _ (Error EpolyVarTooBig_matrix)  (* ~n < m*)
      end.

    Fixpoint color_poly_matrix (p: polynomial) (mi: matrixInt dim n):
      result (matrixInt dim n) :=
      match p with
        | Polynomial_sum l => sum_mat_aux l mi color_poly_matrix
        | Polynomial_product (Polynomial_variable i       ::
          Polynomial_coefficient (Coefficient_matrix m)   :: nil) (* xi * Mi *)
        | Polynomial_product (Polynomial_coefficient
          (Coefficient_matrix m) :: Polynomial_variable i :: nil) (* Mi * xi *)=>
          product_mat_aux m i mi
        | Polynomial_product (Polynomial_coefficient
          (Coefficient_vector v) :: nil) =>
           Match color_vector v With v ===> Ok {| const := v; args := (args mi)|}
        | Polynomial_product nil         => Ok mi
        | _                              => Ko _ (Todo TPoly_MatrixNatInt)
      end.
    
    Definition color_matrix_function f :=
      let mi := {|const := zero_vec;
                  args  := Vconst zero_matrix n |} in
      color_poly_matrix f mi.

  End poly_matrix.

  (****************************************************************************)
  (** Translation CPF polynomial [interpret] of matrix into CoLoR interpret.  *)
  (****************************************************************************)
  
  Section interpret_matrix.

    Definition color_interpret_matrix (is: symbol * cpf.arity * function) :
      result {f: symbol & mint (arity f)} :=
      let '(f, _, fn) := is in
      Match color_matrix_function (arity f) fn With m ===>
        Ok (existT f m).

    (* MOVE into CoLoR library. *)
    
    Definition matrix_cast n m (Heq: n = m) (p:mint n) : mint m.
      rewrite <- Heq; auto.
    Defined.
    
    (* Default matrix interpretation. *)

    Definition default_matrix (n: nat) :=
      Build_matrixInt (id_vec dim_pos) (Vconst id_matrix n).

    (**************************************************************************)
   
    Section fun_pairs.

      Variable f : symbol.
      
      Fixpoint fun_of_pairs_list_matrix (l : list {g: symbol & mint (arity g)})
      : mint (arity f) :=
        match l with
          | existT g m :: l' =>
            match @eq_symb_dec Sig g f with
              | left h  => matrix_cast (f_equal arity h) m (* g = f *)
              | right _ => fun_of_pairs_list_matrix l' (* g <> f *)
            end 
          | nil => default_matrix (arity f)
        end.
      
    End fun_pairs.

    (* Define matrix interpretation use for all domains.  *)

    Variable l : list {g: symbol & mint (arity g)}.

    (* Matrix interpretations function. *)

    Definition trsInt_matrix (f: Sig) := fun_of_pairs_list_matrix f l.
        
    (* Define an Instance of [TMatrixInt] (AMatrixBasedInt2). *)
          
    Global Instance TMatrix_Int : TMatrixInt (OSR:=OSR) Sig dim.

    Proof.
      apply Build_TMatrixInt.
      apply trsInt_matrix.
    Defined.
    
  End interpret_matrix.

  (****************************************************************************)
  (** ** RECURSIVE PATH ORDERINGS                                             *)
  (****************************************************************************)
  
  Require Import rpo2 Coccinelle2 rpo_extension rpo Coccinelle.
  
  Section rpo.
    
    (**************************************************************************)
    (* Translation function [status_type] and [prec_nat] *)
    
    Section status_type.
      
      Variable f : symbol.

      (* Define a function return a status *)

      Definition stat t :=
        match t with
          | T10_lex => Lex
          | T10_mul => Mul
        end.

      (* Translation function of [RedPair_pathOrder] ->
      [status_type]. 
      For example: stat(f#) = lex
      - In the list of [RedPair_pathOrder], stat[] is the fourth
        argument [t10]. *)

      Fixpoint col_status (l : list (symbol * cpf.arity *
        nonNegativeInteger * t10)) : status_type :=
        match l with
          | (g, _, _, t) :: l' =>
            match @eq_symb_dec Sig g f with
              | left _  => stat t (* g = f *)
              | right _ => col_status l' (* g <> f *)
            end
          | nil => Lex (* If it is nil/default, return Lex *)
        end.

      (* Translation function of [RedPair_pathOrder] -> [nat]
      ([prec_nat]). 
       For example: prec (f#) = 3
       - The arity of f# is: 1
       - The prec_nat of f# is: 3.
       In the list of
       |RedPair_pathOrder]: list (symbol * arity * nonNegativeInteger * t10),
       it is the third argument [nonNegativeInteger]. *)
      
      Fixpoint col_prec_nat (l : list (symbol * cpf.arity *
        nonNegativeInteger * t10)) : nat :=
        match l with
          | (g, _, n, _) :: l' =>
            match @eq_symb_dec Sig g f with
              | left  _ => let n := nat_of_N n in n
                           (* translate from nonNegativeInt to nat *)
              | right _ => col_prec_nat l'
            end 
          | nil => 0%nat (* When it is nil/default return 0 *)
        end.
      
    End status_type.

    (**************************************************************************)

    Variable l : list (symbol * cpf.arity * nonNegativeInteger * t10).

    (* An assumption of rpo function. *)
    Variable rpo_arg: nat.

    (* Sig -> status_type *)
    Definition color_status f := col_status f l.

    (* Sig -> nat *)
    Definition color_prec_nat f := col_prec_nat f l.

    (* Define an Instance for [Class Precedence]. *)
    Global Instance Precendence_Imp : Pre Sig.

    Proof.
      apply mkPrecedence.
      apply color_status.
      apply color_prec_nat.
      apply rpo_arg.
    Defined.

    (* Correctness proof of [prec_nat] *)
    
    Lemma prec_eq_ok : forall f g,
    rpo_extension.prec_eq_bool color_prec_nat f g = true <->
    rpo_extension.prec_eq color_prec_nat f g.
    
    Proof.
      intros f g. gen (rpo_extension.prec_eq_bool_ok color_prec_nat f g).
      intuition. rewrite H0 in H. hyp.
      case_eq (rpo_extension.prec_eq_bool color_prec_nat f g); intros; try refl.
      rewrite H1 in H. absurd (rpo_extension.prec_eq color_prec_nat f g); hyp.
    Qed.

    (* Define a boolean function for status symbol. *)

    Definition bprec_eq_status_symb f g : bool :=
      implb (rpo_extension.prec_eq_bool color_prec_nat f g)
      (beq_status (color_status f) (color_status g)).
    
    (* Correctness proof of boolean function for status symbol. *)
    
    Lemma bprec_eq_status_symb_ok : forall f g,
     bprec_eq_status_symb f g = true           <->
     (rpo_extension.prec_eq color_prec_nat f g ->
     color_status f = color_status g).

    Proof.
      intros f g. unfold bprec_eq_status_symb, implb.
      case_eq (rpo_extension.prec_eq_bool color_prec_nat f g); intros.
      rewrite prec_eq_ok in H. rewrite beq_status_ok.
      intuition.
      intuition. rewrite <- prec_eq_ok in H1. rewrite H in H1.
      discr.
    Qed.

    (* Define a function [empty_rpo_infos] to be used in function
       [rpo_eval]. *)
    
    Definition empty_rpo_infos :=
      empty_rpo_infos Sig (@Prec Sig Precendence_Imp) rpo_arg.
    
    (* Define a function [rpo_eval] to be used in the function
       [pathOrdering] in [rainbow_full_termin.v] *)
    
    Definition rpo_eval :=
      @rpo_eval Sig (@Prec Sig Precendence_Imp) empty_rpo_infos rpo_arg.

  End rpo.

  (***********************************************************************)
  (** ** ARGUMENT FILTERING                                              *)
  (***********************************************************************)
  
  Require Import error_monad.

  Section AF.
    
    (* Check the filtering in both cases. *)
    
    Definition is_proj_filter t :=
      match t with
        | T11_collapsing _
        | T11_nonCollapsing _ => true
      end.

    (* Translation function of [positiveInteger] into CoLoR. *)
    
    Open Scope nat_scope.
    
    (* Given a position in CPF and return a type nat *)
    
    Definition color_position (p: positive) : nat :=
      nat_of_P p - 1.

    (* Given a list of positions and return a list of nat. *)
    
    Definition color_positions (ps: list position) : list nat :=
      List.map color_position ps.
    
    (*********************************************************************)
    (** COLLAPSING ARGUMENT FILTERING - PROJECTION                       *)
 
    (* Declare a list of argumentFilter. *)
    Variable l : list (symbol * cpf.arity * t11).

    (* First define [raw_pi], it is defined as [Variable raw_pi : Sig
    -> option nat.] in [AProj.v]. From the list [l] if it is a
    [nonCollapsing] then return None, if it is a collapsing return
    [Some (position - 1)], default/nil is [None]. *)

    (** Build argument filtering on projection (collapsing) *)

     (* Define [pi: forall f: Sig arity, option {k:nat | k < arity f}] in
     the case of projection (collapsing) only from an argument af in CPF. *)

    Require Import AProj.

    Section proj_af.

      Variable f: symbol.

      (* Return a position of collapsing only *)

      Definition pos_col_aux p :=
        let n := color_position p in
        match lt_dec n (arity f) with
          | left h => Some (mk_proj Sig f h)
          | right _ => None
        end.
          
      Fixpoint position_collapsing t :=
        match t with
          | T11_collapsing p => pos_col_aux p
          | T11_nonCollapsing _ => None
        end.

      (* Define pi in the case of projection (collapsing) *)
      Fixpoint pi_proj (l: list (symbol * cpf.arity * t11)):
      option {k : nat | k < arity f}:=
        match l with
          | (g, _, t) :: l' =>
            match @eq_symb_dec Sig g f with
              | left _ => position_collapsing t (* g =  f *)
              | right _ => pi_proj l' (* g <> f *)
            end
          | nil => None (* default is None *)
      end.

      (* Define option nat on collapsing to check bvalid_symbol *)
      Definition pi_valid_aux t :=
        match t with
          | T11_collapsing p => Some (color_position p)
          | T11_nonCollapsing _ => None
        end.

      Fixpoint pi_valid (l : list (symbol * cpf.arity * t11)): option nat :=
        match l with
          | (g, _, t) :: l' =>
            match @eq_symb_dec Sig g f with
              | left _ => pi_valid_aux t
              | right _ => pi_valid l'
            end
          | nil => None
        end.

    End proj_af.

    (* Define pi_proj take a symbol as argument *)

    Definition color_pi_proj f := pi_proj f l.

    (* an element [x:nat] is valid in projection when in a list
       signature, x < arity f. *)

    Definition color_pi_valid f := pi_valid f l.

    (* use to check the symbol is a valid projection or not. *)
    Definition color_bvalid := @bvalid Sig color_pi_valid
                               (list_split_triple l). 

    (* Define an Instance for Class [Proj] in ARedPair2.v *)
    
    Global Instance Proj_Imp : Proj Sig.
    Proof.
      apply Build_Proj.
      apply color_pi_proj.
    Defined.

    (* Define proj function *)

    Definition color_proj t := @proj Sig color_pi_proj t.

    Definition color_proj_rules (r: arules) :=
      @proj_rules Sig color_pi_proj r.

    (* use in subtermproc *)
    Definition is_collapsing t :=
      match t with
        | T11_collapsing _ => true
        | _ => false
      end.

    (*********************************************************************)
    (** NON-COLLAPSING ARGUMENT FILTERING                                *)

    Require Import AFilterPerm ListRepeatFree.

    Section AF1.

      Variable n: nat.

      (* This parameter will become a condition to check later in
      the definition below *)

      Parameter raw_pi_ok : forall ps,
       forallb (bgt_nat n) (color_positions ps) = true.

      (* REMARK: do not return nil in collapsing, it is not a right value.
         mk_nat_lts { val :> nat; prf : arity f < n }: list (nat_lt n) *)

      Definition pi_filter_aux t : nat_lts n :=
        match t with
          | T11_collapsing _     => mk_nat_lts n
          | T11_nonCollapsing ps =>
            if forallb (bgt_nat n) (color_positions ps)
            then build_nat_lts n
            (color_positions ps)(raw_pi_ok ps)
            else nil
        end.

    End AF1.
    
    (* define a function pi_filter returns a pair (f, pi) *)
    
    Definition pi_filter (is: symbol * cpf.arity * t11) :
      {f:symbol & nat_lts (arity f)} :=
      let '(f, _, t) := is in
      existT f (pi_filter_aux (arity f) t).
    
    Section fun_filter_AF.

      Variable f : symbol.
      
      (* define a cast function for filtering *)
      Definition filter_cast n m (Heq : n = m) (p: nat_lts n) : nat_lts m.
        rewrite <- Heq; auto.
      Defined.
    
      (* Define function like fun_of_pairs_poly *)

      Fixpoint fun_pi_filter (l : list {g: symbol & nat_lts (arity g)}):
        nat_lts (arity f) :=
        match l with
          | existT g t :: l' =>
            match @eq_symb_dec Sig g f with
              | left h => filter_cast (f_equal arity h) t
              | right _ => fun_pi_filter l' (* g <> f *)
            end
          | nil => nil (* default value *)
        end.

    End fun_filter_AF.

    Variable ls : list {g: symbol & nat_lts (arity g)}.

    Definition color_pi_filter  f := fun_pi_filter f ls.

    (* Define filter rules *)

    Definition color_filter_rule := @AFilterPerm.filter_rule Sig.
      
    (* Translation function of [filter_rules]. *)
    
    Definition color_filter_rules r := List.map (color_filter_rule r).

    (* Define an Instance for Class [Perm] in ARedPair2.v *)

    Global Instance Perm_Imp : Perm Sig.
    Proof.
      apply Build_Perm.
      apply color_pi_filter.
    Defined.

    Definition color_perm_Sig := @perm_Sig Sig Perm_Imp.

    (* Define color filter term *)
    Definition color_filter (t: aterm) :=
      @AFilterPerm.filter Sig color_pi_filter t.

    Variable H : forallb (fun x : {f : symbol & nat_lts (arity f)} =>
                 let (f, p) := x in brepeat_free beq_nat
                 (List.map (@val (arity f)) p)) ls  = true.

    Lemma pi_filter_non_dup : forall f, repeat_free (List.map (@val (arity f))
      (color_pi_filter f)).

    Proof.
      intro f. unfold color_pi_filter, pi_filter, fun_pi_filter.
      induction ls; simpl in *; try discr.
      (* default case *)
      auto.
      (* cons case *)
      destruct a as [g].
      destruct (@eq_symb_dec Sig g f); try discr;
      simpl in *. Focus 2.
      (* g <> f *)
      apply IHl0. rewrite andb_eq in H. destruct H. apply H1.
      (* g = f *)
      unfold filter_cast. simpl_eq. rewrite andb_eq in H.
      destruct H. rewrite brepeat_free_ok in H0.
      apply H0.
      intros x y. intuition.
      rewrite beq_nat_ok in H4. apply H4.
      apply beq_nat_ok. apply H4.
    Qed.

    (* Proof permut by using the color_pi_filter *)

    Variable H1: forallb (fun x : {f: symbol & nat_lts (arity f)} =>
                 let (f, p) := x in bforall_lt (fun i =>
                 mem beq_nat i (List.map (@val (arity f)) p)) (arity f)) ls
                 = true.

    Lemma pi_filter_permut : forall f i, i < arity f ->
      In i (List.map (@val (arity f)) (color_pi_filter f)).

    Proof.
      intros f. unfold color_pi_filter, pi_filter, fun_pi_filter.
      induction ls; simpl in *; try discr.
      (* default case *)
      Focus 2.
      (* cons case *)
      destruct a as [g].
      destruct (@eq_symb_dec Sig g f); try discr.
      (* g = f *)
      unfold filter_cast. simpl_eq. rewrite andb_eq in H1.
      destruct H1. rewrite bforall_lt_ok in H0.
      unfold forall_lt in H0.
      apply H0.
      (* proof membership *)
      intuition. rewrite mem_ok in H1. apply H1.
      (* beq_nat *)
      intros x0 y. intuition. rewrite beq_nat_ok in H5.
      apply H5. apply beq_nat_ok. apply H5.
      apply mem_ok.
      (* beq_nat *)
      intros x0 y. intuition. rewrite beq_nat_ok in H5.
      apply H5. apply beq_nat_ok. apply H5.
      apply H1.
      (* g <> f *)
      apply IHl0. rewrite andb_eq in H. destruct H.
      apply H2. rewrite andb_eq in H1. destruct H1.
      apply H2.
      (* default case *)
    Admitted.
      
  End AF.

  (*********************************************************************)
  (** ** STRING REVERSE                                                *)
  (*********************************************************************)

  (** Translation functions for termination technique: string reverse. *)
  
  (* Define a function from [rs: rules] return list of [Sig/symbol]. *)

  Require Import AReverse AUnary.

  (* TODO section *)
  Section reverse.

    Variable n: nat.

    (* REMOVE *)
    Definition is_unary_aux (t: term) : nat :=
      match t with
        | Term_var _ => 0%nat
        | Term_funapp g _ => arity g
      end.
    (* REMOVE *)
    Definition is_unary_symbol (r: rule) : nat :=
      match r with
        | (l, r) =>
          match is_unary_aux l with
            | 0 => is_unary_aux r
            | o => o
          end
      end.

  End reverse.

  Section unary.

    Variable f: symbol.

    Require Import ATerm_of_String.

    Fixpoint fun_of_is_unary (l: list {g: symbol & nat}):
      nat :=
      match l with
        | existT g p :: l' =>
          match @eq_symb_dec Sig g f with
            | left h => 1%nat
            | right _ => fun_of_is_unary l'
          end
        | nil => 1%nat (* default value *)
      end.

    (*
    Fixpoint fun_of_is_unary (l: list {g: symbol & arity g = 1%nat }):
      arity f = 1%nat :=
      match l with
        | existT g p :: l' =>
          match @eq_symb_dec Sig g f with
            | left h => default_unary (arity f) (* CHECk *)
            | right _ => fun_of_is_unary l'
          end
        | nil => default_unary (arity f) (* default value *)
      end.*)

  End unary.

  (* REMOVE *)
  Fixpoint symbol_in_term (t: term) : list symbol :=
    match t with
      | Term_var _       => nil
      | Term_funapp g ts => g :: nil
    end.
  
  (* REMOVE*)
  Definition symbol_in_rule (r: rule) : list symbol :=
    match r with
      | (a, b)  =>
        match symbol_in_term a with
          | nil => symbol_in_term b
          | o   => o
        end
    end.

  (* REMOVE *)
  Definition symbol_in_rules (rs: rules) := flat (List.map symbol_in_rule rs).
  
  Definition return_symbol_aux (t:term) : option symbol :=
    match t with
      | Term_var _ => None
      | Term_funapp g _ => Some g
    end.

  Definition return_symbol (r: rule) : option symbol :=
    match r with
      | (a, b) => match return_symbol_aux a with
                    | None => return_symbol_aux b
                    | o => o
                  end
    end.

  (* Define a pair from rule *)

  Definition color_unary (r: rule) : result {g: symbol & nat} := 
    match return_symbol r with
      | None => Ko _ (Todo Todo1)
      | Some g => Ok  (existT g (is_unary_symbol r))
    end.

  Variable ls: list {g: symbol & nat}.

  (* Define color_fun_is_unary *)
  Definition color_fun_of_is_unary f := fun_of_is_unary f ls.

  Variable H: forallb (fun x : {f: symbol & nat} =>
              let (f, p) := x in beq_nat 1%nat (arity f)) ls = true.
            
  (* define a function like trsInt *)
  Definition unary_aux f := fun_of_is_unary f ls.

  Lemma color_bis_unary_ok: forall f, 1%nat = unary_aux f.

  Proof.
    intro f. unfold unary_aux, fun_of_is_unary.
    induction ls; simpl in *; try discr.
    (* default case *)
    auto.
    (* cons case *)
    destruct a as [g].
    destruct (@eq_symb_dec Sig g f); try discr.
    (* g = f *)
    auto.
    (* g <> f *)
    apply IHl. rewrite andb_eq in H.
    destruct H. apply H1.
  Qed.

End Top.
  
(****************************************************************************)
(** ** LOOP                                                                 *)
(****************************************************************************)

Require Import error_monad.

Section loop.

  (*  Require a dynamic arity *)
  (* Translate a string into nat *)

  Variable nat_of_string : string -> nat.

  Open Scope nat_scope.
  
  (* Given a [positionInTerm] type return a list of position of type
      natural numbers. *)

  (* TO BE CHECK: is it return the correct position in a term? *)

  Definition color_result_position (p: position) : result nat :=
   Ok ((nat_of_P p) - 1).
  
  Definition color_positionInTerm (ps: positionInTerm) : result (list nat) :=
    map color_result_position ps.
  
  (* From a rewriteStep: positionInTerm × rule × option boolean ×
  term. return a type [data: (positions * rule)] *)

  Fixpoint color_rewriteStep (a: symbol -> nat)
    (rs: list cpf.position * rule * option boolean * term ):
    result (list nat * arule a) :=
    let '(ps, r, _, _)          := rs in
    Match color_positionInTerm ps      With ps ===>
    Match color_rule a nat_of_string r With r  ===> Ok (ps, r). 
         
  Definition color_rewriteSteps (a: symbol -> nat)
    (rsteps: list (positionInTerm * rule * option boolean * term)):
    result (list (list nat * arule a)) :=
    match rsteps with
      | nil => Ok nil
      | rs  => map (color_rewriteStep a) rs
    end.

  (* Define function translate [context -> list position] *)

  Fixpoint color_position_of_context (c: context) : list nat :=
    match c with
      | Context_box                => nil
      | Context_funContext _ l c _ => List.length l ::
                                      color_position_of_context c
    end.
  
  (* Loop in relative termination proof. *)
  
  Require Import AModLoop.
  
  (* Define function return [mod_data = (list data * data)]. *)
  
  Definition color_mod_data a (ls: list (list cpf.position * rule *
    option boolean * term)):
    result ((list (list nat * arule a)) * (list nat * arule a)) :=
    match ls with
      | nil      => Ko _ (Todo Todo1)
      | l :: ls' =>
        Match color_rewriteStep  a l   With ds ===>
        Match color_rewriteSteps a ls' With mds ===> Ok (mds, ds)
    end.
  
    (* Define a type [list mod_data]. *)
  
  Definition color_list_mod_data a
    (ls: list (list (list cpf.position * rule * option boolean * term))):
    result (list ((list (list nat * arule a)) * (list nat * arule a))) :=
      map (color_mod_data a) ls.
  
  Close Scope nat_scope.
  
End loop.

(***********************************************************************)
(** ** Formalization of dependency pair transformation computing new
   signature such that arity of marked symbol is equal to arity of symbol
   in the case of dependency pair transformation. 
   
   [REMARK]: We may need to check that there is no sharp symbol in rules
   [R].
   
   [NOTE]: This section outside section [color] and define a new
   variable for arity because we want to use [Sig dp_arity] in the
   lemma [HFSig_of_dup_Sig_eq]. *)

Section DP.
  
  Variable arity : symbol -> nat.

  (* [dup_sig: Signature -> Signature]*)
  
  Definition FSig_of_dup_Sig  (f: dup_sig (Sig arity)) : Sig arity :=
    match f with
      | hd_symb s
      | int_symb (Symbol_sharp _ as s) => Symbol_sharp s
      | int_symb s                     => s
    end.

  Definition dp_arity (f:symbol) : nat :=
    match f with
      | Symbol_sharp g => arity g
      | h              => arity h
    end.
 
  Lemma HFSig_of_dup_Sig_eq: forall f : dup_sig (Sig arity),
    ASignature.arity f =
    @ASignature.arity (Sig dp_arity) (FSig_of_dup_Sig f).
    
  Proof.
    intros f. simpl. unfold dp_arity, dup_ar.
    destruct f; auto. simpl. destruct s; auto.
  Qed.
  
End DP.