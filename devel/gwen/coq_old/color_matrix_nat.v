(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2013-04-18

* Matrix interpretation over domain natural numbers

*)

Set Implicit Arguments.

Require Import ATrs ARedPair2 APolyInt_MA2 AMonAlg2 Equality LogicUtil
  List BoolUtil NatUtil VecUtil VecArith2 poly cpf2color cpf
  OrdSemiRing2 Matrix2 AMatrixInt2 AMatrixBasedInt2_Nat cpf_util.

(***********************************************************************)
(** ** Matrix interpretation over domain natural numbers is an
interpretation can be seen as an instance of monotone algebras with [A
= N^d] for some fixed dimension [d]. *)

Section S.

  Variable arity: symbol -> nat.
  Variable dim : nat.

  Notation Sig := (Sig arity).
  Notation dim_pos := (dim_pos dim).
  Notation mint := (matrixInt matrix dim).

  (** Cast *)
  
  Definition matrix_cast_nat n m (Heq: n = m)(p: mint n) : mint m.
  rewrite <- Heq; auto.
  Defined.

  (** Default matrix interpretation. *)
  
  Definition default_matrix_nat (n: nat) :=
    mkMatrixInt (id_vec dim_pos) (Vconst (id_matrix dim) n).

  (** [fun_of_pairs_matrix_list] is a representation for an
     interpretation associating to every function symbol of arity [n],
     an natural matrix with [n] variables. It is represented by a list
     of pairs [(g, mi)], where [g] is a function symbol and [mi] is
     its interpretation. *)
  
  Section fun_of_pairs_matrix_list.

    Variable f : symbol.
    
    Fixpoint fun_of_matrix_nat_list (l : list {g: symbol & mint (arity g)})
      : mint (arity f) :=
      match l with
        | existT g m :: l' =>
          match @eq_symb_dec Sig g f with
            | left h => matrix_cast_nat (f_equal arity h) m
            | right _ => fun_of_matrix_nat_list l'
          end 
        | nil => default_matrix_nat (arity f)
      end.
    
  End fun_of_pairs_matrix_list.

  (****************************************************************************)
  (** ** Matrix interpretation in the setting of monotone
     algebras. CoLoR library for proving matrix interpretation over natural
     numbers used [Module] and [Functor]. Modules cannot be defined
     inside sections, also module in Coq is not a first-class module like
     in OCaml. These files are redefine and reproof from CoLoR library for
     matrix interpretation use [Record] instead. *)
  
  Section MatrixMethodConf_Nat.

    Variable l : list {g : symbol & mint (arity g)}.

    Definition trsInt_nat (f : Sig) := fun_of_matrix_nat_list f l.

    Definition TMatrixInt := mkMatrixMethodConf Sig trsInt_nat.

    Definition Matrix_MonoAlgType := matAlg TMatrixInt.

    (** Weak reduction pair for matrix intepretration. *)

    Definition Matrix_WeakRedPair := bwrp Matrix_MonoAlgType.
  
    (** Reduction pair associcated to a monotone algebra. *)

    Definition matrix_wrp := mkbWeakRedPair (wf_succ Matrix_WeakRedPair)
      (sc_succ Matrix_WeakRedPair)(bsucc_sub Matrix_WeakRedPair)
      (sc_succeq Matrix_WeakRedPair) (cc_succeq Matrix_WeakRedPair)
      (ARedPair2.refl_succeq Matrix_WeakRedPair)
      (ARedPair2.succ_succeq_compat Matrix_WeakRedPair)
      (bsucceq_sub Matrix_WeakRedPair) (ARedPair2.trans_succ Matrix_WeakRedPair)
    (ARedPair2.trans_succeq Matrix_WeakRedPair).

    (* FIXME: this proof can cause the problem of axiom after extraction *)
    (* TODO : finish proof of monontone in default_matrix *)
    
    (** Proving monotone of default matrix interpretation. The
       restriction on the interpretation to be monotone is that their
       upper left elements [Mi(1,1)] are positive for all matrices [Mi]
       for [i = 1, ..., n] for every [f \in F] with [arity (f) = n].
       This proof is easy to proof because the [id_matrix] and
       [id_vector] has [1>0] at the upper left elements [Mi(1,1) = 1 >
       0]. *)   

    Variable H1: forallb (fun x : {f : symbol & matrixInt matrix dim (arity f)} =>
      let (f, mi) := x in bVforall
        (fun m : matrix dim dim => bgt_nat (get_elem m dim_pos dim_pos) 0)
        (args mi)) l = true.
    
    Lemma matrix_nat_monotone_default : forall f: Sig,
      monotone_interpretation (default_matrix_nat (arity f)).
      
    Proof.
      intros. unfold default_matrix_nat. unfold monotone_interpretation.
      apply Vforall_intro; simpl in *.
      intros.
      unfold id_matrix in H. unfold id_vec in H.
      unfold A1N in H.
      unfold zero_vec in H. unfold A0N in H.
      unfold get_elem. unfold get_row. simpl in *.
      apply Vin_nth in H.
      
      (*      apply Vforall_intro; simpl in *. 
      intros M H.
      unfold get_elem.
      eapply Vforall_eq.
      apply Vforall_intro.
      intros.*)
    Admitted.

    (*Variable H1: forallb (fun x : {f : symbol & matrixInt matrix dim (arity f)} =>
      let (f, mi) := x in bVforall
        (fun m : matrix dim dim => bgt_nat (get_elem m dim_pos dim_pos) 0)
        (args mi)) l = true. *)
    
    Lemma trsInt_nat_mon : forall f, monotone_interpretation (trsInt_nat f).
    Proof.
      intro f. unfold trsInt_nat. unfold fun_of_matrix_nat_list. 
      induction l; simpl in *; try discr.  
      (* Default matrix monotone *)
      apply matrix_nat_monotone_default.
      simpl in *.
      destruct a as [g]; try discr.
      destruct (@eq_symb_dec Sig g f).
      (* g = f *)
      unfold matrix_cast_nat. simpl_eq.
      rewrite andb_eq in H1. destruct H1.
      rewrite <- bmonotone_interpretation_ok.
      unfold bmonotone_interpretation. hyp.
      (* g <> f *)
      apply IHl0.
      rewrite andb_eq in H1.
      destruct H1. hyp.
    Qed.

  End MatrixMethodConf_Nat.

  (****************************************************************************)
  (** ** Boolean functions for matrix interpretation over domain natural
   numbers. *)
  
  Section BoolMint_Nat.
    
    (** Matrix orders, we define orders [ge(>=)] and [gt(>)] on [A = N^d] as follows:
       [(u1, ..., ud) >= (v1, ..., vd) <=> \forall i, ui >=_Nat vi
       (mint_ge)
       (u1, ..., ud) > (v1, ..., ud) <=> (u1, ..., ud) >= (v1, ...,
       vd) /\ u1 >_Nat v1 (mint_gt)]
       
       where [>=_Nat] and [>_Nat]: are orders over natural numbers. *)

    (** Define boolean function of [mat_ge]/ *)

    Definition bmat_ge (m n: nat) (M N: matrix m n) :=
      match mat_ge_dec M N with
        | left _ => true (* M >=m N *)
        | right _ => false (* ~ M >=m N *)
      end.

    (** Correctness proof of [bmat_ge]. *)
    
    Lemma bmat_ge_ok : forall (m n: nat) (M N: matrix m n),
                         bmat_ge M N = true <-> mat_ge M N.
    Proof.
      intros m n M N. unfold bmat_ge.
      case_eq (mat_ge_dec M N); intuition.
    Qed.

    (** Define boolean function for [mint_ge]. *)
    (* Let matrices [M, N \in A^dxd], and vectors [x, y \in A^d].
       If [M >= N and x >= y] then [Mx >= My] *)

    Definition bmint_ge n (l r : mint n) : bool :=
      bVforall2n (bmat_ge (n:=dim))(args l) (args r) &&
      bVforall2n (fun m n => bge_nat m n) (const l) (const r).

    (** Correctness proof of [bmint_ge] over domain natural numbers. *)
    
    Lemma bmint_ge_ok : forall n (l r: mint n),
      bmint_ge l r = true <-> mint_ge l r.
      
    Proof.
      intros n l r. intuition. 
      (* [1]. Proving the <- *)
      unfold bmint_ge in H. rewrite andb_eq in H. destruct H.
      unfold mint_ge. split.
      (* Left part. *)
      rewrite bVforall2n_ok in H. apply H.
      (* Proving boolean function of [bmat_ge]. *)
      intros M N. split.
      (* -> *)
      intro H1. apply bmat_ge_ok. hyp.
      (* <- *)
      intro H1. rewrite bmat_ge_ok. hyp.
      (* Right part. *)
      rewrite bVforall2n_ok in H0. apply H0.
      (* Proving boolean function of [bge]. *)
      intros x y. split.
      (* -> *)
      intro H1. apply bge_nat_ok. hyp.
      (* <- *)
      intro H1. rewrite bge_nat_ok. hyp.
      (* [2]. Proving the -> *)
      unfold bmint_ge. rewrite andb_eq. split.
      (* Left part. *)
      rewrite bVforall2n_ok. unfold mint_ge in H.
      destruct H. apply H.
      (* Proving boolean function of [bmat_ge]. *)
      intros M N. split.
      (* -> *)
      intro H1. apply bmat_ge_ok. hyp.
      (* <- *)
      intro H1. rewrite bmat_ge_ok. hyp.
      (* Right part. *)
      rewrite bVforall2n_ok. unfold mint_ge in H.
      destruct H. apply H0.
      (* Proving boolean function of [bge]. *)
      intros x y. split.
      (* -> *)
      intro H1. apply bge_nat_ok. hyp.
      (* <- *)
      intro H1. rewrite bge_nat_ok. hyp.
    Qed.

    (** Define boolean function for [mint_gt] over domain natural numbers. *)
    (** Let matrices [M, N \in A^dxd], and vectors [x, y \in A^d].
       If [M >= N and x > y] then [Mx > My] *)

    Definition bmint_gt n (l r : mint n) : bool :=
      bmint_ge l r && (bgt_nat (vec_at0 (const l)) (vec_at0 (const r))).
    
    (** Correctness proof of [bmint_gt] over domain natural numbers. *)

    Lemma bmint_gt_ok : forall n (l r : mint n),
      bmint_gt l r = true <-> mint_ge l r /\
      vec_at0 (const l) > vec_at0 (const r).
    
    Proof.
      intros. intuition. apply bmint_ge_ok. unfold bmint_gt in H.
      rewrite andb_eq in H. destruct H. apply H.
      unfold bmint_gt in H. rewrite andb_eq in H.
      destruct H. apply bgt_nat_ok in H0. apply H0.
      (* -> *)
      unfold bmint_gt. rewrite andb_eq. split.
      apply bmint_ge_ok. apply H0.
      apply bgt_nat_ok. apply H1.
    Qed.
    
  End BoolMint_Nat.

End S.