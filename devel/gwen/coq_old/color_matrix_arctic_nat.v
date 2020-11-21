(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2013-04-18

* Matrix interpretation over domain arctic natural numbers

*)

Set Implicit Arguments.

Require Import ATrs ARedPair2 APolyInt_MA2 AMonAlg2 LogicUtil BoolUtil
  AMatrixBasedInt2_ArcticNat VecUtil VecArith2 Matrix2 cpf2color cpf
  OrdSemiRing2 VecOrd cpf_util List AArcticInt2 AArcticBasedInt2
  Equality .

(***********************************************************************)
(** ** Matrix interpretation over domain arctic natural numbers, the main
different with matrix interpretation over natural numbers is that we
want to use the arctic semiring for the underlying algebra operations. *)

Section S.
  
  Variable arity: symbol -> nat.
  Variable dim : nat.

  Notation Sig := (Sig arity).
  Notation dim_pos := (dim_pos dim).
  Notation mint := (matrixInt_arcnat matrix_arcnat dim).

  (** Cast *)

  Definition matrix_cast_arcnat n m (Heq: n = m)(p: mint n) : mint m.
  rewrite <- Heq; auto.
  Defined.

  (** Default of matrix interpretation over arctic natural numbers. *)
  
  (* In Arctic natural numbers semi-ring define: A0 = minusInf, A1 = Pos 0,
     for example the (2 x 2) identity matrix is:
     |Pos 0    minusInf|
     |minusInf    Pos 0| *)

  Definition default_matrix_arcnat (n: nat) :=
    mkMatrixInt_arcnat (id_vec_arcnat dim_pos)
    (Vconst (id_matrix_arcnat dim) n).

  (** [fun_of_pairs_matrix_arcnat_list] is a representation for an
     interpretation associating to every function symbol of arity [n],
     an natural matrix with [n] variables. It is represented by a list
     of pairs [(g, mi)], where [g] is a function symbol and [mi] is its
     interpretation. *)

  Section fun_of_pairs_matrix_arcnat_list.
  
    Variable f : symbol.

    Fixpoint fun_of_matrix_arcnat_list (l : list {g: symbol & mint (arity g)})
      : mint (arity f) :=
      match l with
        | existT g m :: l' =>
          match @eq_symb_dec Sig g f with
            | left h => matrix_cast_arcnat (f_equal arity h) m
            | right _ => fun_of_matrix_arcnat_list l'
          end 
        | nil => default_matrix_arcnat (arity f)
      end.
    
  End fun_of_pairs_matrix_arcnat_list.

  (***********************************************************************)
  (** ** Matrix interpretation in the setting of monotone algebras. *)

  Section MatrixMethodConf_Arcnat.

    Variable l : list {g : symbol & mint (arity g)}.

    Definition trsInt_arcnat (f : Sig) := fun_of_matrix_arcnat_list f l.

    Definition TMatrixInt_arcnat :=
      mkMatrixMethodConf_arcnat Sig trsInt_arcnat.

    Definition MatrixArcnat_MonoAlgType := matAlg_arcnat TMatrixInt_arcnat.

    (** Weak reduction pair for matrix intepretration. *)

    Definition MatrixArcnat_WeakRedPair := bwrp MatrixArcnat_MonoAlgType.
  
    (** Reduction pair associcated to a monotone algebra. *)

    Definition matrix_arcnat_wrp := mkbWeakRedPair (wf_succ
      MatrixArcnat_WeakRedPair) (sc_succ
      MatrixArcnat_WeakRedPair)(bsucc_sub MatrixArcnat_WeakRedPair)
      (sc_succeq MatrixArcnat_WeakRedPair) (cc_succeq
      MatrixArcnat_WeakRedPair) (ARedPair2.refl_succeq
      MatrixArcnat_WeakRedPair) (ARedPair2.succ_succeq_compat
      MatrixArcnat_WeakRedPair) (bsucceq_sub MatrixArcnat_WeakRedPair)
      (ARedPair2.trans_succ MatrixArcnat_WeakRedPair)
      (ARedPair2.trans_succeq MatrixArcnat_WeakRedPair).
    
  End MatrixMethodConf_Arcnat.
  
  (****************************************************************************)
  (** ** Boolean function for matrix interpretation over domain arctic
   natural numbers *)

  Section BoolMint_Arcnat.

    Definition bgt_arc (m n: ArcticDom) :=
      match gt_decr m n with
        | left _ => true (* {m > n} *)
        | right _ => false (* {~ m > n} *)
      end.
    
    (** Correctness proof of [bgt] in arctic naturals domain. *)

    Lemma bgt_arc_ok : forall m n, bgt_arc m n = true <-> gtr m n.

    Proof.
      intros. unfold bgt_arc.
      case_eq (gt_decr m n); intuition.
    Qed.
    
    (** Define boolean function of [ge] over domain arctic natural numbers. *)
    
    Definition bge_arc (m n: ArcticDom) := bgt_arc m n || beq_ArcticDom m n.
    
    (** Correctness proof of [bge] over domain arctic natural numbers. *)
    
    Lemma bge_arc_ok : forall m n, bge_arc m n = true <-> ger m n.
      
    Proof.
      intros n m. intuition. unfold ger.
      unfold bge_arc in H. rewrite orb_eq in H.
      destruct H; try discr.
      apply bgt_arc_ok in H. left. apply H.
      apply beq_ArcticDom_ok in H. right. apply H.
      (* -> *)
      unfold ger in H. destruct H.
      unfold bge_arc. rewrite orb_eq.
      left. rewrite bgt_arc_ok. apply H.
      unfold bge_arc. rewrite orb_eq.
      right. rewrite beq_ArcticDom_ok. apply H.
    Qed.

    (** Define a boolean function of [mat_ge]. *)

    Definition bmat_ge_arcnat (m n : nat) (M N : matrix_arcnat m n) :=
      match mat_ge_dec_arcnat M N with
        | left _ => true  (* M >=m N *)
        | right _ => false (* ~ M >=m N *)
      end.

    (** Correctness prove of [bmat_ge].  *)

    Lemma bmat_ge_arcnat_ok: forall (m n : nat) (M N : matrix_arcnat m n),
                               bmat_ge_arcnat M N = true <-> mat_ge_arcnat M N.

    Proof.
      intros m n M N. unfold bmat_ge_arcnat.
      case_eq (mat_ge_dec_arcnat M N); intuition.
    Qed.

    (** Define boolean function for [mint_ge] over domain arctic natural numbers. *)
    (* Let matrices [M, N \in A^dxd], and vectors [x, y \in A^d].
       If [M >= N and x >= y] then [Mx >= My] *)

    Definition bmint_arc_ge n (l r : mint n) : bool :=
      bVforall2n (bmat_ge_arcnat (n := dim)) (args_arcnat l) (args_arcnat r) &&
      bVforall2n (fun m n => bge_arc m n) (const_arcnat l) (const_arcnat r).

    (** Correctness proof of [bmint_ge] in arctic naturals domain. *)
    
    Lemma bmint_arc_ge_ok : forall n (l r: mint n),
      bmint_arc_ge l r = true <-> mint_ge_arcnat l r.

    Proof.
      intros n l r. intuition.
      (*[1]. Proving the <- *)
      unfold mint_ge_arcnat. unfold bmint_arc_ge in H.
      rewrite andb_eq in H. destruct H.
      split. rewrite bVforall2n_ok in H. apply H.
      (* Proving boolean function of [bmat_ge_arcnat]. *)
      intros M N. split.
      (* -> *)
      intro H1. rewrite bmat_ge_arcnat_ok in H1. hyp.
      (* <- *)
      intro H1. rewrite bmat_ge_arcnat_ok. hyp.
      (* Proving the second part of && [const_arcnat]. *)
      rewrite bVforall2n_ok in H0. apply H0.
      (* Proving boolean function of [bge_arc]. *)
      intros x y. split.
      (* -> *)
      intro H1. apply bge_arc_ok. hyp.
      (* <- *)
      intro H1. rewrite bge_arc_ok. hyp.
      (* [2]. Proving the other ways -> *)
      unfold bmint_arc_ge. rewrite andb_eq. split.
      (* Proving the first part of && [bmat_ge_arcnat]. *)
      rewrite bVforall2n_ok. unfold mint_ge_arcnat in H.
      destruct H. apply H.
      (* Proving the boolean function of [bmat_ge_arcnat]. *)
      intros M N. split.
      (* -> *)
      intro H1. apply bmat_ge_arcnat_ok. hyp.
      (* <- *)
      intro H1. rewrite bmat_ge_arcnat_ok. hyp.
      (* Proving the second part of && [const_arcnat]. *)
      rewrite bVforall2n_ok. unfold mint_ge_arcnat in H.
      destruct H. apply H0.
      (* Proving the boolean function of [bge_arc]. *)
      intros x y. split.
      (* -> *)
      intro H1. apply bge_arc_ok. hyp.
      (* <- *)
      intro H1. rewrite bge_arc_ok. hyp.
    Qed.
    
    (** Define boolean function of [gtx] over domain arctic natural
       numbers. Arctic addition is not strictly monotone in single
       arguments. It is, however, "haft strict" in the following
       sense: a strict increase in both arguments simultaneously gives
       a strict increase in the result. There is one exception: arctic
       addition is obviously strict if one argument is arctic zero,
       i.e., [-oo]. This is the motivation for introducing the
       following relation [gtx].

       NOTE: arctic addition is strict if one argument is [arctic zero:
       -oo (A0/MinusInf)]; relation [gtx: a >> b <-> (a > b) \/ (a = b =
       -oo]. *)

    Definition bgtx (x y: ArcticDom) : bool := 
      bgt_arc x y || beq_ArcticDom x MinusInf && beq_ArcticDom y MinusInf.

    (* Correctness proof of [bgtx]. *)
    
    Lemma bgtx_ok : forall x y, bgtx x y = true <-> gtx x y.
    Proof.
      intros x y. split.
      (* -> *)
      intro H. unfold bgtx in H.
      rewrite orb_eq in H. rewrite andb_eq in H. 
      destruct H.
      (* Proving the correctness of [bgt]. Left part *)
      rewrite bgt_arc_ok in H. unfold gtx.
      left. hyp.
      (* Right part. *)
      destruct H.
      unfold gtx. right.
      rewrite beq_ArcticDom_ok in H. rewrite beq_ArcticDom_ok in H0. auto.
      (* <- *)
      intro H. unfold gtx in H. destruct H.
      unfold bgtx.
      rewrite orb_eq. rewrite andb_eq. left.
      (* Left part. *)
      rewrite bgt_arc_ok. hyp.
      (* Right part. *)
      unfold eqAr in H. unfold A0r in H. destruct H.
      unfold bgtx. rewrite orb_eq. rewrite andb_eq.
      right. split.
      rewrite beq_ArcticDom_ok. hyp.
      rewrite beq_ArcticDom_ok. hyp.
    Qed.

    (** Define boolean function of [mat_gt]. *)
    
    Definition bmat_gt_arcnat (M N: matrix_arcnat dim dim) :=
      match mat_gt_dec M N with
          | left _ => true (* M >=m N *)
          | right _ => false (* ~ M >=m N *)
      end.
    
    (** Correctness proof of [bmat_gt]. *)
    
    Lemma bmat_gt_arcnat_ok : forall (M N : matrix_arcnat dim dim),
                                bmat_gt_arcnat M N = true <-> mat_gt M N.
    Proof.
      intros M N. unfold bmat_gt_arcnat.
      case_eq (mat_gt_dec M N); intuition.
    Qed.

    (** Define boolean function for [mint_gt] over domain arctic natural numbers. *)
    (* Let matrices [M, N \in A^dxd], and vectors [x, y \in A^d].
       If [M >> N and x >> y] then [Mx >> My] *)

    Definition bmint_arc_gt n (l r : mint n) : bool :=
      bVforall2n bmat_gt_arcnat (args_arcnat l) (args_arcnat r) &&
      bVforall2n (fun m n => bgtx m n) (const_arcnat l) (const_arcnat r).

    (** Correctness proof of [bmint_gt] in arctic naturals domain. *)

    Lemma bmint_arc_gt_ok : forall n (l r : mint n),
      bmint_arc_gt l r = true <-> Vforall2n (mat_gt (dim:=dim))
      (args_arcnat l) (args_arcnat r)
      /\ vec_gt (const_arcnat l) (const_arcnat r).
    
    Proof.
      intros n l r. intuition.
      (* [1] <- *)
      unfold bmint_arc_gt in H. rewrite andb_eq in H. destruct H.
      rewrite <- bVforall2n_ok. apply H.
      (* Proving boolean function of [bmat_gt]. *)
      intros M N. split.
      (* -> *)
      intro H1. apply bmat_gt_arcnat_ok. hyp.
      (* <- *)
      intro H1. rewrite bmat_gt_arcnat_ok. hyp.
      (* Proving [const_arcnat]. *)
      unfold bmint_arc_gt in H.
      rewrite andb_eq in H. destruct H.
      rewrite bVforall2n_ok in H0. apply H0.
      (* Proving the boolean function of [bgtx]. *)
      intros x y. split.
      (* -> *)
      intro H1. apply bgtx_ok. hyp.
      (* <- *)
      intro H1. rewrite bgtx_ok. hyp.
      (* [2]. -> *)
      unfold bmint_arc_gt. rewrite andb_eq.
      split.
      (* Left part. *)
      rewrite bVforall2n_ok. apply H0.
      (* Proving boolean function of [bmat_gt]. *)
      intros M N. split.
      (* -> *)
      intro H. apply bmat_gt_arcnat_ok. hyp.
      (* <- *)
      intro H. rewrite bmat_gt_arcnat_ok. hyp.
      (* Right part. *)
      rewrite bVforall2n_ok. apply H1.
      (* Proving boolean function of [bgtx]. *)
      intros x y. split.
      (* -> *)
      intro H. unfold bgtx in H. rewrite orb_eq in H. rewrite andb_eq in H.
      destruct H.
      unfold gtx.
      (* Left part. *)
      left. apply bgt_arc_ok. hyp.
      (* Right part. *)
      unfold gtx. right.
      unfold eqAr, A0r.
      destruct H. rewrite beq_ArcticDom_ok in H.
      rewrite beq_ArcticDom_ok in H2. auto.
      (* <- *)
      intro H. rewrite bgtx_ok. hyp.
    Qed.
    
  End BoolMint_Arcnat.

End S.