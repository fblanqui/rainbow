(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2013-04-18

* Matrix interpretation over domain arctic integer numbers - below zero

*)

Set Implicit Arguments.

Require Import ATrs ARedPair2 APolyInt_MA2 AMonAlg2 Equality
  AArcticBZInt2 ListForall ListUtil LogicUtil BoolUtil ZUtil
  AMatrixBasedInt2_ArcticBZ VecUtil VecArith2 Matrix2 cpf2color cpf
  OrdSemiRing2 VecOrd cpf_util AArcticBasedInt2.

(***********************************************************************)
(** ** Matrix interpretation over domain arctic integer numbers -
   below zero. *)

Section S.

  Variable arity: symbol -> nat.
  Variable dim : nat.

  Notation Sig := (Sig arity).
  Definition dim_pos := (dim_pos dim).
  Notation mint := (matrixInt_arcbz matrix_arcbz dim).

  (** Cast *)

  Definition matrix_cast_arcbz n m (Heq: n = m)(p: mint n) : mint m.
  rewrite <- Heq; auto.
  Defined.

  (** Default matrix interpretation over domain arctic integer numbers. *)

  Definition default_matrix_arcbz (n : nat) :=
    mkMatrixInt_arcbz (id_vec_arcbz dim_pos) (Vconst (id_matrix_arcbz dim) n).

  (** [fun_of_pairs_matrix_arcbz_list] is a representation for an interpretation
     associating to every function symbol of arity [n], an natural matrix
     with [n] variables. It is represented by a list of pairs [(g, mi)],
     where [g] is a function symbol and [mi] is its interpretation. *)
  
  Section fun_of_pairs_matrix_arcbz_list.

    Variable f : symbol.
    
    Fixpoint fun_of_matrix_arcbz_list (l : list {g: symbol & mint (arity g)})
      : mint (arity f) :=
      match l with
        | existT g m :: l' =>
          match @eq_symb_dec Sig g f with
            | left h => matrix_cast_arcbz (f_equal arity h) m
            | right _ => fun_of_matrix_arcbz_list l'
          end 
        | nil => default_matrix_arcbz (arity f)
      end.
    
  End fun_of_pairs_matrix_arcbz_list.

(***********************************************************************)
(** ** Matrix interpretation in the setting of monotone algebras. *)

  Section MatrixMethodConf_Arcbz.

    Variable l : list {g : symbol & mint (arity g)}.

    Definition trsInt_arcbz (f : Sig) := fun_of_matrix_arcbz_list f l.

    Definition TMatrixInt_arcbz := mkMatrixMethodConf_arcbz Sig trsInt_arcbz.

    Definition MatrixArcbz_MonoAlgType := matAlg_arcbz TMatrixInt_arcbz.

    (** Weak reduction pair for matrix intepretration. *)

    Definition MatrixArcbz_WeakRedPair := bwrp MatrixArcbz_MonoAlgType.
  
    (** Reduction pair associcated to a monotone algebra. *)

    Definition matrix_arcbz_wrp := mkbWeakRedPair
      (wf_succ MatrixArcbz_WeakRedPair)
      (sc_succ MatrixArcbz_WeakRedPair)(bsucc_sub MatrixArcbz_WeakRedPair)
      (sc_succeq MatrixArcbz_WeakRedPair) (cc_succeq MatrixArcbz_WeakRedPair)
      (ARedPair2.refl_succeq MatrixArcbz_WeakRedPair)
      (ARedPair2.succ_succeq_compat MatrixArcbz_WeakRedPair)
      (bsucceq_sub MatrixArcbz_WeakRedPair)
      (ARedPair2.trans_succ MatrixArcbz_WeakRedPair)
      (ARedPair2.trans_succeq MatrixArcbz_WeakRedPair).

  End MatrixMethodConf_Arcbz.

  (****************************************************************************)
  (** ** Boolean function for matrix interpretation over domain arctic
     integer numbers *)
  
  Section BoolMint_arcbz.
  
    Local Open Scope Z_scope.
    
    (** Define boolean function for [gt] over domain arctic integer
       numbers/below-zero. *)

    Definition bgt_arc_bz m n :=
      match gt_decrbz m n with
        | left _ => true
        | right _ => false
      end.

    Notation "x >> y" := (gtrbz x y) (at level 70).
    
    (** Correcntess proof of [bgt] over domain arctic below-zero. *)

    Lemma bgt_arc_bz_ok : forall m n, bgt_arc_bz m n = true <-> (m >> n)%Z.

    Proof.
      intros. unfold bgt_arc_bz.
      case_eq (gt_decrbz m n); intuition.
    Qed.
  
    (** Define boolean function for [ge] over domain arctic integer
    numbers/below-zero. *)

    Definition bge_arc_bz m n := bgt_arc_bz m n || beq_ArcticBZDom m n.
    
    (** Correctness proof of [bge] in arctic below-zero. *)

    Lemma bge_arc_bz_ok : forall m n, bge_arc_bz m n = true <-> gerbz m n.

    Proof.
      intros m n. intuition.
      unfold gerbz. unfold bge_arc_bz in H. rewrite orb_eq in H.
      destruct H; try discr.
      apply bgt_arc_bz_ok in H. left. apply H.
      apply beq_ArcticBZDom_ok in H. right. apply H.
      (* -> *)
      unfold gerbz in H. destruct H.     
      unfold bge_arc_bz. rewrite orb_eq.
      left. rewrite bgt_arc_bz_ok. apply H.
      unfold bge_arc_bz. rewrite orb_eq.
      right. rewrite beq_ArcticBZDom_ok. apply H.
    Qed.

    (** Define boolean function of [mat_ge] *)

    Definition bmat_ge_arcbz (m n : nat)(M N: matrix_arcbz m n) :=
      match mat_ge_dec_arcbz M N with
        | left _ => true (* M >=m N *)
        | right _ => false (* ~ M >=m N *)
      end.
   
    (** Correctness proof of mat_ge_arcbz and [bmat_ge]. *)
    
    Lemma bmat_ge_arcbz_ok : forall (m n: nat) (M N: matrix_arcbz m n), 
                               bmat_ge_arcbz M N = true <-> mat_ge_arcbz M N.
    Proof.
      intros. unfold bmat_ge_arcbz.
      case_eq (mat_ge_dec_arcbz M N); intuition.
    Qed.

    (** Define boolean function of [mint_ge] over domain arctic
    integer numbers/below-zero. *)

    Definition bmint_arc_bz_ge n (l r : mint n) : bool :=
      bVforall2n (bmat_ge_arcbz (n:= dim)) (args_arcbz l) (args_arcbz r)
    && bVforall2n (fun m n => bge_arc_bz m n) (const_arcbz l) (const_arcbz r).

    (** Correctness proof of [bmint_ge] over domain arctic integer
      numbers/below-zero. *)

    Lemma bmint_arc_bz_ge_ok: forall n (l r: mint n),
      bmint_arc_bz_ge l r = true <-> mint_ge_arcbz l r.
    
    Proof.
      intros n l r. intuition.
      (* [1]. Proving the <- *)
      unfold bmint_arc_bz_ge in H.
      rewrite andb_eq in H. destruct H.
      rewrite bVforall2n_ok in H. unfold mint_ge_arcbz.
      split. apply H.
      rewrite bVforall2n_ok in H0. apply H0.
      (* Proving boolean function of [bge]. *)
      intros. split.
      (* -> *)
      intro H1. apply bge_arc_bz_ok in H1. hyp.
      (* <- *)
      intro H1. rewrite bge_arc_bz_ok. hyp.
      (* Proving boolean function of [bmat_ge]*)
      intros. split.
      (* -> *)
      intro H1. rewrite bmat_ge_arcbz_ok in H1.
      hyp.
      (* <- *)
      intro H1. apply bmat_ge_arcbz_ok. hyp.
      (* [2]. Proving the other -> *)
      unfold bmint_arc_bz_ge. rewrite andb_eq.
      split. rewrite bVforall2n_ok.
      unfold mint_ge_arcbz in H. destruct H.
      apply H. intros.
      (* -> *)
      split. intro H1. apply bmat_ge_arcbz_ok. hyp.
      (* <- *)
      intro H1. apply bmat_ge_arcbz_ok. hyp.
      (* Proving boolean function of [const_arcbz]. *)
      rewrite bVforall2n_ok. unfold mint_ge_arcbz in H.
      destruct H. apply H0.
      (* Proving boolean function of [bge_arc]. *)
      intros. split. 
      (* -> *)
      intro H1. apply bge_arc_bz_ok. hyp.
      (* <- *)
      intro H1. rewrite bge_arc_bz_ok. hyp.
    Qed.
    
    (** Define boolean function for [gtx] in Arctic below-zero domain
       arctic addition is not strictly monotone in single
       arguments. It is, however, "haft strict" in the following sense:
       a strict increase in both arguments simultaneously gives a strict
       increase in the result. There is one exception: arctic addition
       is obviously strict if one argument is arctic zero, i.e.,
       [-oo]. This is the motivation for introducing the following
       relation [gtx]. *)
    
    Definition bgtxbz (x y: ArcticBZDom) : bool := 
      bgt_arc_bz x y || beq_ArcticBZDom x MinusInfBZ
        && beq_ArcticBZDom y MinusInfBZ.
  
    (** Correctness proof of [bgtxbz] *)

    Lemma bgtxbz_ok : forall x y, bgtxbz x y = true <-> gtx_bz x y.
    Proof.
      intros. intuition.
      unfold gtx_bz. unfold bgtxbz in H.
      rewrite orb_eq in H. rewrite andb_eq in H.
      destruct H; try discr.
      apply bgt_arc_bz_ok in H.
      (* Left part. *)
      left. hyp.
      destruct H. apply beq_ArcticBZDom_ok in H.
      apply beq_ArcticBZDom_ok in H0.
      (* Right part. *)
      right. auto.
      unfold gtx_bz in H. destruct H.
      unfold bgtxbz. rewrite orb_eq. rewrite andb_eq.
      (* Left part. *)
      left. rewrite bgt_arc_bz_ok. hyp.
      unfold bgtxbz. rewrite orb_eq. rewrite andb_eq.
      (* Right part. *)
      right. split. rewrite beq_ArcticBZDom_ok. destruct H.
      auto. rewrite beq_ArcticBZDom_ok. destruct H.
      auto.
    Qed.
   
    (** Define boolean function of [mat_gt]. *)

    Require Import AArcticBasedInt2.

    Definition bmat_gt_arcbz (M N:  matrix_arcbz dim dim)  :=
      match mat_gt_decbz M N with
        | left _ => true
        | right _ => false
      end.

    (** Correctness proof of [bmat_gt]. *)

    Lemma bmat_gt_arcbz_ok : forall (M N:  matrix_arcbz dim dim),
                               bmat_gt_arcbz M N = true <-> mat_gtbz M N.
    Proof.
      intros. unfold bmat_gt_arcbz.
      case_eq (mat_gt_decbz M N); intuition.
    Qed.

    (** Define boolean function for [mint_gt] over domain arctic
       integer numbers/below-zero. *)

    Definition bmint_arc_bz_gt n (l r : mint n) : bool :=
      bVforall2n bmat_gt_arcbz (args_arcbz l) (args_arcbz r) &&
      bVforall2n (fun m n => bgtxbz m n) (const_arcbz l) (const_arcbz r).

    (** Correctness proof of [bmint_gt] over domain arctic integer
       numbers/below-zero. *)

    Lemma bmint_arc_bz_gt_ok : forall n (l r : mint n),
      bmint_arc_bz_gt l r = true <-> Vforall2n (mat_gtbz (dim:=dim))
      (args_arcbz l) (args_arcbz r)
      /\ vec_gtbz (const_arcbz l) (const_arcbz r).

    Proof.
      intros n l r. intuition.
      (* Left part. *)
      unfold bmint_arc_bz_gt in H. rewrite andb_eq in H.
      destruct H. rewrite <- bVforall2n_ok. apply H.
      intros. split. intro H1. apply bmat_gt_arcbz_ok. hyp.
      intro H1. rewrite bmat_gt_arcbz_ok. hyp.
      (* Right part. *)
      unfold vec_gtbz.
      unfold bmint_arc_bz_gt in H. 
      rewrite andb_eq in H. destruct H.
      rewrite bVforall2n_ok in H0. apply H0.
      (* Boolean function of [bgtx]. *)
      intros. split. intro H1.
      apply bgtxbz_ok. hyp.
      intro H1. rewrite bgtxbz_ok. hyp.
      (* Boolean function of [bmint_gt]. *)
      unfold bmint_arc_bz_gt. rewrite andb_eq. split.
      rewrite bVforall2n_ok. apply H0. 
      intros. split. intro H2. apply bmat_gt_arcbz_ok. hyp.
      intro H2. rewrite bmat_gt_arcbz_ok. hyp.
      (* Second part. *)
      rewrite bVforall2n_ok. apply H1.
      intros. split. intro H2. apply bgtxbz_ok. hyp.
      intro H2. rewrite bgtxbz_ok. hyp.
    Qed.
    
  End BoolMint_arcbz.

End S.