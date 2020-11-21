(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2013-04-18

* Matrix interpretation over domain tropical

*)

Set Implicit Arguments.

Require Import ATrs ARedPair2 APolyInt_MA2 AMonAlg2 Equality
  ATropicalInt2 ListForall ListUtil ZUtil LogicUtil BoolUtil
  AMatrixBasedInt2_Trop VecUtil VecArith2 AMatrixInt2 cpf2color
  cpf OrdSemiRing2 Matrix2 cpf_util.

(***********************************************************************)
(** ** Matrix interpretation over domain tropical. *)

Section S.

  Variable arity: symbol -> nat.
  Variable dim : nat.

  Notation Sig := (Sig arity).
  Notation dim_pos := (dim_pos dim).
  Notation mint := (matrixInt_trop matrix_trop dim).

  (** Cast *)

  Definition matrix_cast_trop n m (Heq: n = m)(p: mint n) : mint m.
  rewrite <- Heq; auto.
  Defined.

  (** Default matrix interpretation over domain tropical. *)

  Definition default_matrix_trop (n: nat) :=
    mkMatrixInt_trop (id_vec_trop dim_pos) (Vconst (id_matrix_trop dim) n).

  (** [fun_of_pairs_matrix_trop_list] is a representation for an interpretation
     associating to every function symbol of arity [n], an natural matrix
     with [n] variables. It is represented by a list of pairs [(g, mi)],
     where [g] is a function symbol and [mi] is its interpretation. *)
  
  Section fun_of_pairs_matrix_trop_list.

    Variable f : symbol.

    Fixpoint fun_of_matrix_trop_list (l : list {g: symbol & mint (arity g)})
      : mint (arity f) :=
      match l with
        | existT g m :: l' =>
          match @eq_symb_dec Sig g f with
            | left h => matrix_cast_trop (f_equal arity h) m
            | right _ => fun_of_matrix_trop_list l'
          end 
        | nil => default_matrix_trop (arity f)
      end.
    
  End fun_of_pairs_matrix_trop_list.

  (***********************************************************************)
  (** ** Matrix interpretation in the setting of monotone algebras. *)
  
  (*Require Import ARedPair2 APolyInt_MA2 AMonAlg2 Equality ATropicalInt2.*)
  
  Section matrixMethodConf_trop.

    Variable l : list {g : symbol & mint (arity g)}.

    Notation "x >> y" := (gtt x y) (at level 70).

    Variable A0_gt_A1 : A0t >> A1t.

    Definition trsInt_trop (f : Sig) := fun_of_matrix_trop_list f l.

    Definition TMatrixInt_trop := mkMatrixMethodConf_trop Sig trsInt_trop.

    Definition MatrixTrop_MonoAlgType := matAlg_trop TMatrixInt_trop.

    (** Weak reduction pair for matrix intepretration. *)

    Definition MatrixTrop_WeakRedPair := bwrp MatrixTrop_MonoAlgType.
  
    (** Reduction pair associcated to a monotone algebra. *)
    
    Definition matrix_trop_wrp := mkbWeakRedPair
      (wf_succ MatrixTrop_WeakRedPair)
      (sc_succ MatrixTrop_WeakRedPair)(bsucc_sub MatrixTrop_WeakRedPair)
      (sc_succeq MatrixTrop_WeakRedPair) (cc_succeq MatrixTrop_WeakRedPair)
      (ARedPair2.refl_succeq MatrixTrop_WeakRedPair)
      (ARedPair2.succ_succeq_compat MatrixTrop_WeakRedPair)
      (bsucceq_sub MatrixTrop_WeakRedPair)
      (ARedPair2.trans_succ MatrixTrop_WeakRedPair)
      (ARedPair2.trans_succeq MatrixTrop_WeakRedPair).

  End matrixMethodConf_trop.

  (****************************************************************************)
  (** ** Boolean function for matrix interpretation over domain
     tropical. *)
  
  Section BoolMint_tropical.

    Notation "x >> y" := (gtt x y) (at level 70).
    
    (** Define boolean function for [gt] over domain tropical. *)
    
    Definition bgt_trop m n :=
      match gt_dect m n with
        | left _ => true
        | right _ => false
      end.
    
    (** Correcntess proof of [bgt] over domain tropical. *)
    
    Lemma bgt_trop_ok : forall m n, bgt_trop m n = true <-> (m >> n)%Z.
    
    Proof.
      intros. unfold bgt_trop.
      case_eq (gt_dect m n); intuition.
    Qed.
    
    (** Define boolean function for [ge] over domain tropical. *)

    Definition bge_trop m n := bgt_trop m n || beq_TropicalDom m n.
  
    (** Correctness proof of [bge] over domain tropical. *)

    Lemma bge_trop_ok : forall m n, bge_trop m n = true <-> get m n.
    
    Proof.
      intros m n. intuition.
      unfold get. unfold bge_trop in H. rewrite orb_eq in H.
      destruct H; try discr.
      apply bgt_trop_ok in H. left. apply H.
      apply beq_TropicalDom_ok in H. right. apply H.
      (* -> *)
      unfold get in H. destruct H.     
      unfold bge_trop. rewrite orb_eq.
      left. rewrite bgt_trop_ok. apply H.
      unfold bge_trop. rewrite orb_eq.
      right. rewrite beq_TropicalDom_ok. apply H.
    Qed.

    (** Define boolean function of [mat_ge]. *)
    
    Definition bmat_ge_trop (m n : nat) (M N: matrix_trop m n) :=
      match mat_ge_dec_trop M N with
        | left _ => true (* M >=m N *)
        | right _ => false (* ~ M >=m N *)
      end.

    (** Correctness proof of [bmat_ge]. *)
    
    Lemma bmat_ge_trop_ok: forall (m n: nat) (M N: matrix_trop m n),
                             bmat_ge_trop M N = true <-> mat_ge_trop M N.
    Proof.
      intros m n M N. unfold bmat_ge_trop.
      case_eq (mat_ge_dec_trop M N); intuition.
    Qed.

    (** Define boolean function of [mint_ge] over domain tropical. *)

    Definition bmint_ge_trop n (l r: mint n) : bool :=
      bVforall2n (bmat_ge_trop (n:=dim))(args_trop l) (args_trop r) &&
      bVforall2n (fun m n => bge_trop m n) (const_trop l) (const_trop r).
    
    (** Correctness proof of [bmint_ge] over domain tropical. *)

    Lemma bmint_ge_trop_ok: forall n (l r: mint n),
      bmint_ge_trop l r = true <-> mint_ge_trop l r.

    Proof.
      intros n l r. split. 
      (* [1]. -> *)
      intro H. unfold mint_ge_trop.
      (* Left part. *)
      split. unfold bmint_ge_trop in H. rewrite andb_eq in H.
      destruct H. rewrite bVforall2n_ok in H. apply H.
      (* Proving boolean function of [bmat_ge]. *)
      intros M N. split.
      (* -> *)
      intro H1. apply bmat_ge_trop_ok. hyp.
      (* <- *)
      intro H1. rewrite bmat_ge_trop_ok. hyp.
      (* Right part. *)
      unfold bmint_ge_trop in H. rewrite andb_eq in H.
      destruct H. rewrite bVforall2n_ok in H0. apply H0.
      (* Proving boolean function of [bge]. *)
      intros x y. split.
      (* -> *)
      intro H1. apply bge_trop_ok. hyp.
      (* <- *)
      intro H1. rewrite bge_trop_ok. hyp.
      (* [2]. <- *)
      intro H. unfold bmint_ge_trop.
      rewrite andb_eq. split.
      (* Left part. *)
      rewrite bVforall2n_ok.
      unfold mint_ge_trop in H. destruct H.
      apply H.
      (* Proving boolean function of [bmat_ge]. *)
      intros M N. split.
      (* -> *)
      intro H1. apply bmat_ge_trop_ok. hyp.
      (* <- *)
      intro H1. rewrite bmat_ge_trop_ok. hyp.
      (* Right part. *)
      rewrite bVforall2n_ok. unfold mint_ge_trop in H.
      destruct H. apply H0.
      (* Proving boolean function of [bge]. *)
      intros x y. split.
      (* -> *)
      intro H1. apply bge_trop_ok. hyp.
      (* <- *)
      intro H1. rewrite bge_trop_ok. hyp.
    Qed.

    (** Define boolean function for [gtx] over domain tropical. *)

    Definition bgtx_trop (x y: TropicalDom) : bool := 
      bgt_trop x y || beq_TropicalDom x PlusInf && beq_TropicalDom y PlusInf.

    (* REMARK: declare import of ATropicalBasedInt here because of the
    inconsitent type. *)

    Require Import ATropicalBasedInt2.
    
    (** Correctness proof of [bgtx]. *)

    Lemma bgtx_trop_ok : forall x y, bgtx_trop x y = true <-> gtx_trop x y.
    Proof.
      intros x y. split.
      (* -> *)
      intro H. unfold bgtx_trop in H.
      rewrite orb_eq in H. destruct H.
      unfold gtx_trop.
      (* Left part. *)
      left. apply bgt_trop_ok. hyp.
      (* Right part. *)
      rewrite andb_eq in H. destruct H.
      unfold gtx_trop. right. unfold eqAt.
      rewrite beq_TropicalDom_ok in H. rewrite beq_TropicalDom_ok in H0.
      auto.
      (* <- *)
      intro H. unfold bgtx_trop. rewrite orb_eq. unfold gtx_trop in H.
      destruct H. left.
      rewrite bgt_trop_ok. hyp. 
      right. rewrite andb_eq. split.
      unfold eqAt in H. rewrite beq_TropicalDom_ok. destruct H; auto.
      rewrite beq_TropicalDom_ok. destruct H; auto.
    Qed.

    (** Defintion boolean function of [mat_gt]. *)

    Definition bmat_gt_trop (M N: matrix_trop dim dim) :=
      match mat_gt_dec_trop M N with
        | left _ => true (* M >=m N *)
        | right _ => false (* ~ M >=m N *)
      end.

    (** Correctness proof of [bmat_gt].*)

    Lemma bmat_gt_trop_ok : forall (M N: matrix_trop dim dim),
                              bmat_gt_trop M N = true <-> mat_gt_trop M N.
    Proof.
      intros M N. unfold bmat_gt_trop.
      case_eq (mat_gt_dec_trop M N); intuition.
    Qed.

    (** Define boolean function for [mint_gt] over domain tropical. *)

    Definition bmint_gt_trop n (l r : mint n) : bool :=
      bVforall2n bmat_gt_trop (args_trop l) (args_trop r) &&
      bVforall2n (fun m n => bgtx_trop m n) (const_trop l) (const_trop r).

    (** Correctness proof of [bmint_gt] over domain tropical. *)

    Lemma bmint_gt_trop_ok : forall n (l r : mint n),
      bmint_gt_trop l r = true <-> mint_gt_trop l r.
    Proof.
      intros n l r. split.
      (* -> *)
      intro H. unfold bmint_gt_trop in H.
      rewrite andb_eq in H. destruct H.
      unfold mint_gt_trop. split.
      (* Left part. *)
      rewrite bVforall2n_ok in H. apply H.
      (* Proving boolean function of [bmat_gt]. *)
      intros M N. split.
      (* -> *)
      intro H1. apply bmat_gt_trop_ok. hyp.
      (* <- *)
      intro H1. rewrite bmat_gt_trop_ok. hyp.
      (* Right part. *)
      rewrite bVforall2n_ok in H0. apply H0.
      (* Proving boolean function of [bgtx]. *)
      intros x y. split.
      (* -> *)
      intro H1. apply bgtx_trop_ok. hyp.
      (* <- *)
      intro H1. rewrite bgtx_trop_ok. hyp.
      (* [2]. <- *)
      intro H. unfold bmint_gt_trop.
      rewrite andb_eq. split.
      (* Left part. *)
      rewrite bVforall2n_ok. unfold mint_gt_trop in H.
      destruct H. apply H.
      (* Proving boolean function of [bmat_gt]. *)
      intros M N. split.
      (* -> *)
      intro H1. apply bmat_gt_trop_ok. hyp.
      (* <- *)
      intro H1. rewrite bmat_gt_trop_ok. hyp.
      (* Right part. *)
      rewrite bVforall2n_ok. unfold mint_gt_trop in H.
      destruct H. apply H0.
      (* Proving boolean function of [bgtx]. *)
      intros x y. split.
      (* -> *)
      intro H1. apply bgtx_trop_ok. hyp.
      (* <- *)
      intro H1. rewrite bgtx_trop_ok. hyp.
    Qed.

  End BoolMint_tropical.

End S.