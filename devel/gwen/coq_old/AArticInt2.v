(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski and Johannes Waldmann, 2008-01
*)


Set Implicit Arguments.

Require Import AArcticBasedInt2 Matrix2 OrdSemiRing2 VecUtil
  AMonAlg2 SN RelUtil NatUtil AWFMInterpretation LogicUtil
  AMatrixBasedInt2_ArcticNat Bool VecArith2.

(***********************************************************************)
(** ** Matrix interpretation in domain arctic natural numbers. *)

Definition matrixInt := @matrixInt_arcnat matrix_arcnat.
Definition mkMatrixInt := @mkMatrixInt_arcnat matrix_arcnat.

(** Condition for an arctic interpretation to be valid. *)

Section S.

  Variable dim : nat.
  Variable Sig : Signature.

  Section Somewhere_finite.

  Variable dim_pos : dim > 0.
    
    Definition somewhere_finite n (fi : matrixInt dim n) := 
      Vexists (fun m => get_elem_arcnat m dim_pos dim_pos <> MinusInf)
      (args_arcnat fi) \/ Vnth (const_arcnat fi) dim_pos <> MinusInf.

    Definition bsomewhere_finite n (fi : matrixInt dim n) :=
      bVexists (fun m => is_finite (get_elem_arcnat m dim_pos dim_pos))
      (args_arcnat fi)
      || is_finite (Vnth (const_arcnat fi) dim_pos).

    Require Import BoolUtil.
    
    Lemma bsomewhere_finite_ok : forall n (fi : matrixInt dim n),
      bsomewhere_finite fi = true <-> somewhere_finite fi.

    Proof.
      intros. unfold bsomewhere_finite, somewhere_finite.
      rewrite orb_eq. rewrite is_finite_ok.
      rewrite bVexists_ok. refl. intro. apply is_finite_ok.
    Qed.

    Variable mc : MatrixMethodConf_arcnat Sig dim.
    Notation trsInt := (trsInt_arcnat mc).

    Require Import List ListForall.

    Variable Fs : list Sig.
    Variable Fs_ok : forall f : Sig, In f Fs.

    Lemma fin_somewhere_finite :
      forallb (fun f => bsomewhere_finite (trsInt f)) Fs = true ->
      forall f : Sig, somewhere_finite (trsInt f).

    Proof.
      rewrite forallb_forall. intros H f.
      rewrite <- bsomewhere_finite_ok.
      apply H. apply Fs_ok.
    Qed.

  End Somewhere_finite.

  Implicit Arguments fin_somewhere_finite [Fs].

  Ltac somewhere_finite Fs_ok :=
    apply (fin_somewhere_finite _ _ Fs_ok);
      (check_eq || fail 10 "invalid arctic interpretation").

  (** Section for proving termination with an arctic interpretation. *)
  
  Section TArcticInt.

    Variable mc : MatrixMethodConf_arcnat Sig dim.

    Parameter trsIntOk : forall f : Sig, somewhere_finite (dim_pos dim)
      (trsInt_arcnat mc f).

    Section MonotoneAlgebra.

      Lemma mat_times_vec_at0_positive : forall n (m : matrix_arcnat n n) 
        (v : vector Ar n) (dim_pos : n > 0),
        get_elem_arcnat m dim_pos dim_pos <> MinusInf ->   
        Vnth v dim_pos <> MinusInf ->
        Vnth (mat_vec_prod_arcnat m v) dim_pos <> MinusInf.
        
      Proof.
        destruct n; intros. absurd_arith.
        VSntac v. unfold matrix_arcnat in m. VSntac m. 
        unfold mat_vec_prod_arcnat, col_mat_to_vec_arcnat,
          get_col_arcnat. rewrite Vnth_map. 
        set (w := mat_mult_spec_arcnat).
        unfold get_elem_arcnat, get_row_arcnat in w. rewrite w.
        simpl. VSntac (Vhead m). unfold dot_product_arcnat.
        simpl. rewrite A_plus_comm. apply arctic_plus_notInf_left.
        apply arctic_mult_notInf. 
        rewrite H2 in H. unfold get_elem_arcnat in H. simpl in H.
        rewrite Vhead_nth. 
        rewrite <- (Vnth_eq (Vhead m) dim_pos (lt_O_Sn n)); trivial.
        rewrite H1 in H0. hyp.
      Qed.

      Notation mat_times_vec := (@mat_vec_prod_arcnat dim dim).
      Notation "x + y" := (Aplusr x y).
      Notation "x * y" := (Amultr x y).
      Notation "x >_0 y" := (gtx x y) (at level 70).
      Notation "X =A= Y" := (eqAr X Y) (at level 70).

      Lemma gtx_plus_compat : forall m m' n n',
        m >_0 m' -> n >_0 n' -> m + n >_0 m' + n'.

      Proof.
        intros. destruct H. destruct H0.
        left. apply plus_gt_compatr; hyp.
        destruct H0. rewrite H0. rewrite H1.
        do 2 rewrite A_plus_0_r. left. hyp.
        destruct H. rewrite H. rewrite H1.
        do 2 rewrite A_plus_0_l. hyp.
      Qed.

      Notation "x >>= y" := (ger x y) (at level 70).
      
      Lemma gtx_mult_compat : forall m m' n n',
        m >_0 m' -> n >>= n' -> m * n >_0 m' * n'.
        
      Proof.
        intros.
        destruct m; destruct m'; destruct n; destruct n';
          destruct H; destruct H0; simpl;
            try solve
              [ elimtype False; auto
                | intuition; discr
                | left; simpl; auto
                | left; simpl in *; omega
                | right; auto
              ].
        left. simpl. injection H0. intro. subst n. simpl in H. omega.
      Qed.

      Definition dom2vec_arcnat (d : dom_arcnat dim) := dom2vec_arcnat d.

      Notation mint := (matrixInt_arcnat matrix_arcnat dim).

      Lemma eval_some_notInf : forall n (mi : mint n)
        (v : vector (dom_arcnat dim) n),
        Vexists (fun m => get_elem_arcnat m
          (dim_pos dim) (dim_pos dim) <> MinusInf) (args_arcnat mi) ->
        Vfold_left Aplusr A0r
        (Vmap (fun v => Vnth v (dim_pos dim))
          (Vmap2 mat_times_vec (args_arcnat mi)
            (Vmap dom2vec_arcnat v))) <> MinusInf.
        
      Proof.
        induction n; intros; simpl; destruct mi.
        VOtac. auto.
        simpl in H. VSntac args_arcnat. rewrite H0 in H; simpl. destruct H.
        rewrite A_plus_comm. apply arctic_plus_notInf_left.
        apply mat_times_vec_at0_positive. hyp.
        VSntac v. simpl. destruct (Vhead v).
        simpl in *.
        apply ge_A1_not_minusInf. hyp.
        apply arctic_plus_notInf_left. 
        rewrite <- Vmap_tail.
        apply (IHn (mkMatrixInt const_arcnat (Vtail args_arcnat))). hyp.
      Qed.

      Lemma mi_eval_at0 : forall n (mi : mint n) (v : vector (dom_arcnat dim) n),
        somewhere_finite (dim_pos dim) mi ->
        vec_at0_arcnat (mi_eval_aux_arcnat mi (Vmap dom2vec_arcnat v)) <> MinusInf.

      Proof.
        intros. unfold mi_eval_aux_arcnat, vec_at0_arcnat. 
        rewrite vector_plus_nth_arcnat. destruct H.
        rewrite add_vectors_nth_arcnat. apply arctic_plus_notInf_left.
        apply eval_some_notInf. hyp.
        rewrite A_plus_comm. apply arctic_plus_notInf_left. hyp.
      Qed.

      Lemma mi_eval_ok : forall f v,
        vec_invariant_arcnat (mi_eval_aux_arcnat
          (trsInt_arcnat mc f) (Vmap dom2vec_arcnat v)).

      Proof.
        intros. simpl in *.
        apply not_minusInf_ge_A1.
        set (w := mi_eval_at0). unfold vec_at0_arcnat in w. apply w.
        apply trsIntOk.
      Qed.

      Definition I := I_arcnat mc mi_eval_ok.
      Definition succ := @AArcticBasedInt2.succ dim.
      Definition succ' := @AArcticBasedInt2.succ' Sig dim mc.
      Definition succ'_sub :=
        @AArcticBasedInt2.succ'_sub Sig dim  gtx_plus_compat  gtx_mult_compat mc mi_eval_ok. 
      Definition succ'_dec := @AArcticBasedInt2.succ'_dec Sig dim mc.
      Definition succeq := @succeq_arcnat dim.
      Definition succeq' := @succeq_arcnat' Sig dim mc.
      Definition succeq'_sub := @succeq'_sub_arcnat Sig dim mc mi_eval_ok.
      Definition succeq'_dec := @succeq'_dec_arcnat Sig dim mc.
      Definition refl_succeq := @refl_succeq_arcnat dim.
      Definition monotone_succeq :=
        @monotone_succeq_arcnat Sig dim mc mi_eval_ok.
      Definition trans_succeq := @trans_succeq_arcnat dim.
      Definition trans_succ := @AArcticBasedInt2.trans_succ dim.
      Definition succ_succeq_compat :=
        @AArcticBasedInt2.succ_succeq_compat dim ge_gt_eqr.

      Lemma succ_wf : WF succ.

      Proof.
        apply WF_incl with 
          (fun x y => gtr
            (vec_at0_arcnat (dom2vec_arcnat x))
            (vec_at0_arcnat (dom2vec_arcnat y))).
        intros x y xy.
        destruct (@Vforall2n_nth _ _ gtx _ 
          (dom2vec_arcnat x) (dom2vec_arcnat y) _ (dim_pos dim) xy). 
        hyp.
        destruct H. destruct x.
        absurd (Vnth x (dim_pos dim) = A0r).
        apply ge_A1_not_minusInf. hyp. hyp.
        fold (@Rof (dom_arcnat dim) Ar gtr
          (fun v => vec_at0_arcnat (dom2vec_arcnat v))).
        apply WF_inverse. apply gt_WFr.
      Qed.

      (* Define record type for MonotoneAlgType for domain arctic
         natural numbers. *)
      
      Definition matAlg_arcnat := mkbMonoAlgType Sig I succ succeq
        refl_succeq trans_succ trans_succeq monotone_succeq succ_wf
        succ_succeq_compat succ' succeq' succ'_sub succeq'_sub
        succ'_dec succeq'_dec.

    End MonotoneAlgebra.

    Ltac prove_cc_succ Fs_ok :=
      fail 10 "arctic matrices cannot be used for proving total termination".

  End TArcticInt.

End S.