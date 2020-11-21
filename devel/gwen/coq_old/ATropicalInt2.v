(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Johannes Waldmann, 2010-04
*)

Set Implicit Arguments.

Require Import ATropicalBasedInt2 Matrix2 OrdSemiRing2 VecUtil
  AMonAlg2 SN RelUtil NatUtil AWFMInterpretation LogicUtil
  AMatrixBasedInt2_Trop Bool VecArith2 SemiRing2 VecOrd.

Definition matrixInt := @matrixInt_trop matrix_trop.
Definition mkMatrixInt := @mkMatrixInt_trop matrix_trop.

(***********************************************************************)
(** ** Condition for a tropical interpretation to be valid. *)

Section S.

  Variable dim : nat.
  Variable Sig : Signature.

  Section Somewhere_tfinite.

    Definition somewhere_tfinite n (fi : matrixInt dim n) := 
      Vexists (fun m => get_elem_trop m (dim_pos dim)
        (dim_pos dim) <> PlusInf) (args_trop fi)
      \/ Vnth (const_trop fi) (dim_pos dim) <> PlusInf.
    
    Definition bsomewhere_tfinite n (fi : matrixInt dim n) :=
      bVexists
      (fun m => tropical_is_finite (get_elem_trop m
        (dim_pos dim) (dim_pos dim))) (args_trop fi)
      || tropical_is_finite (Vnth (const_trop fi) (dim_pos dim)).
    
    Require Import BoolUtil.
    
    Lemma bsomewhere_tfinite_ok : forall n (fi : matrixInt dim n),
      bsomewhere_tfinite fi = true <-> somewhere_tfinite fi.
      
    Proof.
      intros. unfold bsomewhere_tfinite, somewhere_tfinite.
      rewrite orb_eq. rewrite tropical_is_finite_ok.
      rewrite bVexists_ok. refl. intro. apply tropical_is_finite_ok.
    Qed.

    Require Import List ListForall.

    Variable Fs : list Sig.
    Variable Fs_ok : forall f : Sig, In f Fs.
    Variable mc: MatrixMethodConf_trop Sig dim.
    Notation trsInt := (trsInt_trop mc).
    
    Lemma fin_somewhere_tfinite :
      forallb (fun f => bsomewhere_tfinite (trsInt f)) Fs = true ->
      forall f : Sig, somewhere_tfinite (trsInt f).
      
    Proof.
      rewrite forallb_forall. intros H f. rewrite <- bsomewhere_tfinite_ok.
      apply H. apply Fs_ok.
    Qed.
    
  End Somewhere_tfinite.
  
  Implicit Arguments fin_somewhere_tfinite [Fs].
  
  Ltac somewhere_tfinite Fs_ok :=
    apply (fin_somewhere_tfinite _ _ Fs_ok);
      (check_eq || fail 10 "invalid tropical interpretation").
  
  (***********************************************************************)
  (** ** Proving termination with a tropical interpretation. *)
  
  Section TTropicalInt.

    Variable mc : MatrixMethodConf_trop Sig dim.
    Parameter trsIntOk : forall f : Sig, somewhere_tfinite  (trsInt_trop mc f).
    
    Section MonotoneAlgebra. 
      
      Lemma mat_times_vec_at0_positive : forall n (m : matrix_trop n n) 
        (v : vector At n) (dim_pos : n > 0),
        get_elem_trop m dim_pos dim_pos <> PlusInf ->   
        Vnth v dim_pos <> PlusInf ->
        Vnth (mat_vec_prod_trop m v) dim_pos <> PlusInf.
        
      Proof.
        destruct n; intros. absurd_arith.
        VSntac v. unfold matrix_trop in m. VSntac m. 
        unfold mat_vec_prod_trop, col_mat_to_vec_trop, get_col_trop. rewrite Vnth_map. 
        set (w := mat_mult_spec_trop). unfold get_elem_trop, get_row_trop in w. rewrite w.
        simpl. VSntac (Vhead m). unfold dot_product_trop.
        simpl. rewrite A_plus_commt. apply tropical_plus_notInf_leftt.
        apply tropical_mult_notInft. 
        rewrite H2 in H. unfold get_elem_trop in H. simpl in H.
        rewrite Vhead_nth. 
        rewrite <- (Vnth_eq (Vhead m) dim_pos (lt_O_Sn n)); trivial.
        rewrite H1 in H0. hyp.
      Qed.

      Notation mat_times_vec := (@mat_vec_prod_trop dim dim).
      Notation mint := (matrixInt_trop matrix_trop dim).
      Notation "x >_0 y" := (gtx_trop x y) (at level 70).
      Notation "x >>= y" := (get x y) (at level 70).
      Notation "x >> y" := (gtt x y) (at level 70).
      Notation "x + y" := (Aplust x y).
      Notation "x * y" := (Amultt x y).
      Notation "X =A= Y" := (eqAt X Y) (at level 70).

      Lemma gtx_plus_compat : forall m m' n n',
        m >_0 m' -> n >_0 n' -> m + n >_0 m' + n'.
        
      Proof.
        intros. destruct H. destruct H0.
        left. apply plus_gt_compatt; hyp.
        destruct H0. rewrite H0. rewrite H1. 
        do 2 rewrite A_plus_0_rt. left. hyp.
        destruct H. rewrite H. rewrite H1.
        do 2 rewrite A_plus_0_lt. hyp.
      Qed.
      
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
      
      Definition dom2vec_trop (d : dom_trop dim) := dom2vec_trop d.
      
      Lemma eval_some_notInf : forall n (mi : mint n) (v : vector (dom_trop dim) n),
        Vexists (fun m => get_elem_trop m (dim_pos dim)
          (dim_pos dim) <> PlusInf) (args_trop mi) ->
        Vfold_left Aplust A0t
        (Vmap (fun v => Vnth v (dim_pos dim))
          (Vmap2 mat_times_vec (args_trop mi) (Vmap dom2vec_trop v))) <> PlusInf.
        
      Proof.
        induction n; intros; simpl; destruct mi.
        VOtac. auto.
        simpl in H. VSntac args_trop. rewrite H0 in H; simpl. destruct H.
        rewrite A_plus_commt. apply tropical_plus_notInf_leftt.
        apply mat_times_vec_at0_positive. hyp.
        VSntac v. simpl. destruct (Vhead v).
        unfold vec_invariant_trop, vec_at0_trop in v0. simpl in *.
        (* TODO... change - specific to tropical... *)
        intuition. clear H1. unfold A1t in v0. rewrite H2 in v0.
        contradiction.
        apply tropical_plus_notInf_leftt. 
        rewrite <- Vmap_tail.
        apply (IHn (mkMatrixInt_trop const_trop (Vtail args_trop))). hyp.
      Qed.
      
      Lemma mi_eval_at0 : forall n (mi : matrixInt dim n) (v : vector (dom_trop dim) n),
        somewhere_tfinite mi ->
        vec_at0_trop (mi_eval_aux_trop mi (Vmap dom2vec_trop v)) <> PlusInf.
        
      Proof.
        intros. unfold mi_eval_aux_trop, vec_at0_trop. 
        rewrite vector_plus_nth_trop. destruct H.
        rewrite add_vectors_nth_trop. apply tropical_plus_notInf_leftt.
        apply eval_some_notInf. hyp.
        rewrite A_plus_commt. apply tropical_plus_notInf_leftt. hyp.
      Qed.
      
      Notation trsInt := (trsInt_trop mc).
      
      Lemma mi_eval_ok : forall f v,
        vec_invariant_trop (mi_eval_aux_trop (trsInt f) (Vmap dom2vec_trop v)).

      Proof.
        intros. unfold vec_invariant_trop, vec_at0_trop.
        apply tropical_plus_inf_max.
        set (w := mi_eval_at0). (*unfold vec_at0 in w.*) apply w.
        apply trsIntOk.
      Qed.
      
      Definition I := I_trop mc mi_eval_ok.
      Definition succ := @succ_trop dim.
      Definition succ' := @succ'_trop Sig dim mc.
      Definition succ'_sub :=
        @succ'_sub_trop Sig dim  gtx_plus_compat gtx_mult_compat mc mi_eval_ok.
      Definition succ'_dec := @succ'_dec_trop Sig dim mc.
      Definition succeq := @succeq_trop dim.
      Definition succeq' := @succeq_trop' Sig dim mc.
      Definition succeq'_sub := @succeq'_sub_trop Sig dim mc mi_eval_ok.
      Definition succeq'_dec := @succeq'_dec_trop Sig dim mc.
      Definition refl_succeq := @refl_succeq_trop dim.
      Definition monotone_succeq := @monotone_succeq_trop Sig dim mc mi_eval_ok.
      Definition trans_succeq := @trans_succeq_trop dim.
      Definition succ_succeq_compat := @succ_succeq_compat_trop dim ge_gt_eq.

      Lemma succ_wf : WF succ.
        
      Proof.
        apply WF_incl with 
          (fun x y => vec_at0_trop (dom2vec_trop x) >> vec_at0_trop (dom2vec_trop y)).
        intros x y xy.
        destruct (@Vforall2n_nth _ _ gtx_trop _
          (dom2vec_trop x) (dom2vec_trop y) _ (dim_pos dim) xy). 
        hyp.
        destruct H. destruct x.
        (* TODO: change, specific for tropical *)
        absurd (A0t = Vnth x (dim_pos dim)).
        unfold vec_invariant_trop in v.
        intro eq. clear H xy. rewrite eq in v. exact (gt_irreflt _ v).
        intuition.
        fold (@Rof (dom_trop dim) At gtt (fun v => vec_at0_trop (dom2vec_trop v))).
        apply WF_inverse. apply gt_WFt.
      Qed.

      Lemma trans_succ : transitive succ.
        
      Proof.
        unfold succ, succ_trop. apply Rof_trans with (f:=dom2vec_trop).
        unfold succ_vec_trop. apply Vreln_trans. apply gtx_trans_trop.
      Qed.
      
    (** Define record type for MonotoneAlgType for domain arctic
       natural numbers. *)
    
      Definition matAlg_trop := mkbMonoAlgType Sig I succ succeq refl_succeq
        trans_succ trans_succeq monotone_succeq succ_wf succ_succeq_compat
        succ' succeq' succ'_sub succeq'_sub succ'_dec succeq'_dec.
      
    End MonotoneAlgebra.
    
    Ltac prove_cc_succ Fs_ok :=
      fail 10 "tropical matrices cannot be used for proving total termination".
    
  End TTropicalInt.
  
End S. 