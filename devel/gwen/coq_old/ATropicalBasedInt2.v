(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Johannes Waldmann, 2010-04
*)

Set Implicit Arguments.

Require Import AMonAlg2 Matrix2 OrdSemiRing2 VecUtil SN RelUtil
  LogicUtil Setoid VecEq VecOrd VecArith2 AMatrixBasedInt2_Trop SemiRing2.

Section S.

  Variable Sig: Signature.
  Variable dim : nat.

  Section ABI.

    Notation matrixInt := (matrixInt_trop matrix_trop).
    Notation mint := (matrixInt dim).
    Notation mat := (matrix_trop dim dim).
    Notation "X =A= Y" := (eqAt X Y) (at level 70).
    Notation "x >>= y" := (get x y) (at level 70).
    Notation "x >> y" := (gtt x y) (at level 70).
    Variable A0_min : forall x, x >>= PlusInf.
    Variable ge_gt_eq : forall x y, x >>= y -> x >> y \/ x =A= y.
    Definition gtx_trop x y := x >> y \/ (x =A= PlusInf /\ y =A= PlusInf).
    Notation "x >_0 y" := (gtx_trop x y) (at level 70).

    Add Morphism gtx_trop with signature eqAt ==> eqAt ==> iff as
    gtx_mort.

    Proof.
      unfold gtx_trop. intuition. left. rewrite <- H.
      rewrite <- H0. hyp. right.
      split. trans x. sym. hyp. hyp. trans x0. sym.
      hyp. hyp.
      left. rewrite H. rewrite H0. hyp. right. split.
      trans y; hyp. trans y0; hyp.
    Qed.

    Lemma gtx_trans_trop : transitive gtx_trop.

    Proof.
      unfold gtx_trop. intros x y z. intuition.
      left. apply gt_transt with y; hyp.
      unfold eqAt in H2.
      rewrite H2. rewrite H0 in H1. auto.
      unfold eqAt in H.
      rewrite H. rewrite H2 in H1. auto.
    Qed.

    Definition succ_vec_trop {n} := Vreln gtx_trop (n:=n).
    Definition dom2vec_trop (d : dom_trop dim) := dom2vec_trop d.
    Definition succ_trop (x y : dom_trop dim) := succ_vec_trop
    (dom2vec_trop x) (dom2vec_trop y).
    Notation "x >v y" := (succ_trop x y) (at level 70).

    Lemma trans_succ_trop : transitive succ_trop.

    Proof.
      unfold succ_trop. apply Rof_trans with (f:=dom2vec_trop).
      unfold succ_vec_trop.
      apply Vreln_trans. apply gtx_trans_trop.      
    Qed.

    Lemma ge_gtx_compat_trop : forall x y z, x >>= y -> y >_0 z -> x
    >_0 z.

    Proof.
      unfold gtx_trop. intuition. left. apply ge_gt_compatt with y; hyp.
      unfold eqAt in H2.
      rewrite H2. rewrite H0 in H. destruct (ge_gt_eq H); intuition.
    Qed.

    Variable succ_wf : WF succ_trop.
    Notation "x + y" := (Aplust x y).
    Notation "x * y" := (Amultt x y).
    Variable gtx_plus_compat : forall m m' n n',
      m >_0 m' -> n >_0 n' -> m + n >_0 m' + n'.
    Variable gtx_mult_compat : forall m m' n n',
      m >_0 m' -> n >>= n' -> m * n >_0 m' * n'.

    Definition succeq_trop (x y : dom_trop dim) := succeq_trop x y.

    Lemma succ_succeq_compat_trop : absorbs_left succ_trop succeq_trop.

    Proof.
      intros x z xz. destruct xz as [y [xy yz] ].
      unfold succ_trop, succ_vec_trop. apply Vforall2n_intro. intros.
      apply ge_gtx_compat_trop with (Vnth (dom2vec_trop y) ip).
      apply Vforall2n_nth. hyp.
      apply Vforall2n_nth. hyp.
    Qed.

    Lemma gtx_dec_trop : rel_dec gtx_trop.

    Proof.
      intros x y. destruct (gt_dect x y).
      left. left. hyp.
      destruct (eqA_dect x PlusInf).
      destruct (eqA_dect y PlusInf).
      left. right. auto.
      right. unfold gtx_trop. intuition.
      right. unfold gtx_trop. intuition.
    Defined.

    Lemma succ_dec_trop : rel_dec succ_trop.
  
    Proof.
      intros x y. unfold succ_trop.
      apply (Vforall2n_dec gtx_dec_trop (dom2vec_trop x) (dom2vec_trop y)).
    Defined.

    Variable mc : MatrixMethodConf_trop Sig dim.

    Variable mi_eval_ok : forall f v, vec_invariant_trop
      (mi_eval_aux_trop (trsInt_trop mc f) (Vmap dom2vec_trop v)).

    Notation I := (I_trop mc mi_eval_ok).
    Notation IR_succ := (IR I succ_trop).

    Definition mat_gt_trop := mat_forall2_trop gtx_trop (m:=dim)
    (n:=dim).

    Definition vec_gt_trop := Vforall2n gtx_trop (n:=dim).

    Definition mint_gt_trop n (l r : mint n) := Vforall2n mat_gt_trop
      (args_trop l) (args_trop r) /\ vec_gt_trop (const_trop l)
      (const_trop r).

    Definition term_gt_trop := term_gt_trop mc mint_gt_trop.

    Lemma mat_gt_dec_trop : rel_dec mat_gt_trop.

    Proof.
      unfold mat_gt_trop. apply mat_forall2_dec_trop.
      exact gtx_dec_trop.
    Defined.

    Lemma vec_gt_dec_trop : rel_dec vec_gt_trop.
      
    Proof.
      unfold vec_gt_trop. apply Vforall2n_dec.
      exact gtx_dec_trop.
    Defined.

    Lemma mint_gt_dec_trop : forall n, rel_dec (@mint_gt_trop n).

    Proof.
      intros n x y. unfold mint_gt_trop.
      destruct (Vforall2n_dec mat_gt_dec_trop
        (args_trop x) (args_trop y)); 
        intuition.
      destruct (vec_gt_dec_trop (const_trop x)
        (const_trop y)); intuition.      
    Defined.

    Lemma Vfold_left_gtx_compat_trop : forall n (v v' : vector At n),
      (forall i (ip: i < n), Vnth v ip >_0 Vnth v' ip) -> Vfold_left
      Aplust SemiRing2.PlusInf v >_0 Vfold_left Aplust
      SemiRing2.PlusInf v'.

    Proof.
      induction v; simpl; intros.
      VOtac. simpl. right. intuition. 
      VSntac v'. simpl. apply gtx_plus_compat.
      apply IHv. intros. 
      apply Vforall2n_nth. change v with (Vtail (Vcons h v)). 
      apply Vforall2n_tail. apply Vforall2n_intro. hyp.
      change h with (Vhead (Vcons h v)). do 2 rewrite Vhead_nth.
      apply (H _ (Lt.lt_O_Sn n)).
    Qed.

    Section Matrix.

      Variables (m n p : nat) (M M' : matrix_trop m n) (N N' :
      matrix_trop n p).

      Notation vge := vec_ge_trop.
      Notation vgt := (Vforall2n gtx_trop).
      Notation mge := mat_ge_trop.
      Notation mgt := (mat_forall2_trop gtx_trop).

      Lemma arctic_dot_product_mon : forall i (v v' w w' : vector At
        i), vgt v v' -> vge w w' -> dot_product_trop v w >_0
        dot_product_trop v' w'.

      Proof.
        unfold dot_product_trop. induction v; intros; simpl.
        right. intuition. unfold A0t. refl. unfold A0t. refl.
        apply gtx_plus_compat.
        apply IHv.
        change v with (Vtail (Vcons h v)). apply Vforall2n_tail. hyp.
        apply Vreln_tail_intro. hyp.
        apply gtx_mult_compat. change h with (Vhead (Vcons h v)). 
        do 2 rewrite Vhead_nth. apply Vforall2n_nth. hyp.
        do 2 rewrite Vhead_nth. apply Vforall2n_nth. hyp.
      Qed.

      Infix "<*>" := mat_mult_trop (at level 40).

      Lemma mat_arctic_mult_mon : mgt M M' -> mge N N' -> 
        mgt (M <*> N) (M' <*> N').

      Proof.
        intros. unfold mat_forall2_trop. intros.
        do 2 rewrite mat_mult_spec_trop. apply arctic_dot_product_mon.
        apply Vforall2n_intro. intros. 
        exact (H i i0 ip ip0).
        unfold vge. apply Vforall2n_intro. intros.
        do 2 rewrite <- get_elem_swap_trop. exact (H0 i0 j ip0 jp).
      Qed.

    End Matrix.

    Lemma mat_vec_prod_gt_compat : forall (M M' : mat) m m', 
      mat_gt_trop M M' -> m >=v m' -> 
      vec_gt_trop (mat_vec_prod_trop M m) (mat_vec_prod_trop M' m').

    Proof.
      intros. unfold mat_vec_prod_trop, vec_gt_trop. apply Vforall2n_intro. 
      intros. do 2 rewrite Vnth_col_mat_trop. 
      apply mat_arctic_mult_mon. hyp.
      intros k l pk pl. do 2 rewrite vec_to_col_mat_spec_trop.
      apply Vforall2n_nth. hyp.
    Qed.

    Lemma mint_eval_mon_succ : forall (val : valuation I) k (mi mi' :
      mint k), mint_gt_trop mi mi' -> succ_vec_trop (mint_eval_trop
      val mi) (mint_eval_trop val mi').

    Proof.
      intros. unfold succ_vec_trop. apply Vforall2n_intro. intros. destruct H.
      eapply gtx_mort. 
      apply (Vnth_mor eqAt); rewrite (mint_eval_split_trop ); refl.
      apply (Vnth_mor eqAt). rewrite mint_eval_split_trop. refl.
      do 2 rewrite vector_plus_nth_trop.
      apply gtx_plus_compat.
      apply Vforall2n_nth. hyp.
      do 2 rewrite add_vectors_nth_trop.
      apply Vfold_left_gtx_compat_trop. intros.
      do 2 rewrite Vnth_map. do 2 rewrite Vnth_map2.
      set (eval := Vnth (Vbuild (fun i (_ : i < k) => val i)) ip0).
      apply Vforall2n_nth. apply mat_vec_prod_gt_compat.
      apply Vforall2n_nth. hyp.
      apply vec_ge_refl_trop.
    Qed.

    Lemma term_gt_incl_succ_trop : term_gt_trop << IR_succ.

    Proof.
      intros l r lr v. destruct (mint_eval_equiv_trop l r v). simpl in *.
      unfold succ_trop. unfold succ_vec_trop. 
      symmetry in H. symmetry in H0.
      rewrite (Vforall2n_mor sid_theoryAt gtx_mort H H0).
      apply mint_eval_mon_succ. hyp.
    Qed.

    Definition succ'_trop := term_gt_trop.
    Definition succ'_sub_trop := term_gt_incl_succ_trop.
    Definition succ'_dec_trop := term_gt_dec_trop mc mint_gt_trop
    mint_gt_dec_trop.

  End ABI.

End S.
