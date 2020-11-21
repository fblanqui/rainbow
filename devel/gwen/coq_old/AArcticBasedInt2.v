(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski and Johannes Waldmann, 2008-01
*)

Set Implicit Arguments.

Require Import AMonAlg2 Matrix2 OrdSemiRing2 VecUtil SN RelUtil
  LogicUtil Setoid VecEq VecOrd AMatrixBasedInt2_ArcticNat
  AMatrixBasedInt2_ArcticBZ VecArith2.

(** Section for proving termination with matrix interpretations. *)

Section S.

  Variable Sig : Signature.
  Variable dim : nat.

  Section ABI.

    Notation matrixInt_arcnat := (matrixInt_arcnat matrix_arcnat).
    Notation mint := (matrixInt_arcnat dim).
    Notation mat := (matrix_arcnat dim dim).
    Notation MinusInf := A0r.
    Notation "x >> y" := (gtr x y) (at level 70).
    Notation "x >>= y" := (ger x y) (at level 70).
    Notation "x =A= y" := (eqAr x y) (at level 70).
    Variable A0_min : forall x, x >>= MinusInf.
    Variable ge_gt_eq : forall x y, x >>= y -> x >> y \/ x =A= y.
    
    Definition gtx x y := x >> y \/ (x =A= MinusInf /\ y =A= MinusInf).
    
    Notation "x >_0 y" := (gtx x y) (at level 70).
    
    Add Morphism gtx with signature eqAr ==> eqAr ==> iff as gtx_mor.
      
    Proof.
      unfold gtx. intuition. left. rewrite <- H.
      rewrite <- H0. hyp. right.
      split. trans x. sym. hyp. hyp. trans x0. sym.
      hyp. hyp.
      left. rewrite H. rewrite H0. hyp. right. split.
      trans y; hyp. trans y0; hyp.
    Qed.
    
    Lemma gtx_trans : transitive gtx.
      
    Proof.
      unfold gtx. intros x y z. intuition.
      left. apply gt_transr with y; hyp. unfold MinusInf in H2.
      unfold eqAr in H2.
      rewrite H2.
      rewrite H0 in H1. auto.
      unfold eqAr in H. rewrite H. rewrite H2 in H1. auto.
      Qed.
    
    Definition succ_vec {n} := Vreln gtx (n:=n).
    
    Notation vec := (vector Ar dim).
    
    Definition succ (x y : dom_arcnat dim) :=
      succ_vec (dom2vec_arcnat x) (dom2vec_arcnat y).
    
    Notation "x >v y" := (succ x y) (at level 70).
    
    Definition dom2vec_arcnat (d : dom_arcnat dim):= dom2vec_arcnat d.
    
    Lemma trans_succ : transitive succ.
      
    Proof.
      unfold succ. apply Rof_trans with (f:=dom2vec_arcnat).
      unfold succ_vec.
      apply Vreln_trans. apply gtx_trans.      
    Qed.
    
    Lemma ge_gtx_compat : forall x y z, x >>= y -> y >_0 z -> x >_0 z.
      
    Proof.
      unfold gtx. intuition. left. apply ge_gt_compatr with y; hyp.
      unfold eqAr in H2. rewrite H2. rewrite H0 in H.
      destruct (ge_gt_eq H); intuition.
    Qed.
    
    Variable succ_wf : WF succ.
    
    Notation "x + y" := (Aplusr x y).
    Notation "x * y" := (Amultr x y).
    
    Variable gtx_plus_compat : forall m m' n n',
      m >_0 m' -> n >_0 n' -> m + n >_0 m' + n'.
    
    Variable gtx_mult_compat : forall m m' n n',
      m >_0 m' -> n >>= n' -> m * n >_0 m' * n'.
    
    Infix ">=v" := vec_ge_arcnat (at level 70).
    
    Definition succeq (x y : dom_arcnat dim) :=
      (dom2vec_arcnat x) >=v (dom2vec_arcnat y).
    
    Lemma succ_succeq_compat : absorbs_left succ succeq.
      
    Proof.
      intros x z xz. destruct xz as [y [xy yz] ].
      unfold succ, succ_vec. apply Vforall2n_intro. intros.
      apply ge_gtx_compat with (Vnth (dom2vec_arcnat y) ip).
      apply Vforall2n_nth. hyp.
      apply Vforall2n_nth. hyp.
    Qed.
    
    Lemma gtx_dec : rel_dec gtx.
      
    Proof.
      intros x y. destruct (gt_decr x y).
      left. left. hyp.
      destruct (eqA_decr x MinusInf).
      destruct (eqA_decr y MinusInf).
      left. right. auto.
      right. unfold gtx. intuition.
      right. unfold gtx. intuition.
    Defined.
    
    Lemma succ_dec : rel_dec succ.
      
    Proof.
      intros x y. unfold succ.
      apply (Vforall2n_dec gtx_dec (dom2vec_arcnat x) (dom2vec_arcnat y)).
    Defined.
    
    Infix "[+]" := vector_plus_arcnat (at level 50).
    Infix "<*>" := mat_mult_arcnat (at level 40).
    
    Variable mc : MatrixMethodConf_arcnat Sig dim.
    
    Definition mat_gt := mat_forall2_arcnat gtx (m:=dim) (n:=dim).
    Definition vec_gt := Vforall2n gtx (n:=dim).
    
    Definition mint_gt n (l r : mint n) := 
      Vforall2n mat_gt (args_arcnat l) (args_arcnat r) /\ 
      vec_gt (const_arcnat l) (const_arcnat r).
    
    Definition term_gt := term_ord_arcnat mc mint_gt.

    Lemma mat_gt_dec : rel_dec mat_gt.
      
    Proof.
      unfold mat_gt. apply mat_forall2_dec_arcnat. exact gtx_dec.
    Defined.
    
    Lemma vec_gt_dec : rel_dec vec_gt.
      
    Proof.
      unfold vec_gt. apply Vforall2n_dec. exact gtx_dec.
    Defined.
    
    Lemma mint_gt_dec : forall n, rel_dec (@mint_gt n).
      
    Proof.
      intros n x y. unfold mint_gt.
      destruct (Vforall2n_dec mat_gt_dec (args_arcnat x) (args_arcnat y)); 
        intuition.
      destruct (vec_gt_dec (const_arcnat x) (const_arcnat y)); intuition.      
    Defined.
    
    Lemma Vfold_left_gtx_compat : forall n (v v' : vector Ar n),
      (forall i (ip: i < n), Vnth v ip >_0 Vnth v' ip) ->
      Vfold_left Aplusr A0r v >_0 Vfold_left Aplusr A0r v'.
      
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
      
      Variables (m n p : nat) (M M' : matrix_arcnat m n)
        (N N' : matrix_arcnat n p).
      
      Notation vge := vec_ge_arcnat.
      Notation vgt := (Vforall2n gtx).
      Notation mge := mat_ge_arcnat.
      Notation mgt := (mat_forall2_arcnat gtx).

      Lemma arctic_dot_product_mon : forall i (v v' w w' : vector Ar i), 
        vgt v v' -> vge w w' ->
        dot_product_arcnat v w >_0 dot_product_arcnat v' w'.

      Proof.
        unfold dot_product_arcnat. induction v; intros; simpl.
        right. intuition.
        apply gtx_plus_compat.
        apply IHv.
        change v with (Vtail (Vcons h v)). apply Vforall2n_tail. hyp.
        apply Vreln_tail_intro. hyp.
        apply gtx_mult_compat. change h with (Vhead (Vcons h v)). 
        do 2 rewrite Vhead_nth. apply Vforall2n_nth. hyp.
        do 2 rewrite Vhead_nth. apply Vforall2n_nth. hyp.
      Qed.

      Lemma mat_arctic_mult_mon :
        mgt M M' -> mge N N' -> mgt (M <*> N) (M' <*> N').

      Proof.
        intros. unfold mat_forall2_arcnat. intros.
        do 2 rewrite mat_mult_spec_arcnat. apply arctic_dot_product_mon.
        apply Vforall2n_intro. intros. 
        exact (H i i0 ip ip0).
        unfold vge. apply Vforall2n_intro. intros.
        do 2 rewrite <- get_elem_swap_arcnat. exact (H0 i0 j ip0 jp).
      Qed.

    End Matrix.
    
    Lemma mat_vec_prod_gt_compat : forall (M M' : mat) m m', 
      mat_gt M M' -> m >=v m' -> 
      vec_gt (mat_vec_prod_arcnat M m) (mat_vec_prod_arcnat M' m').

    Proof.
      intros. unfold mat_vec_prod_arcnat, vec_gt. apply Vforall2n_intro. 
      intros. do 2 rewrite Vnth_col_mat_arcnat.
      apply mat_arctic_mult_mon. hyp.
      intros k l pk pl. do 2 rewrite vec_to_col_mat_spec_arcnat.
      apply Vforall2n_nth. hyp.
    Qed.
    
    Variable mi_eval_ok : forall f v,
      vec_invariant_arcnat (mi_eval_aux_arcnat 
        (trsInt_arcnat mc f) (Vmap dom2vec_arcnat v)).
    
    Notation I := (I_arcnat mc mi_eval_ok).
    Notation IR_succ := (IR I succ).
    
    Lemma mint_eval_mon_succ : forall (val : valuation I) k 
      (mi mi' : mint k), mint_gt mi mi' -> 
      succ_vec (mint_eval_arcnat val mi) (mint_eval_arcnat val mi').

    Proof.
      intros. unfold succ_vec. apply Vforall2n_intro. intros. destruct H.
      eapply gtx_mor.
      apply (Vnth_mor eqAr);
      rewrite mint_eval_split_arcnat; refl.
      apply (Vnth_mor eqAr). rewrite mint_eval_split_arcnat. refl.
      do 2 rewrite vector_plus_nth_arcnat.
      apply gtx_plus_compat. 
      apply Vforall2n_nth. hyp.
      do 2 rewrite add_vectors_nth_arcnat.
      apply Vfold_left_gtx_compat. intros.
      do 2 rewrite Vnth_map. do 2 rewrite Vnth_map2.
      set (eval := Vnth (Vbuild (fun i (_ : i < k) => val i)) ip0).
      apply Vforall2n_nth. apply mat_vec_prod_gt_compat.
      apply Vforall2n_nth. hyp.
      apply vec_ge_refl_arcnat.
    Qed.

    Lemma term_gt_incl_succ : term_gt << IR_succ.

    Proof.
      intros l r lr v. destruct (mint_eval_equiv_arcnat l r v). simpl in *.
      unfold succ. unfold succ_vec.
      symmetry in H. symmetry in H0.
      rewrite (Vforall2n_mor sid_theoryAr gtx_mor H H0).
      apply mint_eval_mon_succ. hyp.
    Qed.
    
    Definition succ' := term_gt.
    Definition succ'_sub := term_gt_incl_succ.
    Definition succ'_dec := term_gt_dec_arcnat mc mint_gt mint_gt_dec.

  End ABI.
  
  (** Arctic integer numbers. *)
  
  Section ABZ.

    Notation mat := (matrix_arcbz dim dim).
    Notation "x >> y" := (gtrbz x y) (at level 70).
    Notation "x >>= y" := (gerbz x y) (at level 70).
    Notation "x =A= y" := (eqArbz x y) (at level 70).
    Definition gtx_bz x y := x >> y \/ (x =A= MinusInfBZ /\ y =A= MinusInfBZ).
    Notation "x >_0 y" := (gtx_bz x y) (at level 70).
    Notation "x + y " := (Aplusrbz x y).
    Notation "x * y " := (Amultrbz x y).    
    Variable ge_gt_eq : forall x y, x >>= y -> x >> y \/ x =A= y.

    (* Define morphism for gtxbz *)

    Add Morphism gtx_bz with signature eqArbz ==> eqArbz ==> iff as gtx_morbz.
    Proof.
      unfold gtx_bz. intuition. left. rewrite <- H.
      rewrite <- H0. hyp. right.
      split. trans x. sym. hyp. hyp. trans x0. sym.
      hyp. hyp.
      left. rewrite H. rewrite H0. hyp. right. split.
      trans y; hyp. trans y0; hyp.
    Qed.

    Lemma ge_gtx_compat_bz : forall x y z, x >>= y -> y >_0 z -> x >_0 z.
      
    Proof.
      unfold gtx_bz. intuition. left. apply ge_gt_compatrbz with y; hyp.
      unfold eqArbz in H2. 
      rewrite H2. rewrite H0 in H. destruct (ge_gt_eq H); intuition.
    Qed.

    (* Define gtx_plus_compat_bz *)

    Variable gtx_plus_compat_bz : forall m m' n n',
                                 m >_0 m' -> n >_0 n' -> m + n >_0 m' + n'.

    Variable gtx_mult_compat_bz : forall m m' n n',
      m >_0 m' -> n >>= n' -> m * n >_0 m' * n'.

    Definition succ_vecbz {n} := Vreln gtx_bz (n:=n).

    Definition succbz (x y : dom_arcbz dim) :=
      succ_vecbz (dom2vec_arcbz x) (dom2vec_arcbz y).

    (* Proving Vfold_left_gtx_compat_bz *)

    Lemma Vfold_left_gtx_compat_bz : forall n (v v' : vector Arbz n),
      (forall i (ip: i < n), Vnth v ip >_0 Vnth v' ip) ->
      Vfold_left Aplusrbz A0rbz v >_0 Vfold_left Aplusrbz A0rbz v'.
      
    Proof.
      induction v; simpl; intros.
      VOtac. simpl. right. intuition. unfold A0rbz. refl.
      unfold A0rbz. refl.
      VSntac v'. simpl. apply gtx_plus_compat_bz.
      apply IHv. intros. 
      apply Vforall2n_nth. change v with (Vtail (Vcons h v)). 
      apply Vforall2n_tail. apply Vforall2n_intro. hyp.
      change h with (Vhead (Vcons h v)). do 2 rewrite Vhead_nth.
      apply (H _ (Lt.lt_O_Sn n)).
    Qed.

    Definition mat_gtbz := mat_forall2_arcbz gtx_bz (m:=dim) (n:=dim).

    Definition vec_gtbz := Vforall2n gtx_bz (n:=dim).

    Notation matrixInt := (matrixInt_arcbz matrix_arcbz).

    Notation mint := (matrixInt dim).

    Definition mint_gtbz n (l r : mint n) := 
      Vforall2n mat_gtbz (args_arcbz l) (args_arcbz r) /\ 
      vec_gtbz (const_arcbz l) (const_arcbz r).

    Variable mc : MatrixMethodConf_arcbz Sig dim.

    Definition term_gtbz := term_ord_arcbz mc mint_gtbz.

    Definition succ'bz := term_gtbz.

    Definition dom2vec_arcbz (d : dom_arcbz dim) := dom2vec_arcbz d.
    
    (* Proving mat_vec_prod_gt_compat_bz. *)

    Infix ">=v" := vec_ge_arcbz (at level 70).
    Notation vgebz := vec_ge_arcbz.
    Notation vgtbz := (Vforall2n gtx_bz).
    Infix "<*>" := mat_mult_arcbz (at level 40).
    Notation mgebz := mat_ge_arcbz.
    Notation mgtbz := (mat_forall2_arcbz gtx_bz).

    Lemma arctic_dot_product_mon_bz : forall i (v v' w w' : vector ArcticBZDom i), 
      vgtbz v v' -> vgebz w w' ->
      dot_product_arcbz v w >_0 dot_product_arcbz v' w'.
    
    Proof.
      unfold dot_product_arcbz. induction v; intros; simpl.
      right. intuition. unfold A0rbz. refl. unfold A0rbz. refl.
      apply gtx_plus_compat_bz.
      apply IHv.
      change v with (Vtail (Vcons h v)). apply Vforall2n_tail. hyp.
      apply Vreln_tail_intro. hyp.
      apply gtx_mult_compat_bz. change h with (Vhead (Vcons h v)).
      do 2 rewrite Vhead_nth. apply Vforall2n_nth. hyp.
      do 2 rewrite Vhead_nth. apply Vforall2n_nth. hyp.
    Qed.

    Lemma mat_arctic_mult_mon_bz : forall (m n p: nat) (M M': matrix_arcbz m n)
                                       (N N': matrix_arcbz n p),
        mgtbz M M' -> mgebz N N' -> mgtbz (M <*> N) (M' <*> N').
      Proof.
        intros. unfold mat_forall2_arcbz. intros.
        do 2 rewrite mat_mult_spec_arcbz. apply arctic_dot_product_mon_bz.
        apply Vforall2n_intro. intros.
        exact (H i i0 ip ip0).
        unfold vgebz. apply Vforall2n_intro. intros.
        do 2 rewrite <- get_elem_swap_arcbz. exact (H0 i0 j ip0 jp).
      Qed.

    Lemma mat_vec_prod_gt_compat_bz : forall (M M' : matrix_arcbz dim dim)
      (m m': vector ArcticBZDom dim), 
      mat_gtbz M M' -> m >=v m' ->
      vec_gtbz (mat_vec_prod_arcbz M m) (mat_vec_prod_arcbz M' m').

    Proof.
      intros. unfold mat_vec_prod_arcbz, vec_gtbz. apply Vforall2n_intro.
      intros. do 2 rewrite Vnth_col_mat_arcbz.
      apply mat_arctic_mult_mon_bz. hyp.
      intros k l pk pl. do 2 rewrite vec_to_col_mat_spec_arcbz.
      apply Vforall2n_nth. hyp.
    Qed.
    
    Variable mi_eval_ok : forall f v,
      vec_invariant_arcbz (mi_eval_aux_arcbz
        (trsInt_arcbz mc f) (Vmap dom2vec_arcbz v)).

    Definition I := I_arcbz mc mi_eval_ok.
    Notation IR_succ := (IR I succbz).

    (* proving mint_eval_mon_succ_bz *)

    Lemma mint_eval_mon_succ_bz : forall (val : valuation I) k 
      (mi mi' : mint k), mint_gtbz mi mi' -> 
      succ_vecbz (mint_eval_arcbz val mi) (mint_eval_arcbz val mi').

    Proof.
      intros. unfold succ_vecbz. apply Vforall2n_intro. intros. destruct H.
      eapply gtx_morbz.
      apply (Vnth_mor eqArbz);
      rewrite mint_eval_split_arcbz; refl.
      apply (Vnth_mor eqArbz). rewrite mint_eval_split_arcbz. refl.
      do 2 rewrite vector_plus_nth_arcbz.
      apply gtx_plus_compat_bz. 
      apply Vforall2n_nth. hyp.
      do 2 rewrite add_vectors_nth_arcbz.
      apply Vfold_left_gtx_compat_bz. intros.
      do 2 rewrite Vnth_map. do 2 rewrite Vnth_map2.
      set (eval := Vnth (Vbuild (fun i (_ : i < k) => val i)) ip0).
      apply Vforall2n_nth. apply mat_vec_prod_gt_compat_bz.
      apply Vforall2n_nth. hyp.
      apply vec_ge_refl_arcbz.
    Qed.

    Lemma term_gt_incl_succbz : term_gtbz << IR_succ.
    Proof.
      intros l r lr v. destruct (mint_eval_equiv_arcbz l r v). simpl in *.
      unfold succ. unfold succ_vec.
      symmetry in H. symmetry in H0. 
      rewrite (Vforall2n_mor sid_theoryArbz gtx_morbz H H0).
      apply mint_eval_mon_succ_bz. hyp. 
    Qed.

    Definition succ'_subbz := term_gt_incl_succbz.

    Lemma gtx_decbz : rel_dec gtx_bz.
      
    Proof.
      intros x y. destruct (gt_decrbz x y).
      left. left. hyp.
      destruct (eqA_decrbz x MinusInfBZ).
      destruct (eqA_decrbz y MinusInfBZ).
      left. right. auto.
      right. unfold gtx_bz. intuition.
      right. unfold gtx_bz. intuition.
    Defined.

    Lemma mat_gt_decbz : rel_dec mat_gtbz.
      
    Proof.
      unfold mat_gtbz. apply mat_forall2_dec_arcbz. exact gtx_decbz.
    Defined.

    Lemma vec_gt_decbz : rel_dec vec_gtbz.
      
    Proof.
      unfold vec_gtbz. apply Vforall2n_dec. exact gtx_decbz.
    Defined.

    Lemma mint_gt_decbz : forall n, rel_dec (@mint_gtbz n).
      
    Proof.
      intros n x y. unfold mint_gtbz.
      destruct (Vforall2n_dec mat_gt_decbz (args_arcbz x) (args_arcbz y)); 
        intuition.
      destruct (vec_gt_decbz (const_arcbz x) (const_arcbz y)); intuition.      
    Defined.
    
    Definition succ'_decbz := term_gt_dec_arcbz mc mint_gtbz mint_gt_decbz. 
    Definition succeqbz := @succeq_arcbz dim.
    Definition succeq'bz := @succeq_arcbz' Sig dim mc.
    Definition succeq'_subbz := @succeq'_sub_arcbz Sig dim mc mi_eval_ok.
    Definition succeq'_decbz := @succeq'_dec_arcbz Sig dim mc.
    Definition refl_succeqbz := @refl_succeq_arcbz dim.
    Definition monotone_succeqbz :=
      @monotone_succeq_arcbz Sig dim mc mi_eval_ok.
    Definition trans_succeqbz := @trans_succeq_arcbz dim.
    
    Lemma gtx_transbz : transitive gtx_bz.
      
    Proof.
      unfold gtx_bz. intros x y z. intuition.
      left. apply gt_transrbz with y; hyp.
      unfold eqArbz in H2. rewrite H2.
      rewrite H0 in H1. auto.
      unfold eqArbz in H. rewrite H.
      rewrite H2 in H1.
      auto.
    Qed.

    Lemma trans_succbz : transitive succbz.

    Proof.
      unfold succbz. apply Rof_trans with (f:=dom2vec_arcbz).
      unfold succ_vec.
      apply Vreln_trans. apply gtx_transbz.      
    Qed.

    Lemma succ_succeq_compatbz : absorbs_left succbz succeqbz.
      
    Proof.
      intros x z xz. destruct xz as [y [xy yz] ].
      unfold succ, succ_vec. apply Vforall2n_intro. intros.
      apply ge_gtx_compat_bz with (Vnth (dom2vec_arcbz y) ip).
      apply Vforall2n_nth. hyp.
      apply Vforall2n_nth. hyp.
    Qed.

  End ABZ.
  
End S.