(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski and Johannes Waldmann, 2008-01
*)

Set Implicit Arguments.

Require Import Matrix2 AMonAlg2 AArcticBasedInt2 VecUtil OrdSemiRing2
  SN RelUtil ZArith AMatrixBasedInt2_ArcticBZ LogicUtil VecArith2.

Definition matrixInt := @matrixInt_arcbz matrix_arcbz.
Definition mkMatrixInt := @mkMatrixInt_arcbz matrix_arcbz.

(** Condition for an arctic BZ interpretation to be valid. *)

Section S.

  Variable Sig : Signature.
  Variable dim : nat.

  Variable mc : MatrixMethodConf_arcbz Sig dim.
  Notation "x >>= y" := (gerbz x y) (at level 70).
  
  Section Absolute_finite.
  
    Definition absolute_finite n (fi : matrixInt dim n) := 
      Vnth (const_arcbz fi) (dim_pos dim) >>= A1rbz.

    Definition babsolute_finite n (fi : matrixInt dim n) :=
      is_above_zero (Vnth (const_arcbz fi) (dim_pos dim)).
    
    Lemma babsolute_finite_ok : forall n (fi : matrixInt dim n),
      babsolute_finite fi = true <-> absolute_finite fi.
      
    Proof.
      intros. unfold babsolute_finite, absolute_finite.
      rewrite is_above_zero_ok. tauto.
    Qed.
    
    Require Import List ListForall.
 
    Variable Fs : list Sig.
    Variable Fs_ok : forall f : Sig, In f Fs.
    
    Lemma fin_absolute_finite :
      forallb (fun f => babsolute_finite (trsInt_arcbz mc f)) Fs = true ->
      forall f : Sig, absolute_finite (trsInt_arcbz mc f).
      
    Proof.
      rewrite forallb_forall. intros H f. rewrite <- babsolute_finite_ok.
      apply H. apply Fs_ok.
    Qed.
    
  End Absolute_finite.

  (** Module type for proving termination with matrix interpretations. *)
  
  Local Open Scope Z_scope.
  
  Section ArcticBZInt.
    
    Parameter trsIntOk : forall f : Sig, absolute_finite (trsInt_arcbz mc f).
    
    Section MonotoneAlgebra.
      
      Definition dom2vec_arcbz (d : dom_arcbz dim) := dom2vec_arcbz d.
      
      Lemma mi_eval_at0 : forall n (mi : matrixInt dim n)
        (v : vector (dom_arcbz dim) n),
        absolute_finite mi ->
        vec_at0_arcbz  (mi_eval_aux_arcbz
          mi (Vmap dom2vec_arcbz v)) >>= A1rbz.
        
      Proof.
        intros. unfold mi_eval_aux_arcbz, vec_at0_arcbz.
        rewrite vector_plus_nth_arcbz. rewrite A_plus_commrbz. 
        apply arctic_plus_ge_monotone. exact H.
      Qed.
      
      Notation "x >> y" := (gtrbz x y) (at level 70).
      Notation "x >>= y" := (gerbz x y) (at level 70).
      Notation "x =A= y" := (eqArbz x y) (at level 70).
      
      Definition gtx_bz x y := x >> y \/
        (x =A= MinusInfBZ /\ y =A= MinusInfBZ).

      Notation "x >_0 y" := (gtx_bz x y) (at level 70).
      Notation "x + y " := (Aplusrbz x y).
      Notation "x * y " := (Amultrbz x y).

      Lemma gtx_plus_compat : forall m m' n n',
        m >_0 m' -> n >_0 n' -> m + n >_0 m' + n'.
        
      Proof.
        intros. destruct H. destruct H0.
        left. apply plus_gt_compatrbz; hyp.
        destruct H0. rewrite H0. rewrite H1.
        do 2 rewrite A_plus_0_rbz. left. hyp.
        destruct H. rewrite H. rewrite H1.
        do 2 rewrite A_plus_0_lbz. hyp.
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
        left. simpl. injection H0. intro. subst z1. simpl in H. omega.
      Qed.
      
      Lemma mi_eval_ok : forall f v,
        vec_invariant_arcbz (mi_eval_aux_arcbz
          (trsInt_arcbz mc f) (Vmap dom2vec_arcbz v)).
        
      Proof.
        intros. unfold vec_invariant_arcbz, vec_at0_arcbz. 
        set (w := mi_eval_at0). unfold vec_at0_arcbz in w. apply w.
        apply trsIntOk.
      Qed.
      
      Definition I := I_arcbz mc mi_eval_ok.

      Definition succ := @AArcticBasedInt2.succbz dim.

      Definition succ' := @AArcticBasedInt2.succ'bz Sig dim mc.

      Definition succ'_sub :=
        @AArcticBasedInt2.succ'_subbz Sig dim  gtx_plus_compat gtx_mult_compat mc mi_eval_ok. 

      Definition succ'_dec := @AArcticBasedInt2.succ'_decbz Sig dim mc.

      Definition succeq := @succeq_arcbz dim.

      Definition succeq' := @succeq_arcbz' Sig dim mc.

      Definition succeq'_sub := @succeq'_sub_arcbz Sig dim mc mi_eval_ok.

      Definition succeq'_dec := @succeq'_dec_arcbz Sig dim mc.

      Definition refl_succeq := @refl_succeq_arcbz dim.

      Definition monotone_succeq :=
        @monotone_succeq_arcbz Sig dim mc mi_eval_ok.

      Definition trans_succeq := @trans_succeq_arcbz dim.

      Definition trans_succ := @AArcticBasedInt2.trans_succbz dim.

      Definition succ_succeq_compat :=
        @AArcticBasedInt2.succ_succeq_compatbz dim ge_gt_eqrbz.
      
      Lemma succ_wf : WF succ.
        
      Proof.
        apply wf_transp_WF.
        unfold succ, transp.
        apply well_founded_lt_compat with (f := 
          (fun d: dom_arcbz dim => 
            match vec_at0_arcbz (dom2vec_arcbz d) with
              | Fin x => Zabs_nat x
              | MinusInfBZ => 0%nat
            end
          )
        ).
        intros x y xy. destruct x. destruct y. simpl. 
        cut (gerbz (vec_at0_arcbz x) A1rbz). 2: hyp.
        cut (gerbz (vec_at0_arcbz x0) A1rbz). 2: hyp.
        cut (gtx_bz (vec_at0_arcbz x0) (vec_at0_arcbz x)).
        gen (vec_at0_arcbz x0). gen (vec_at0_arcbz x).
        clear x x0 v v0 xy. intros x y xy x_lb y_lb.
        destruct x; destruct y.
        (*FIXME: this should be solved by arctic_ord *)
        unfold A1rbz in *.
        assert (z >= 0).
        apply fin_ge_impl_ge; hyp.
        assert (z0 >= 0).
        apply fin_ge_impl_ge; hyp.
        destruct xy. simpl in H1.
        apply Zabs_nat_lt. omega.
        destruct H1; discr.
        destruct x_lb; [ contr | discr ].
        destruct y_lb; [ contr | discr ].
        destruct y_lb; [ contr | discr ].
        unfold vec_at0_arcbz. apply Vforall2n_nth. hyp.
      Qed.
      
      (** Define record type for MonotoneAlgType for domain arctic
         natural numbers. *)
      
      Definition matAlg_arcbz := mkbMonoAlgType Sig I succ succeq refl_succeq
        trans_succ trans_succeq monotone_succeq succ_wf succ_succeq_compat
        succ' succeq' succ'_sub succeq'_sub succ'_dec succeq'_dec.
      
    End MonotoneAlgebra.
    
    (** Tactics *)
    
    Ltac prove_cc_succ Fs_ok :=
      fail 10 "arctic matrices cannot be used for proving total termination".
    
  End ArcticBZInt.
  
  Implicit Arguments fin_absolute_finite [Fs].
  
  Ltac absolute_finite Fs_ok :=
    apply (fin_absolute_finite _ _ Fs_ok);
      (check_eq || fail 10 "invalid below-zero arctic interpretation").

End S.