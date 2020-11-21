(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-04-29 (bigN)
- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski and Hans Zantema, 2007-03-22

* Termination criterion based on matrix interpretations.

References:
-  J. Endrullis, J. Waldmann and H. Zantema, "Matrix Interpretations for 
   Proving Termination of Term Rewriting", Proceedings of the 3rd 
   International Joint Conference (IJCAR 2006), 2006.
*)

Set Implicit Arguments.

Require Import LogicUtil Setoid Matrix2 VecUtil AMonAlg2 SN RelUtil
  AWFMInterpretation VecEq NatUtil VecOrd AMatrixBasedInt2_Nat
  VecArith2 OrdSemiRing2.

(***********************************************************************)
(** * Proving termination with matrix interpretation over domain
natural numbers. *)

Section S.

  Variable Sig : Signature.
  Variable dim : nat.
  Notation vec := (vector AN dim).

  Definition matrixInt := @matrixInt matrix.
  Definition mkMatrixInt := @mkMatrixInt matrix.
  
  Section MonotoneAlgebra.
    
    Variable m : MatrixMethodConf Sig dim.
    Notation mint := (matrixInt dim).
    Notation vec_invariant := (vec_invariant).
    Notation mi_eval_aux := (mi_eval_aux ).
    Notation trsInt := (trsInt m).

    Definition dom2vec (d: dom dim) := (dom2vec d).
    Parameter mi_eval_ok : forall f v,
      vec_invariant (mi_eval_aux (trsInt f) (Vmap dom2vec v)).
    Definition I := I m mi_eval_ok.
    Definition succeq (d : dom dim) := succeq d.
    Definition refl_succeq (d : dom dim) := refl_succeq d.
    Definition monotone_succeq :=
      @monotone_succeq Sig dim m mi_eval_ok.
    Definition trans_succeq (d : dom dim) := trans_succeq d.
    Definition succeq' := succeq' m.
    Definition succeq'_sub := @succeq'_sub Sig dim m mi_eval_ok.   
    Definition succeq'_dec := succeq'_dec m.
    Infix ">=v" := vec_ge (at level 70).
    Definition succ_vec (v1 v2: vector nat dim) :=
      v1 >=v v2 /\ vec_at0 v1 > vec_at0 v2.
    Definition succ v1 v2 := succ_vec (dom2vec v1) (dom2vec v2).

    Lemma succ_wf : WF succ.

    Proof.
      apply WF_incl with (Rof gtN 
        (fun v : dom dim => vec_at0 (dom2vec v))).
      unfold succ, succ_vec, Rof, gtN. intros x y. intuition.
      apply WF_inverse. apply gt_WF.
    Qed.

    Lemma trans_succ : transitive succ.

    Proof.
      unfold succ. apply Rof_trans with (f:=dom2vec).
      unfold succ_vec.
      intros v1 v2 v3 h12 h23. intuition.
      apply vec_ge_trans with v2; hyp.
    Qed.

    Lemma succ_succeq_compat : absorbs_left succ succeq.

    Proof.
      intros x z xz. destruct xz as [y [xy yz]]. split.
      apply trans_succeq with y. hyp. destruct yz. hyp.
      apply ge_gt_compatN with (Vnth (dom2vec y)
        (dim_pos dim)). unfold vec_at0.
      apply Vforall2n_nth. hyp. 
      destruct yz. hyp.
    Qed.

    Lemma succ_dec : rel_dec succ.
      
    Proof.
      apply intersection_dec. apply succeq_dec. intros x y.
      apply NatUtil.gt_dec.
    Defined.

    Notation IR_succ := (IR I succ).

    Require Import ATrs.

    Definition rule_mi l r := rule_mi m (@mkRule Sig l r).
    Definition mint_gt n (l r : mint n) := 
      mint_ge l r /\ vec_at0 (const l) > vec_at0 (const r).
    Definition term_gt := term_gt m mint_gt.
    Infix "[+]" := vector_plus (at level 50).

    Lemma vec_plus_gt_compat_l : forall (vl vl' vr vr': vector nat dim),
      vec_at0 vl >= vec_at0 vl' -> vec_at0 vr > vec_at0 vr' -> 
      vec_at0 (vl [+] vr) > vec_at0 (vl' [+] vr').

    Proof.
      unfold vec_at0, vector_plus. intros.
      do 2 rewrite Vnth_map2.
      unfold Aplus. apply plus_gt_compat_rN; hyp.
    Qed.

    Lemma mint_eval_mon_succ : forall (val : valuation I) k 
      (mi mi' : mint k), mint_gt mi mi' -> 
      succ_vec (mint_eval val mi) (mint_eval val mi').

    Proof.
      intros. destruct H. split.
      apply mint_eval_mon_succeq. hyp.
      unfold mint_eval, add_vectors. simpl.
      apply vec_plus_gt_compat_l. 
      unfold vec_at0.
      apply Vforall2n_nth. 
      exact (mint_eval_mon_succeq_args _ H). hyp.
    Qed.

    Notation vec := (vector AN).

    Add Parametric Relation n : (vec n) (@eq_vec n) reflexivity proved
      by (@eq_vec_refl AN eqAN sid_theoryAN n) symmetry proved by
      (@eq_vec_sym AN eqAN sid_theoryAN n) transitivity proved by
      (@eq_vec_trans AN eqAN sid_theoryAN n) as eq_vec_rel.

    Add Parametric Morphism n : (@vec_ge n) with signature (@eq_vec n)
      ==> (@eq_vec n) ==> iff as vec_ge_mor.
      
    Proof.
      unfold vec_ge. intros.
      apply (Vforall2n_mor sid_theoryAN). intuition.
      trans a1. apply eq_ge_compatN. sym. hyp.
      trans a2. hyp. apply eq_ge_compatN. hyp.
      trans a1'. apply eq_ge_compatN. hyp.
      trans a2'. hyp. apply eq_ge_compatN. sym. hyp.
      hyp. hyp.
    Qed.
    
    Implicit Arguments vec_ge_mor [n x y x0 y0].

    Lemma term_gt_incl_succ : term_gt << IR_succ.

    Proof.
      intros l r lr v. destruct (mint_eval_equiv l r v). simpl in * .
      unfold succ, I, succ_vec. symmetry in H. symmetry in H0.
      rewrite (vec_ge_mor H H0).
      rewrite (Vnth_mor _ H (dim_pos dim)). 
      rewrite (Vnth_mor _ H0 (dim_pos dim)).
      change (succ_vec (mint_eval v
        (mi_of_term  m (ABterm.inject_term
          (Max.le_max_l (maxvar l) (maxvar r)))))
      (mint_eval v (mi_of_term m
        (ABterm.inject_term (Max.le_max_r (maxvar l) (maxvar r)))))).
      apply mint_eval_mon_succ. hyp.
    Qed.

    Lemma mint_gt_dec : forall n, rel_dec (@mint_gt n).
      
    Proof.
      intro. apply intersection_dec. apply mint_ge_dec.
      intros x y. apply NatUtil.gt_dec.
    Defined.

    Definition succ' := term_gt.
    Definition succ'_sub := term_gt_incl_succ.
    Definition succ'_dec := term_gt_dec m mint_gt mint_gt_dec.

    (** Define record type for MonotoneAlgType. *)

    Definition matAlg := mkbMonoAlgType Sig I succ succeq refl_succeq
      trans_succ trans_succeq monotone_succeq succ_wf
      succ_succeq_compat succ' succeq' succ'_sub succeq'_sub succ'_dec
      succeq'_dec.

    Section ExtendedMonotoneAlgebra.
      
      Section VecMonotonicity.

        Lemma vec_plus_gt_compat_r : forall (vl vl' vr vr': vector nat
          dim), vec_at0 vl > vec_at0 vl' -> vec_at0 vr >= vec_at0 vr'
          -> vec_at0 (vl [+] vr) > vec_at0 (vl' [+] vr').

        Proof.
          unfold vec_at0, vector_plus.
          intros. simpl. do 2 rewrite Vnth_map2. 
          unfold Aplus, Peano.gt. apply plus_gt_compat_lN; hyp.
        Qed.

        Notation vec := (vector AN dim).

        Variable f : matrix dim dim -> vec -> vec.

        Variable f_mon : forall M v1 v2, get_elem M (dim_pos dim)
          (dim_pos dim) > 0 -> v1 >=v v2 -> vec_at0 v1 > vec_at0 v2 ->
          vec_at0 (f M v1) > vec_at0 (f M v2).

        Variables (a b : vec).

        Lemma vec_add_monotone_map2 : forall n1 (v1 : vector vec n1) n2 
          (v2 : vector vec n2)  n (M : vector (matrix dim dim) n) i_j,  
          Vforall (fun m => get_elem m (dim_pos dim) (dim_pos dim) > 0) M ->
          a >=v b -> vec_at0 a > vec_at0 b ->
          vec_at0 (add_vectors
            (Vmap2 f M (Vcast (Vapp v1 (Vcons a v2)) i_j))) >
          vec_at0 (add_vectors
            (Vmap2 f M (Vcast (Vapp v1 (Vcons b v2)) i_j))).

        Proof.
          induction v1; intros; simpl.
          destruct n; [absurd_arith | idtac]. 
          unfold add_vectors, vec_at0, vector_plus.
          simpl.
          do 2 rewrite Vnth_map2.
          unfold Aplus. apply plus_gt_compat_rN.
          apply eq_ge_compatN. refl.
          unfold vec_at0 in f_mon. apply f_mon; try hyp.
          apply (Vforall_in (x:=Vhead M) H). apply Vin_head.
          destruct n0; [absurd_arith | idtac]. unfold vec_at0.
          unfold add_vectors, vec_at0, vector_plus.
          simpl.
          do 2 rewrite Vnth_map2.
          unfold Aplus. apply plus_gt_compat_lN. 2:
          apply eq_ge_compatN; refl.
          match goal with |- ?Hl > ?Hr => fold (Hr > Hl) end.
          unfold vec_at0, add_vectors in IHv1.
          apply IHv1; try hyp.
          apply Vforall_incl with (S n0) M.
          intros. VSntac M. simpl. auto.
          hyp.
        Qed.

      End VecMonotonicity.

      Lemma dot_product_mon_r : forall i j (jp : (j < i)%nat) 
        (v v' w w' : vector nat i),
        v >=v v' -> w >=v w' -> Vnth v jp > A0N ->
        Vnth w jp > Vnth w' jp -> 
        dot_product v w > dot_product v' w'.

      Proof.
        intros i j. gen i. clear i.
        induction j; intros.
        destruct i. absurd_arith.
        VSntac v. VSntac w. VSntac v'. VSntac w'.
        unfold dot_product. simpl.
        fold (dot_product (Vtail v') (Vtail w')). 
        fold (dot_product (Vtail v) (Vtail w)).
        unfold Aplus, Peano.gt. apply plus_gt_compat_rN.
        apply dot_product_mon; apply Vreln_tail_intro; hyp.
        do 4 rewrite Vhead_nth. apply mult_lt_compat_lr.
        apply (Vforall2n_nth (R:=geN)). hyp.
        rewrite (lt_unique (lt_O_Sn i) jp). hyp.
        rewrite (lt_unique (lt_O_Sn i) jp). hyp.
        destruct i. absurd_arith.
        VSntac v. VSntac w. VSntac v'. VSntac w'.
        unfold dot_product. simpl.
        fold (dot_product (Vtail v') (Vtail w')). 
        fold (dot_product (Vtail v) (Vtail w)).
        unfold Aplus, Peano.gt. apply plus_gt_compat_lN.
        apply IHj with (lt_S_n jp).
        apply Vreln_tail_intro. hyp.
        apply Vreln_tail_intro. hyp.
        rewrite Vnth_tail. rewrite lt_nS_Sn. hyp.
        do 2 rewrite Vnth_tail. rewrite lt_nS_Sn. hyp.
        apply mult_le_compat.
        do 2 rewrite Vhead_nth. apply (Vforall2n_nth (R:=geN)). hyp.
        do 2 rewrite Vhead_nth. apply (Vforall2n_nth (R:=geN)). hyp.
      Qed.

      (** Additional property of interpretation required to ensure strict
         monotonicity of interpretations: upper left corner of every matrix
         needs to be positive. *)

      Definition monotone_interpretation n (fi : matrixInt dim n) :=
        Vforall (fun m => get_elem m (dim_pos dim) (dim_pos dim) > 0)
        (args fi).

      Definition bmonotone_interpretation n (fi : matrixInt dim n) :=
        bVforall (fun m => bgt_nat (get_elem m (dim_pos dim) (dim_pos
        dim)) 0) (args fi).

      Lemma bmonotone_interpretation_ok : forall n (fi : matrixInt dim
        n), bmonotone_interpretation fi = true <->
        monotone_interpretation fi.

      Proof.
        intros. apply bVforall_ok. intro. apply bgt_nat_ok.
      Qed.

      Lemma monotone_succ : (forall f : Sig, monotone_interpretation
        (trsInt f)) -> monotone I succ.

      Proof.
        intros H f i j i_j vi vj a b ab. split.
        apply monotone_succeq. destruct ab. hyp.
        simpl. apply vec_plus_gt_compat_r.
        do 2 rewrite Vmap_cast. do 2 rewrite Vmap_app. simpl.    
        apply vec_add_monotone_map2; try solve [destruct ab; hyp].
        intros. unfold vec_at0.
        unfold mat_vec_prod. 
        do 2 rewrite Vnth_col_mat.
        do 2 rewrite mat_mult_spec.
        apply dot_product_mon_r with 0%nat (dim_pos dim).
        unfold vec_ge, ge. apply Vforall2n_intro. intros. apply le_refl.
        unfold vec_ge, ge. apply Vforall2n_intro. intros.
        do 2 rewrite get_col_col_mat. destruct ab.
        apply Vforall2n_nth. hyp.
        hyp.
        do 2 rewrite get_col_col_mat. hyp.
        apply H. apply le_refl.
      Qed.

      Require Import List ListForall.

      Section fin_Sig.

        Variable Fs : list Sig.
        Variable Fs_ok : forall f : Sig, In f Fs.

        Lemma fin_monotone_succ : forallb (fun f =>
          bmonotone_interpretation (trsInt f)) Fs = true -> monotone I
          succ.

        Proof.
          intro H. apply monotone_succ. intro f.
          rewrite <- bmonotone_interpretation_ok.
          rewrite forallb_forall in H. apply H. apply Fs_ok.
        Qed.

      End fin_Sig.
      
    End ExtendedMonotoneAlgebra.
    
  End MonotoneAlgebra.
  
  Implicit Arguments fin_monotone_succ [Fs].
  
  Ltac prove_cc_succ Fs_ok :=
    apply IR_context_closed; apply (fin_monotone_succ Fs_ok);
      (check_eq || fail 10
         "could not prove the monotony of this matrix interpretation").
End S.