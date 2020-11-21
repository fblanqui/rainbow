(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frédéric Blanqui, 2009-03-19 (setoid), 2009-04-29 (bigN), 2014-02-25 (classes)
- Adam Koprowski and Hans Zantema, 2007-03-22

Termination criterion based on matrix interpretations.

References:
-  J. Endrullis, J. Waldmann and H. Zantema, "Matrix Interpretations for 
   Proving Termination of Term Rewriting", Proceedings of the 3rd 
   International Joint Conference (IJCAR 2006), 2006.
*)

Set Implicit Arguments.

Require Import LogicUtil Setoid Matrix2 OrdSemiRing2 VecUtil AMonAlg2
  SN RelUtil AWFMInterpretation NatUtil AMatrixBasedInt2 Nat_as_OSR
  VecArith2 ABterm Max.

Section MatrixInt.

  Variable Sig: Signature.

  Variable dim: nat.

  Context {MI : TMatrixInt (OSR:=Nat_as_OSR) Sig dim}.

  (** Notations *)

  Notation dim_pos := (dim_pos dim).
  Notation vec     := (vector nat dim).
  Notation vec_ge  := (Vforall2 ge).
  Infix ">=v"      := vec_ge (at level 70).
  
  (* Define [vec_at0] of type [nat]. *)

  Definition vec_at0       (v: vec)               := Vnth v dim_pos.
  
  Definition vec_invariant (v : vector s_typ dim) := True.
  
  Lemma inv_id_matrix : vec_invariant (id_vec dim_pos).
  
  Proof. compute. trivial. Qed.
  
  Global Instance Conf : MatrixMethodConf Sig dim.
  
  Proof.
    eapply Build_MatrixMethodConf. apply MI.
    apply inv_id_matrix.
  Defined.

  Notation mint := (@matrixInt _ dim).

  Lemma mi_eval_ok : forall f v,
    vec_invariant (mi_eval_aux (mi_trsInt f)
    (Vmap (@dom2vec Nat_as_OSR Sig dim _) v)).

  Proof. unfold vec_invariant. auto. Qed.
    
  Definition succ_vec v1 v2 := v1 >=v v2 /\ vec_at0 v1 > vec_at0 v2.
  Definition succ           := Rof succ_vec (@dom2vec Nat_as_OSR Sig dim _).

  Lemma succ_wf : WF succ.
  
  Proof.
    apply WF_incl with (Rof gt (fun v : (@dom Nat_as_OSR Sig dim _ ) =>
                       vec_at0 (dom2vec v))).
    unfold succ, succ_vec, Rof, gt. intros x y. intuition.
    apply WF_inverse. apply gt_WF.
  Qed.

  Global Instance trans_succ : Transitive succ.
  
  Proof.
    apply Rof_trans. unfold succ_vec.
    intros v1 v2 v3 h12 h23. intuition.
    trans v2; hyp.
  Qed.
  
  Lemma succ_succeq_compat : absorbs_left succ (@succeq Nat_as_OSR Sig dim _).
  
  Proof.
    intros x z xz. destruct xz as [y [xy yz]]. split.
    apply trans_succeq with y. hyp. destruct yz. hyp.
    apply ge_gt_compat with (Vnth (dom2vec y) dim_pos).
    unfold vec_at0.
    apply Vforall2_elim_nth. hyp. 
    destruct yz. hyp.
  Qed.
  
  Lemma succ_dec : rel_dec succ.
  
  Proof.
    apply intersection_dec.
    (* Remark: being able to apply the lemma [succeq_dec] change it
      form first. *)
    change (rel_dec (@succeq _ _ _ _)). apply succeq_dec.
    intros x y. apply gt_dec.
  Defined.
  
  Notation IR_succ := (IR (I mi_eval_ok) succ).
  
  Definition mint_gt n (l r : mint n) := 
    mint_ge l r /\ vec_at0 (const l) > vec_at0 (const r).

  Definition term_gt := term_gt mint_gt.
  
  Lemma vec_plus_gt_compat_l : forall vl vl' vr vr',
    vec_at0  vl         >= vec_at0  vl' ->
    vec_at0         vr  >  vec_at0          vr' -> 
    vec_at0 (vl [+] vr) >  vec_at0 (vl' [+] vr').
  
  Proof.
    unfold vec_at0, vector_plus. intros. do 2 rewrite Vnth_map2.
    unfold plus. apply plus_gt_compat_r; hyp.
  Qed.
  
  Lemma mint_eval_mon_succ : forall (val : valuation (I mi_eval_ok)) k 
    (mi mi' : mint k), mint_gt mi mi' -> 
    succ_vec (mint_eval val mi) (mint_eval val mi').

  Proof.
    intros. destruct H. split.
    apply mint_eval_mon_succeq with (mi_eval_ok := mi_eval_ok). hyp.
    unfold mint_eval, add_vectors. simpl.
    apply vec_plus_gt_compat_l. 
    unfold vec_at0. apply Vforall2_elim_nth. 
    exact (mint_eval_mon_succeq_args _ H). hyp.
  Qed.
    
  Lemma term_gt_incl_succ : term_gt << IR_succ.
  
  Proof.
    intros l r lr v. destruct (mint_eval_equiv l r v). simpl in * .
    unfold succ, succ_vec, Rof, vec_at0. 
    symmetry in H. symmetry in H0.
    rewrite (@vec_ge_mor Nat_as_OSR dim _ _ H _ _ H0).
    rewrite (Vforall2_elim_nth _ H),
    (Vforall2_elim_nth _ H0).
    change (succ_vec (mint_eval (mi_eval_ok:= mi_eval_ok) v
           (mi_of_term (inject_term (le_max_l (maxvar l) (maxvar r)))))
           (mint_eval (mi_eval_ok := mi_eval_ok) v (mi_of_term
           (inject_term (le_max_r (maxvar l) (maxvar r)))))).
    apply mint_eval_mon_succ. hyp.
  Qed.
  
  Lemma mint_gt_dec : forall n, rel_dec (@mint_gt n).
  
  Proof.
    intro. apply intersection_dec.
    apply (@mint_ge_dec Nat_as_OSR dim n).
    intros x y. apply gt_dec.
  Defined.
  
  Definition succ'     := term_gt.
  Definition succ'_sub := term_gt_incl_succ.
  Definition succ'_dec := term_gt_dec mint_gt mint_gt_dec.

  (* Add *)
  
  (* Boolean function of [mint_gt] of type natural numbers. *)
  
  Require Import BoolUtil.
  
  Definition bmint_gt_nat n (l r : mint n) : bool :=
    bmint_ge l r && (bgt _ (vec_at0 (const l))
                           (vec_at0 (const r))).
  
  (** Correctness proof of [bmint_gt] over domain natural numbers. *)
    
  Lemma bmint_gt_ok : forall n (l r : mint n),
    bmint_gt_nat l r = true <->
    mint_ge l r /\ vec_at0 (const l) > vec_at0 (const r).
    
  Proof.
    intros. intuition. apply bmint_ge_ok. unfold bmint_gt_nat in H.
    rewrite andb_eq in H. destruct H. apply H.
    unfold bmint_gt_nat in H. rewrite andb_eq in H.
    destruct H. apply bgt_ok in H0. apply H0.
    (* -> *)
    unfold bmint_gt_nat. rewrite andb_eq. split.
    apply bmint_ge_ok. apply H0.
    apply bgt_ok. apply H1.
  Qed.
  
  Section ExtendedMonotoneAlgebra.
    
    Section VecMonotonicity.
      
      Lemma vec_plus_gt_compat_r : forall vl vl' vr vr', 
        vec_at0  vl         >  vec_at0  vl' ->
        vec_at0         vr  >= vec_at0          vr' -> 
        vec_at0 (vl [+] vr) >  vec_at0 (vl' [+] vr').

      Proof.
        unfold vec_at0, vector_plus. intros.
        simpl. do 2 rewrite Vnth_map2. apply plus_gt_compat_l; hyp.
      Qed.
      
      Variable f     : matrix dim dim -> vec -> vec.
      Variable f_mon : forall M v1 v2, get_elem M dim_pos dim_pos > 0 ->
                     v1  >=v            v2 ->
        vec_at0      v1  > vec_at0      v2 -> 
        vec_at0 (f M v1) > vec_at0 (f M v2).
        
      Variables (a b : vec).
      
      Lemma vec_add_monotone_map2 : forall n1 (v1 : vector vec n1) n2 
       (v2 : vector vec n2)  n (M : vector (matrix dim dim) n) i_j,  
        Vforall (fun m => get_elem m dim_pos dim_pos > 0) M ->
                a >=v       b ->
        vec_at0 a > vec_at0 b ->
        vec_at0 (add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons a v2)) i_j))) >
        vec_at0 (add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons b v2)) i_j))).

      Proof.
        induction v1; intros; simpl.
        destruct n; [absurd_arith | idtac].
        unfold add_vectors, vec_at0, vector_plus. simpl.
        do 2 rewrite Vnth_map2.
        apply plus_gt_compat_r. apply eq_ge_compat. refl.
        unfold vec_at0 in f_mon. apply f_mon; try hyp.
        apply (Vforall_in (x:=Vhead M) H). apply Vin_head.
        destruct n0; [absurd_arith | idtac].
        unfold add_vectors, vec_at0, vector_plus. simpl.
        do 2 rewrite Vnth_map2.
        apply plus_gt_compat_l. 2: apply eq_ge_compat; refl.
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
           v          >=v v'         ->
           w          >=v w'         ->
      Vnth v jp       >   0          ->
      Vnth w jp       >   Vnth w' jp ->
      dot_product v w >   dot_product v' w'.

    Proof.
      intros i j. gen i. clear i.
      induction j; intros.
      destruct i. absurd_arith.
      VSntac v. VSntac w. VSntac v'. VSntac w'.
      unfold dot_product. simpl.
      apply plus_gt_compat_r.
      (* Remark: cannot apply dot_product_mon alone need to add
        @. *)
      apply (@dot_product_mon Nat_as_OSR); apply Vforall2_tail; hyp.
      do 4 rewrite Vhead_nth. apply mult_lt_compat_lr.
      apply (Vforall2_elim_nth (R:=ge)). hyp.
      rewrite (lt_unique (lt_O_Sn i) jp). hyp.
      rewrite (lt_unique (lt_O_Sn i) jp). hyp.
      destruct i. absurd_arith.
      VSntac v. VSntac w. VSntac v'. VSntac w'.
      unfold dot_product. simpl.
      apply plus_gt_compat_l.
      apply IHj with (lt_S_n jp).
      apply Vforall2_tail. hyp.
      apply Vforall2_tail. hyp.
      rewrite Vnth_tail. rewrite lt_nS_Sn. hyp.
      do 2 rewrite Vnth_tail. rewrite lt_nS_Sn. hyp.
      apply mult_le_compat.
      do 2 rewrite Vhead_nth. apply (Vforall2_elim_nth (R:=ge)). hyp.
      do 2 rewrite Vhead_nth. apply (Vforall2_elim_nth (R:=ge)). hyp.
    Qed.
    
    (* additional property of interpretation required to ensure strict
         monotonicity of interpretations: upper left corner of every matrix
         needs to be positive *)
    Definition monotone_interpretation n (fi : matrixInt dim n) := 
      Vforall (fun m => get_elem m dim_pos dim_pos > 0) (args fi).

    (*Definition bmonotone_interpretation n (fi : matrixInt dim n) := 
        bVforall (fun m => bgt_nat (get_elem m dim_pos dim_pos) 0) (args fi).*)
    
    Definition bmonotone_interpretation n (fi : matrixInt dim n) := 
      bVforall (fun m => bgt Nat_as_OSR (get_elem m dim_pos dim_pos) 0) (args fi).
    
    Lemma bmonotone_interpretation_ok : forall n (fi : matrixInt dim n),
      bmonotone_interpretation fi = true <-> monotone_interpretation fi.

    Proof.
      intros. apply bVforall_ok. intro. apply bgt_ok.
    Qed.
    
    Lemma monotone_succ : (forall f : Sig,
      monotone_interpretation (mi_trsInt f)) -> monotone (I mi_eval_ok) succ.

    Proof.
      intros H f i j i_j vi vj a b ab. split.
      (* Remark: without giving the argument [mi_eval_ok] apply the
        lemma [monote_succeq] coq will complain about the error
        [impossible to unify...]. *)
      apply monotone_succeq with (mi_eval_ok := mi_eval_ok).
      destruct ab. hyp.
      simpl. unfold mi_eval_aux. apply vec_plus_gt_compat_r.
      do 2 rewrite Vmap_cast. do 2 rewrite Vmap_app. simpl.    
      apply vec_add_monotone_map2; try solve [destruct ab; hyp].
      intros. unfold vec_at0. unfold mat_vec_prod. 
      do 2 rewrite (@Vnth_col_mat Nat_as_OSR).
      do 2 rewrite (@mat_mult_spec Nat_as_OSR).
      apply dot_product_mon_r with 0%nat dim_pos.
      apply Vforall2_intro_nth. intros. apply le_refl.
      apply Vforall2_intro_nth. intros.
      do 2 rewrite get_col_col_mat. destruct ab.
      apply Vforall2_elim_nth. hyp.
      hyp.
      do 2 rewrite get_col_col_mat. hyp.
      apply H. apply le_refl.
    Qed.
    
  End ExtendedMonotoneAlgebra.
  
    (* Define an [Instance] for Class [MonotoneAlgebraType]. Instead
    of define each filed as [Definition].
    For example: [Definition succeq := succeq.] etc. *)
    
  Global Instance MonotoneAlgebra : MonotoneAlgebraType Sig.
  
  Proof.
    apply Build_MonotoneAlgebraType with
    (ma_int     := I mi_eval_ok)
    (ma_succ    := succ)
    (ma_succeq  := @succeq _ _ _ _)
    (ma_succeq' := @succeq' _ _ _ _)
    (ma_succ'   := term_gt).
    apply refl_succeq.
    apply trans_succ.
    apply trans_succeq.
    apply monotone_succeq.
    apply succ_wf.
    apply succ_succeq_compat.
    apply term_gt_incl_succ.
    apply succeq'_sub.
    apply succ'_dec.
    apply succeq'_dec.
  Defined.

End MatrixInt.
