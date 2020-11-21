(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski and Johannes Waldmann, 2008-01
*)

Set Implicit Arguments.

Require Import Matrix2 OrdSemiRing2 VecUtil AMonAlg2
  SN RelUtil AWFMInterpretation LogicUtil AMatrixBasedInt2
  Bool VecArith2 AArcticBasedInt2 Arctic_as_OSR SemiRing BoolUtil NatUtil.

(***********************************************************************)
(** Condition for an arctic interpretation to be valid *)

Section Somewhere_finite.

  Variable Sig: Signature.
  Variable dim: nat.
  Context {MI : TMatrixInt (OSR:=Arctic_as_OSR) Sig dim}.

  Notation dim_pos := (dim_pos dim).
  Notation vec     := (vector ArcticDom dim).
  Notation vec_ge  := (Vforall2 ge).
  Infix ">=v"      := vec_ge (at level 70).
  Notation mint    := (@matrixInt _ dim).
  Notation mat     := (matrix dim dim).

  Definition somewhere_finite n (fi : mint n) := 
    Vexists (fun M : mat => get_elem M dim_pos dim_pos <> MinusInf)
                  (args fi) \/ Vnth (const fi) dim_pos <> MinusInf.
  
  Definition bsomewhere_finite n (fi : matrixInt dim n) :=
    bVexists (fun m => is_finite (get_elem m dim_pos dim_pos)) (args fi) ||
                       is_finite (Vnth (const fi) dim_pos).
  
  Lemma bsomewhere_finite_ok : forall n (fi : matrixInt dim n),
    bsomewhere_finite fi = true <-> somewhere_finite fi.

  Proof.
    intros. unfold bsomewhere_finite, somewhere_finite.
    rewrite orb_eq. rewrite is_finite_ok.
    rewrite bVexists_ok. refl. intro. apply is_finite_ok.
  Qed.

End Somewhere_finite.

(***********************************************************************)

Section S.
 
  Variable Sig: Signature.
  Variable dim: nat.
  
  Context {MI : TMatrixInt (OSR:=Arctic_as_OSR) Sig dim}.

  (* FIXME: make mar_trsIntOk as parameter then just use TMatrixInt as
  parameterize *)

  Parameter mar_trsIntOk : forall f: Sig, somewhere_finite (mi_trsInt f).

  Lemma mat_times_vec_at0_positive : forall n (m : matrix n n) 
    (v : vector s_typ n ) (dim_pos : n > 0),
    get_elem m dim_pos dim_pos <> MinusInf ->   
    Vnth v dim_pos <> MinusInf ->
    Vnth (@mat_vec_prod Arctic_as_OSR n n m v) dim_pos <> MinusInf.
  
  Proof.
    destruct n; intros. absurd_arith.
    VSntac v. unfold matrix in m. VSntac m. 
    unfold mat_vec_prod, col_mat_to_vec, get_col. rewrite Vnth_map. 
    set (w := mat_mult_spec). unfold get_elem, get_row in w. rewrite w.
    simpl. VSntac (Vhead m). unfold dot_product. 
    simpl.
    rewrite A_plus_comm. apply arctic_plus_notInf_left.
    apply arctic_mult_notInf. 
    rewrite H2 in H. unfold get_elem in H. simpl in H.
    rewrite Vhead_nth. erewrite <- Vnth_eq. apply H. auto.
    (*rewrite <- (Vnth_eq (Vhead m) dim_pos (lt_O_Sn n)); trivial.*)
    rewrite H1 in H0. hyp.
  Qed.

  Notation "x >_0 y" := (gtx x y) (at level 70).

  Lemma gtx_plus_compat : forall m m' n n',
    m >_0 m' -> n >_0 n' -> m + n >_0 m' + n'.

  Proof.
    intros. destruct H. destruct H0.
    left. apply plus_gt_compat; hyp.
    destruct H0. rewrite H0. rewrite H1.
    do 2 rewrite A_plus_0_r. left. hyp.
    destruct H. rewrite H. rewrite H1.
    do 2 rewrite A_plus_0_l. hyp.
  Qed.

  Lemma gtx_mult_compat : forall m m' n n',
     m >_0 m' -> n >=_a n' -> m * n >_0 m' * n'.

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

  Notation dim_pos       := (dim_pos dim).
  Notation mat_times_vec := (@mat_vec_prod Arctic_as_OSR dim dim).
  Notation mint          := (@matrixInt _ dim).

  Lemma eval_some_notInf : forall n (mi : mint n) (v : vector (@dom _ _ _ _) n),
      Vexists (fun m => get_elem m dim_pos dim_pos <> MinusInf) (args mi) ->
      Vfold_left sr_add sr_0 (Vmap (fun v => Vnth v dim_pos)
      (Vmap2 mat_times_vec (args mi) (Vmap (@dom2vec _ _ _ _) v))) <> MinusInf.

  Proof.
    induction n; intros; simpl; destruct mi.
    VOtac. auto.
    simpl in H. VSntac args. rewrite H0 in H; simpl. destruct H.
    rewrite A_plus_comm. apply arctic_plus_notInf_left.
    apply mat_times_vec_at0_positive. hyp.
    VSntac v. simpl. destruct (Vhead v). 
    unfold vec_invariant, vec_at0 in x. simpl in *.
    apply ge_A1_not_minusInf. hyp.
    apply arctic_plus_notInf_left. 
    rewrite <- Vmap_tail.
    apply (IHn (Build_matrixInt const (Vtail args))). hyp.
  Qed.

  Lemma mi_eval_at0 : forall n (mi : matrixInt dim n) (v : vector (@dom _ _ _ _) n),
    somewhere_finite mi -> vec_at0 (mi_eval_aux mi (Vmap (@dom2vec _ _ _ _) v)) <> MinusInf.

  Proof.
    intros. unfold mi_eval_aux, vec_at0. 
    rewrite vector_plus_nth. destruct H.
    rewrite add_vectors_nth. apply arctic_plus_notInf_left.
    apply eval_some_notInf. hyp.
    rewrite Aplus_comm. apply arctic_plus_notInf_left. hyp.
  Qed.

  Lemma mi_eval_ok : forall f v,
    vec_invariant (mi_eval_aux (mi_trsInt f) (Vmap (@dom2vec _ _ _ _) v)).

  Proof.
    intros. unfold vec_invariant, vec_at0.
    apply not_minusInf_ge_A1.
    set (w := mi_eval_at0). unfold vec_at0 in w. apply w.
    apply mar_trsIntOk.
  Qed.

  Definition I                  := I mi_eval_ok.
  Definition succ               := succ.
  Definition succ'              := succ'. 
  Definition succ'_sub          := @succ'_sub _ _ _ _ gtx_plus_compat gtx_mult_compat
                                                                        mi_eval_ok.
  Definition succ'_dec          := succ'_dec.
  Definition succeq             := succeq.
  Definition succeq'            := succeq'.
  Definition succeq'_sub        := @succeq'_sub     Arctic_as_OSR _ _ _ mi_eval_ok.
  Definition succeq'_dec        := succeq'_dec.
  Definition refl_succeq        := refl_succeq.
  Definition monotone_succeq    := @monotone_succeq Arctic_as_OSR _ _ _ mi_eval_ok.
  Definition trans_succeq       := trans_succeq.
  Definition trans_succ         := trans_succ.
  Definition succ_succeq_compat := succ_succeq_compat ge_gt_eq.

  Lemma succ_wf : WF (@succ _ _ Arctic_as_OSR _).

  Proof.
    apply WF_incl with 
    (fun x y => @vec_at0 _ Arctic_as_OSR (dom2vec x) >_a
                @vec_at0 _ Arctic_as_OSR (dom2vec y)).
    intros x y xy.
    destruct (@Vforall2_elim_nth _ _ (@gtx Arctic_as_OSR) _
             (dom2vec x) (dom2vec y) _ dim_pos xy). 
    hyp.
    destruct H. destruct x.
    absurd (Vnth x dim_pos = sr_0).
    apply ge_A1_not_minusInf. hyp. hyp.
    fold (@Rof _  ArcticDom gt (fun v => vec_at0 (dom2vec v))).
    apply WF_inverse. apply gt_WF.
  Qed.

  (* Define an Instance of MonotoneAlgebraType for Arctic Nat *)

  Global Instance MonotoneAlgebra_ArcNat : MonotoneAlgebraType Sig.

  Proof.
    apply Build_MonotoneAlgebraType with
    (ma_int     := I)
    (ma_succ    := @succ    _ _ _ _)
    (ma_succeq  := @succeq  _ _ _ )
    (ma_succeq' := @succeq' _ _ _)
    (ma_succ'   := @term_gt _ _ _ _).
    apply refl_succeq.
    apply trans_succ.
    apply trans_succeq.
    apply monotone_succeq.
    apply succ_wf.
    apply succ_succeq_compat.
    apply term_gt_incl_succ.
    apply gtx_plus_compat.
    apply gtx_mult_compat.
    apply succeq'_sub.
    apply succ'_dec.
    apply succeq'_dec.
  Defined.
  
End S.