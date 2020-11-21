(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski and Johannes Waldmann, 2008-01
*)

Set Implicit Arguments.

Require Import Matrix2 AMonAlg2 VecUtil OrdSemiRing2
  SN RelUtil ZArith AMatrixBasedInt2 LogicUtil ArcticBZ_as_OSR
  SemiRing VecArith2 AArcticBasedInt2.

(***********************************************************************)
(** Condition for an arctic BZ interpretation to be valid *)

Section Absolute_finite.

  Variable Sig: Signature.
  Variable dim: nat.

  Context {MI: TMatrixInt (OSR:=ArcticBZ_as_OSR) Sig dim}.

  Notation dim_pos := (dim_pos dim).

  Definition absolute_finite  n (fi : matrixInt dim n) := 
    Vnth (const fi) dim_pos >=_b A1.

  Definition babsolute_finite n (fi : matrixInt dim n) :=
    is_above_zero (Vnth (const fi) dim_pos).

  Lemma babsolute_finite_ok : forall n (fi : matrixInt dim n),
    babsolute_finite fi = true <-> absolute_finite fi.

  Proof.
    intros. unfold babsolute_finite, absolute_finite.
    rewrite is_above_zero_ok. tauto.
  Qed.

End Absolute_finite.

(***********************************************************************)
(** Module type for proving termination with matrix interpretations *)

Section S.

  Variable Sig: Signature.
  Variable dim: nat.

  Context {MI: TMatrixInt (OSR:=ArcticBZ_as_OSR) Sig dim}.

  Parameter mb_trsIntOk: forall f: Sig, absolute_finite (mi_trsInt f).

  Notation dim_pos := (@dim_pos   dim).
  Notation dom     := (@dom _ Sig dim _).
  Notation dom2vec := (@dom2vec _ _ _ _).

  Lemma mi_eval_at0 : forall n (mi : matrixInt dim n) (v : vector dom n),
   absolute_finite mi -> vec_at0 (mi_eval_aux mi (Vmap dom2vec v)) >=_b A1.

  Proof.
    intros. unfold mi_eval_aux, vec_at0.
    rewrite vector_plus_nth. rewrite A_plus_comm.
    apply arctic_plus_ge_monotone. exact H.
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
    m >_0 m' -> n >=_b n' -> m * n >_0 m' * n'.

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
    vec_invariant (mi_eval_aux (mi_trsInt f) (Vmap dom2vec v)).

  Proof.
    intros. unfold vec_invariant, vec_at0. 
    set (w := mi_eval_at0). unfold vec_at0 in w. apply w.
    apply mb_trsIntOk.
  Qed.
  
  Definition I                  := I mi_eval_ok.
  Definition succ               := succ.
  Definition succ'              := succ'.
  Definition succ'_sub          := @succ'_sub _ _ _ _ gtx_plus_compat gtx_mult_compat mi_eval_ok.
  Definition succ'_dec          := succ'_dec.
  Definition succeq             := succeq.
  Definition succeq'            := succeq'.
  Definition succeq'_sub        := @succeq'_sub     ArcticBZ_as_OSR _ _ _             mi_eval_ok.
  Definition succeq'_dec        := succeq'_dec.
  Definition refl_succeq        := refl_succeq.
  Definition monotone_succeq    := @monotone_succeq ArcticBZ_as_OSR _ _ _             mi_eval_ok.
  Definition trans_succeq       := trans_succeq.
  Definition trans_succ         := trans_succ.
  Definition succ_succeq_compat := succ_succeq_compat ge_gt_eq.

  Open Scope Z_scope.

  (* REMARK: Need to put %nat at the second [)]. *)
  Lemma succ_wf : WF (@succ _ _ ArcticBZ_as_OSR _).
    
  Proof.
    apply wf_transp_WF.
    unfold succ, transp.
    apply well_founded_lt_compat with (f := 
        (fun d: dom => 
          match vec_at0 (dom2vec d) with
          | Fin x => Zabs_nat x
          | MinusInfBZ => 0%nat
          end
        )%nat).
    intros x y xy. destruct x. destruct y. simpl in *. 
    cut (ge (vec_at0 x) A1). 2: hyp.
    cut (ge (vec_at0 x0) A1). 2: hyp.
    cut (gtx (vec_at0 x0) (vec_at0 x)).
    gen (vec_at0 x0). gen (vec_at0 x).
    clear x x0 m m0 xy. intros x y xy x_lb y_lb.
    destruct x; destruct y; arctic_ord.
    (*FIXME: this should be solved by arctic_ord *)
    unfold A1 in *.
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
    unfold vec_at0. apply Vforall2_elim_nth. hyp.
  Qed.

    (* Define an Instance of MonotoneAlgebraType for Arctic Int. *)

  Global Instance MonotoneAlgebra_ArcInt : MonotoneAlgebraType Sig.
  
  Proof.
    apply Build_MonotoneAlgebraType with
    (ma_int     := I)
    (ma_succ    := @succ _ _ _ _)
    (ma_succeq  := @succeq _ _ _ )
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

    (***********************************************************************)
    (** tactics *)
    
    Ltac prove_cc_succ Fs_ok :=
      fail 10 "arctic matrices cannot be used for proving total termination".
    
End S.