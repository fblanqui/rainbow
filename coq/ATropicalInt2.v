(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Johannes Waldmann, 2010-04
*)

Set Implicit Arguments.

Require Import Matrix2 OrdSemiRing2 VecUtil
  AMonAlg2 SN RelUtil NatUtil AWFMInterpretation LogicUtil
  AMatrixBasedInt2 Bool Structures.Equalities Tropical_as_OSR SemiRing
  VecArith2 ATropicalBasedInt2.

(***********************************************************************)
(** Condition for a tropical interpretation to be valid *)

Section Somewhere_tfinite.

  Variable Sig : Signature.
  Variable dim : nat.

  Context {MI: TMatrixInt (OSR:=Tropical_as_OSR) Sig dim}.

  Notation dim_pos := (dim_pos dim).
  
  Definition somewhere_tfinite n (fi : matrixInt dim n) := 
    Vexists (fun m => get_elem m dim_pos dim_pos <> PlusInf) (args fi)
    \/ Vnth (const fi) dim_pos <> PlusInf.

  Definition bsomewhere_tfinite n (fi : matrixInt dim n) :=
    bVexists
    (fun m => tropical_is_finite (get_elem m dim_pos dim_pos)) (args fi)
    || tropical_is_finite (Vnth (const fi) dim_pos).

  Require Import BoolUtil.

  Lemma bsomewhere_tfinite_ok : forall n (fi : matrixInt dim n),
    bsomewhere_tfinite fi = true <-> somewhere_tfinite fi.

  Proof.
    intros. unfold bsomewhere_tfinite, somewhere_tfinite.
    rewrite orb_eq. rewrite tropical_is_finite_ok.
    rewrite bVexists_ok. refl. intro. apply tropical_is_finite_ok.
  Qed.

End Somewhere_tfinite.

(***********************************************************************)
(** Module type for proving termination with a tropical interpretation *)

Section S.

  Variable Sig: Signature.
  Variable dim: nat.

  Class TTropicalInt := {
    trop_int      :> TMatrixInt Sig dim;
    trop_trsIntOk : forall f : Sig, somewhere_tfinite (mi_trsInt f) }.

  Context {TI : TTropicalInt}.
  
  Lemma mat_times_vec_at0_positive : forall n (m : matrix n n) 
   (v : vector s_typ n) (dim_pos : n > 0),
   get_elem m dim_pos dim_pos <> PlusInf ->   
   Vnth v dim_pos <> PlusInf -> Vnth (mat_vec_prod m v) dim_pos <> PlusInf.
  
  Proof.
    destruct n; intros. absurd_arith.
    VSntac v. unfold matrix in m. VSntac m. 
    unfold mat_vec_prod, col_mat_to_vec, get_col. rewrite Vnth_map. 
    set (w := mat_mult_spec). unfold get_elem, get_row in w. rewrite w.
    simpl. VSntac (Vhead m). unfold dot_product.
    simpl. rewrite A_plus_comm. apply tropical_plus_notInf_left.
    apply tropical_mult_notInf. 
    rewrite H2 in H. unfold get_elem in H. simpl in H.
    rewrite Vhead_nth. erewrite <-Vnth_eq. apply H. auto.
    rewrite H1 in H0. hyp.
  Qed.

  Notation "x >_0 y" := (@gtx _ x y) (at level 70).

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
    m >_0 m' -> n >=_t n' -> m * n >_0 m' * n'.

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

  (* FIXME: Declare a [Variable A0_gt_A1] because in file
  [ATropicalBasedInt.v] in CoLoR decalare this variable. *)

  Import OSR_Notations.

  Variable A0_gt_A1 : sr_0 >> sr_1.
  Notation dim_pos  := (dim_pos dim).

  Lemma eval_some_notInf : forall n (mi : @matrixInt _ dim n)
    (v : vector (@dom Tropical_as_OSR _ dim (@Conf _ _ dim _ A0_gt_A1)) n),
    Vexists (fun m => get_elem m dim_pos dim_pos <> sr_0) (args mi) ->
    Vfold_left sr_add sr_0 (Vmap (fun v => Vnth v dim_pos)(Vmap2 (@mat_vec_prod _ _ _) (args mi)
                           (Vmap (@dom2vec _ _ _ _) v))) <> PlusInf.

  Proof.
    induction n; intros; simpl; destruct mi.
    VOtac. auto.
    simpl in H. VSntac args. rewrite H0 in H; simpl. destruct H.
    rewrite A_plus_comm. apply tropical_plus_notInf_left.
    apply mat_times_vec_at0_positive. hyp.
    VSntac v. simpl. destruct (Vhead v). 
    unfold vec_invariant in m. simpl in *.
    (* TODO... change - specific to tropical... *)
    intuition. unfold ge, vec_at0,gt in m. clear H1. 
    simpl in *. rewrite H2 in m. contr.
    apply tropical_plus_notInf_left. 
    rewrite <- Vmap_tail.
    apply (IHn (Build_matrixInt const (Vtail args))). hyp.
  Qed.

  Lemma mi_eval_at0 : forall n (mi : matrixInt dim n)
    (v : vector (@dom Tropical_as_OSR _ dim (@Conf _ _ dim _ A0_gt_A1)) n),
    somewhere_tfinite mi -> vec_at0 (mi_eval_aux mi (Vmap (@dom2vec _ _ _ _) v)) <> PlusInf.

  Proof.
    intros. unfold mi_eval_aux, vec_at0. 
    rewrite vector_plus_nth. destruct H.
    rewrite add_vectors_nth. apply tropical_plus_notInf_left.
    apply eval_some_notInf. hyp.
    rewrite A_plus_comm. apply tropical_plus_notInf_left. hyp.
  Qed.

  Lemma mi_eval_ok : forall f v, vec_invariant (mi_eval_aux (mi_trsInt f)
    (Vmap (@dom2vec _ _ dim (@Conf _ _ dim _ A0_gt_A1)) v)).

  Proof.
    intros. unfold vec_invariant, vec_at0.
    apply tropical_plus_inf_max.
    set (w := mi_eval_at0). unfold vec_at0 in w. apply w.
    apply trop_trsIntOk.
  Qed.

  Definition I                  := I mi_eval_ok.
  Definition succ               := succ.
  Definition succ'              := succ'.
  Definition succ'_sub          := @succ'_sub _ Tropical_as_OSR _ _ _
                                   gtx_plus_compat gtx_mult_compat mi_eval_ok.
  Definition succ'_dec          := succ'_dec.
  Definition succeq             := (@succeq Tropical_as_OSR).
  Definition succeq'            := (@succeq' Tropical_as_OSR).
  Definition succeq'_sub        := @succeq'_sub Tropical_as_OSR _ _ _ mi_eval_ok.
  Definition succeq'_dec        := (@succeq'_dec Tropical_as_OSR).
  Definition refl_succeq        := (@refl_succeq Tropical_as_OSR).
  Definition monotone_succeq    := @monotone_succeq Tropical_as_OSR _ _ _ mi_eval_ok.
  Definition trans_succeq       := (@trans_succeq Tropical_as_OSR).
  Definition succ_succeq_compat := @succ_succeq_compat _ Tropical_as_OSR _ _ A0_gt_A1 ge_gt_eq.

  Lemma succ_wf : WF (@succ _ _ _ _ A0_gt_A1) .

  Proof.
    apply WF_incl with 
    (fun x y => vec_at0 (dom2vec x) >> vec_at0 (dom2vec y)).
    intros x y xy.
    destruct (@Vforall2_elim_nth _ _ gtx _
      (@dom2vec _ _ _ _ x) (dom2vec y) _ dim_pos xy). 
    hyp.
    destruct H. destruct x.
    (* TODO: change, specific for tropical *)
    absurd (0 = Vnth x dim_pos).
    unfold vec_invariant in m. simpl in *. 
    intuition. unfold ge, vec_at0, gt in m. clear xy. 
    simpl in *. symmetry in H1. rewrite H1 in m. contr.
    intuition.
    fold (@Rof(@dom Tropical_as_OSR _ _ (Conf A0_gt_A1))
     TropicalDom gt (fun v => vec_at0 ((@dom2vec Tropical_as_OSR _ _) _ v))).
    apply WF_inverse. apply gt_WF.
  Qed.
    
  Instance trans_succ : Transitive (@succ _ _ _ _ A0_gt_A1).

  Proof.
    change (transitive (Rof succ_vec (@dom2vec Tropical_as_OSR _ _ (Conf A0_gt_A1)))).
    apply Rof_trans.
    apply Vforall2_trans. class.
  Qed.

  Global Instance MonotoneAlgebra_Trop : MonotoneAlgebraType Sig.

  Proof.
    apply Build_MonotoneAlgebraType with
    (ma_int     := I)
    (ma_succ    := @succ _ _ _ _ _)
    (ma_succeq  := @succeq _ _ _)
    (ma_succeq' := @succeq' _ dim (@Conf _ _ dim _ A0_gt_A1))
    (ma_succ'   := @term_gt _ _ _ _ A0_gt_A1).
    apply refl_succeq.
    apply succ_trans.
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