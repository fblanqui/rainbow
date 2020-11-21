(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-07-03

rule elimination with reduction pairs
*)

Set Implicit Arguments.

Require Import ATrs LogicUtil ARelation RelUtil SN ListUtil AMannaNess ACompat
  BoolUtil.

(***********************************************************************)
(** module type for reduction pairs *)

Section S.

  (* Remark: declare [Sig] as a Variable for [WP_Filter, WP_Perm, WP_Proj]. *)

  Variable Sig  : Signature.
  Notation term := (@term Sig).

  Class DS_WeakRedPair := mkDS_WeakRedPair {
    ds_weak_rp :> Weak_reduction_pair Sig;
    ds_wr_bsucc           : term -> term -> bool;
    ds_wr_bsucc_sub       : rel_of_bool ds_wr_bsucc << (wp_succ ds_weak_rp);
    ds_wr_refl_succeq     : reflexive (wp_succ_eq ds_weak_rp);
    ds_wr_bsucceq         : term -> term -> bool;
    ds_wr_bsucceq_sub     : rel_of_bool ds_wr_bsucceq << (wp_succ_eq ds_weak_rp);
    ds_wr_trans_succ      : transitive (wp_succ ds_weak_rp);
    ds_wr_trans_succeq    : transitive (wp_succ_eq ds_weak_rp)}.

End S.

(***********************************************************************)
(** properties of reduction pairs *)

Section WeakRedPairProps.

  Variable Sig: Signature.
  Context {WP : DS_WeakRedPair Sig}.
  
  Notation rule  := (rule Sig).
  Notation rules := (rules Sig).

  Lemma WF_wp_hd_red_mod : forall E R,
    forallb (brule (@ds_wr_bsucceq Sig WP)) E = true ->
    forallb (brule (@ds_wr_bsucceq Sig WP)) R = true ->
    WF (hd_red_mod E (filter (brule (neg (@ds_wr_bsucc Sig WP))) R)) ->
    WF (hd_red_mod E R).

  Proof.
    intros. set (Rge := filter (brule (neg (@ds_wr_bsucc Sig WP))) R).
    set (Rgt := removes (@eq_rule_dec Sig) Rge R).
    apply WF_incl with (hd_red_mod E (Rgt ++ Rge)).
    apply hd_red_mod_incl. refl. apply incl_removes_app.
    apply rule_elimination_hd_mod with (wp:=mkWeak_reduction_pair
      (@wp_subs Sig (@ds_weak_rp Sig WP)) (@wp_subs_eq Sig (@ds_weak_rp Sig WP))
      (@wp_cont_eq Sig (@ds_weak_rp Sig WP))
      (@wp_absorb Sig (@ds_weak_rp Sig WP)) (@wp_succ_wf Sig (@ds_weak_rp Sig WP))).
    (* E << succeq *)
    intros l r h. apply ds_wr_bsucceq_sub. rewrite forallb_forall in H.
    change (brule (@ds_wr_bsucceq Sig WP) (mkRule l r) = true). apply H. hyp.
    (* Rge << succeq *)
    apply incl_compat with R. unfold Rge. apply filter_incl.
    (* R << succeq *)
    intros l r h. apply ds_wr_bsucceq_sub. rewrite forallb_forall in H0.
    change (brule (@ds_wr_bsucceq Sig WP) (mkRule l r) = true). apply H0. hyp.
    (* Rgt << succ *)
    intros l r h. unfold Rgt in h. rewrite In_removes in h. destruct h.
    unfold Rge in H3. rewrite (notIn_filter _ (@eq_rule_dec Sig)) in H3.
    destruct H3. contr. destruct H3. clear H3.
    apply ds_wr_bsucc_sub. unfold rel. unfold brule, neg in H4. simpl in H4.
    rewrite negb_lr in H4. hyp.
    (* WF (hd_red_mod E Rge) *)
    hyp.
  Qed.

  Variable cc_succ : context_closed (@wp_succ Sig (@ds_weak_rp Sig WP)).

  Lemma WF_rp_red_mod : forall E R,
    forallb (brule (@ds_wr_bsucceq Sig WP)) E = true ->
    forallb (brule (@ds_wr_bsucceq Sig WP)) R = true ->
    WF (red_mod (filter (brule (neg (@ds_wr_bsucc Sig WP))) E)
                (filter (brule (neg (@ds_wr_bsucc Sig WP))) R))
    -> WF (red_mod E R).

  Proof.
    intros. set (Rge := filter (brule (neg (@ds_wr_bsucc Sig WP))) R).
    set (Ege := filter (brule (neg (@ds_wr_bsucc Sig WP))) E).
    set (Rgt := removes (@eq_rule_dec Sig) Rge R).
    set (Egt := removes (@eq_rule_dec Sig) Ege E).
    apply WF_incl with (red_mod (Egt ++ Ege) (Rgt ++ Rge)).
    apply red_mod_incl; apply incl_removes_app.
    apply rule_elimination_mod with (rp:=mkReduction_pair
      (@wp_subs Sig (@ds_weak_rp Sig WP)) (@wp_subs_eq Sig (@ds_weak_rp Sig WP))
      cc_succ (@wp_cont_eq Sig (@ds_weak_rp Sig WP))
      (@wp_absorb Sig (@ds_weak_rp Sig WP)) (@wp_succ_wf Sig (@ds_weak_rp Sig WP))).
    (* Rgt << succ *)
    intros l r h. unfold Rgt in h. rewrite In_removes in h. destruct h.
    unfold Rge in H3. rewrite (notIn_filter _ (@eq_rule_dec Sig)) in H3.
    destruct H3. contr. destruct H3. clear H3.
    apply ds_wr_bsucc_sub. unfold rel. unfold brule, neg in H4. simpl in H4.
    rewrite negb_lr in H4. hyp.
    (* Rge << succeq *)
    apply incl_compat with R. unfold Rge. apply filter_incl.
    (* R << succeq *)
    intros l r h. apply ds_wr_bsucceq_sub. rewrite forallb_forall in H0.
    change (brule (@ds_wr_bsucceq Sig WP) (mkRule l r) = true). apply H0. hyp.
    (* Egt << succ *)
    intros l r h. unfold Egt in h. rewrite In_removes in h. destruct h.
    unfold Ege in H3. rewrite (notIn_filter _ (@eq_rule_dec Sig)) in H3.
    destruct H3. contr. destruct H3. clear H3.
    apply ds_wr_bsucc_sub. unfold rel. unfold brule, neg in H4. simpl in H4.
    rewrite negb_lr in H4. hyp.
    (* Ege << succeq *)
    apply incl_compat with E. unfold Ege. apply filter_incl.
    (* E << succeq *)
    intros l r h. apply ds_wr_bsucceq_sub. rewrite forallb_forall in H.
    change (brule (@ds_wr_bsucceq Sig WP) (mkRule l r) = true). apply H. hyp.
    (* WF (hd_red_mod Ege Rge) *)
    hyp.
  Qed.

  Lemma WF_rp_red : forall R,
    forallb (brule (@ds_wr_bsucceq Sig WP)) R = true ->
    WF (red (filter (brule (neg (@ds_wr_bsucc Sig WP))) R)) ->
    WF (red R).

  Proof.
    intros. rewrite <- red_mod_empty. apply WF_rp_red_mod. refl. hyp.
    simpl. rewrite red_mod_empty. hyp.
  Qed.

(***********************************************************************)
(** tactics for Rainbow *)

  Ltac do_prove_termination prove_cc_succ lemma :=
    apply lemma;
      match goal with
      | |- context_closed _ => prove_cc_succ
      | |- WF _ => idtac
      | |- _ = _ => check_eq || fail 10 "some rule is not in the ordering"
      end.

  Ltac prove_termination prove_cc_succ :=
    let prove := do_prove_termination prove_cc_succ in
    match goal with
    | |- WF (red _) => prove WF_rp_red
    | |- WF (red_mod _ _) => prove WF_rp_red_mod
    | |- WF (hd_red_mod _ _) => prove WF_wp_hd_red_mod
    | |- WF (hd_red_Mod _ _) =>
      try rewrite int_red_incl_red;
        rewrite hd_red_mod_of_hd_red_Mod;
          prove_termination prove_cc_succ
   end.

End WeakRedPairProps.

(***********************************************************************)
(** reduction pair associated to a monotone algebra *)

Require Import AMonAlg2.

Section WP_MonAlg.

  Variable Sig: Signature.

  Context {MA: MonotoneAlgebraType Sig}.

  Notation I := (ma_int Sig).

  Definition succ    := IR I (ma_succ Sig).
  Definition wf_succ := IR_WF I (ma_succ_wf Sig).
  Definition sc_succ := @IR_substitution_closed _ _ (ma_succ Sig).
  Definition bsucc   := bool_of_rel (ma_succ'_dec Sig).

  Lemma bsucc_sub : rel_of_bool bsucc << succ.

  Proof.
    intros t u. unfold rel_of_bool, bsucc, bool_of_rel.
    case (ma_succ'_dec Sig t u); intros. apply ma_succ'_sub. hyp. discr.
  Qed.

  Definition succeq      := IR I (ma_succeq Sig).
  Definition sc_succeq   := @IR_substitution_closed _ _ (ma_succeq Sig).
  Definition cc_succeq   := @IR_context_closed _ _ _ (ma_monotone_succeq Sig).
  Definition refl_succeq := @IR_reflexive _ _ _ (ma_refl_succeq Sig).

  Lemma succ_succeq_compat : absorbs_left succ succeq.

  Proof.
    intros x z xz val. apply ma_succ_succeq_compat.
    destruct xz as [y [ge_xy gt_yz]]. exists (term_int val y). split; auto.
  Qed.

  Definition bsucceq := bool_of_rel (ma_succeq'_dec Sig).

  Lemma bsucceq_sub : rel_of_bool bsucceq << succeq.

  Proof.
    intros t u. unfold rel_of_bool, bsucceq, bool_of_rel.
    case (ma_succeq'_dec Sig t u); intros. apply ma_succeq'_sub. hyp. discr.
  Qed.

  Definition trans_succ   := IR_transitive (ma_trans_succ Sig).
  Definition trans_succeq := IR_transitive (ma_trans_succeq Sig).

  Definition impl_weak_rp := @mkWeak_reduction_pair Sig succ succeq
  sc_succ sc_succeq cc_succeq succ_succeq_compat wf_succ.

  Global Instance WP_MonAlg : DS_WeakRedPair Sig.
  Proof.
    apply mkDS_WeakRedPair with
    (ds_weak_rp  := impl_weak_rp)
    (ds_wr_bsucc := bsucc)
    (ds_wr_bsucceq := bsucceq).
    apply bsucc_sub.
    apply refl_succeq.
    apply bsucceq_sub.
    apply trans_succ.
    apply trans_succeq.
  Defined.

End WP_MonAlg.

(***********************************************************************)
(** reduction pair associated to a permutative non-collapsing
arguments filtering *)


Section AFilter.

  Require Import AFilterPerm.

  Variable Sig: Signature.

  Class Perm := {
    perm_pi    : forall f: Sig, nat_lts (arity f) }.

End AFilter.
  
(*FIXME: define meta-theorems?*)

Section WP_Perm. 

  Variable Sig: Signature.
  Context {P  : Perm Sig}.

  Definition perm_Sig := filter_sig (@perm_pi Sig P).

  Context {WR: DS_WeakRedPair perm_Sig}.

  Definition psucc      := filter_ord         (@wp_succ    perm_Sig (@ds_weak_rp perm_Sig WR)).
  Definition pwf_succ   := WF_filter          (@wp_succ_wf perm_Sig (@ds_weak_rp perm_Sig WR)).
  Definition psc_succ   := filter_subs_closed (@wp_subs perm_Sig (@ds_weak_rp perm_Sig WR)).
  Definition pbsucc t u := (@ds_wr_bsucc perm_Sig WR) (filter (@perm_pi Sig P) t)
                                                   (filter (@perm_pi Sig P) u).

  Lemma pbsucc_sub: rel_of_bool pbsucc << psucc.
  
  Proof.
    intros t u h. apply ds_wr_bsucc_sub. hyp.
  Qed.

  Definition psucceq    := filter_ord         (@wp_succ_eq    perm_Sig (@ds_weak_rp perm_Sig WR)).
  Definition psc_succeq := filter_subs_closed (@wp_subs_eq perm_Sig (@ds_weak_rp perm_Sig WR)).

  Parameter perm_pi_ok : non_dup (@perm_pi Sig P).

  Definition pcc_succeq := filter_weak_cont_closed (perm_pi_ok)
                                                   (@ds_wr_refl_succeq perm_Sig WR)
                                                   (@wp_cont_eq  perm_Sig (@ds_weak_rp perm_Sig WR)).
  
  Lemma prefl_succeq : reflexive psucceq.

  Proof.
    intro x. unfold psucceq. apply ds_wr_refl_succeq.
  Qed.

  Lemma psucc_succeq_compat : absorbs_left psucc psucceq.

  Proof.
    unfold absorbs_left, psucc, psucceq. intros t v [u [h1 h2]].
    unfold filter_ord in *. apply wp_absorb.
    exists (filter (@perm_pi _ _) u).
    auto.
  Qed.

  Definition pbsucceq t u := (@ds_wr_bsucceq perm_Sig WR)(filter (@perm_pi _ P) t)
                                                      (filter (@perm_pi _ P) u).

  Lemma pbsucceq_sub : rel_of_bool pbsucceq << psucceq.

  Proof.
    intros t u h. apply ds_wr_bsucceq_sub. hyp.
  Qed.

  Lemma ptrans_succ : transitive psucc.

  Proof.
    apply filter_trans. apply ds_wr_trans_succ.
  Qed.

  Lemma ptrans_succeq : transitive psucceq.

  Proof.
    apply filter_trans. apply ds_wr_trans_succeq.
  Qed.

  (* Define an instance of WeakRedPair *)

  Definition impl_weak_rp_perm := @mkWeak_reduction_pair Sig psucc psucceq
    psc_succ psc_succeq pcc_succeq psucc_succeq_compat pwf_succ.

  Global Instance WP_Perm : DS_WeakRedPair Sig.
  Proof.
    apply mkDS_WeakRedPair with
    (ds_weak_rp  := impl_weak_rp_perm)
    (ds_wr_bsucc := pbsucc)
    (ds_wr_bsucceq := pbsucceq).
    apply pbsucc_sub.
    apply prefl_succeq.
    apply pbsucceq_sub.
    apply ptrans_succ.
    apply ptrans_succeq.
  Defined.

End WP_Perm.

(***********************************************************************)
(** reduction pair associated to collapsing arguments filtering *)

Section AProj.

  Require Import AProj.

  Variable Sig: Signature.

  Class Proj := {
    pr_pi : forall f: Sig, option {k | k < arity f} }.

End AProj.

(*FIXME: define a meta-theorem?*)

Section WP_Proj.

  Variable Sig: Signature.

  Context {P : Proj Sig}.
  Context {WR: DS_WeakRedPair Sig}.

  Definition pr_succ      := proj_ord         (@pr_pi _ _) (@wp_succ Sig (@ds_weak_rp Sig WR)).
  Definition pr_wf_succ   := WF_proj          (@pr_pi _ _) (@wp_succ_wf Sig (@ds_weak_rp Sig WR)).
  Definition pr_sc_succ   := proj_subs_closed (@pr_pi _ _) (@wp_subs Sig (@ds_weak_rp Sig WR)).
  Definition pr_bsucc t u := ds_wr_bsucc (proj   (@pr_pi _ _) t)
                                      (proj   (@pr_pi _ _) u).

  Lemma pr_bsucc_sub : rel_of_bool pr_bsucc << pr_succ.

  Proof. intros t u h. apply ds_wr_bsucc_sub. hyp. Qed.

  Definition pr_succeq    := proj_ord          (@pr_pi _ _)
                             (@wp_succ_eq    Sig (@ds_weak_rp Sig WR)).
  Definition pr_sc_succeq := proj_subs_closed (@pr_pi _ _)
                             (@wp_subs_eq     Sig (@ds_weak_rp Sig WR)).
  Definition pr_cc_succeq := proj_cont_closed (@pr_pi _ _)
                             (@ds_wr_refl_succeq Sig WR)
                             (@wp_cont_eq     Sig (@ds_weak_rp Sig WR)).
  
  Lemma pr_refl_succeq : reflexive pr_succeq.

  Proof.
    intro x. unfold pr_succeq. apply ds_wr_refl_succeq.
  Qed.

  Lemma pr_succ_succeq_compat : absorbs_left pr_succ pr_succeq.

  Proof.
    unfold absorbs_left, pr_succ, pr_succeq.
    intros t v [u [h1 h2]].
    unfold proj_ord in *.
    apply wp_absorb.
    exists (proj (@pr_pi _ _) u).
    auto.
  Qed.

  Definition pr_bsucceq t u := ds_wr_bsucceq (proj (@pr_pi _ _) t)
                                          (proj (@pr_pi _ _) u).

  Lemma pr_bsucceq_sub : rel_of_bool pr_bsucceq << pr_succeq.

  Proof.
    intros t u h. apply ds_wr_bsucceq_sub. hyp.
  Qed.

  Lemma pr_trans_succ : transitive pr_succ.

  Proof.
    apply proj_trans. apply ds_wr_trans_succ.
  Qed.

  Lemma pr_trans_succeq : transitive pr_succeq.

  Proof.
    apply proj_trans. apply ds_wr_trans_succeq.
  Qed.

  (* Define an Instance for WeakRedPair. *)

 Definition impl_weak_rp_proj := @mkWeak_reduction_pair Sig pr_succ pr_succeq
    pr_sc_succ pr_sc_succeq pr_cc_succeq pr_succ_succeq_compat pr_wf_succ.

  Global Instance WP_Proj : DS_WeakRedPair Sig.
  
  Proof.
    apply mkDS_WeakRedPair with
    (ds_weak_rp  := impl_weak_rp_proj)
    (ds_wr_bsucc := pr_bsucc)
    (ds_wr_bsucceq := pr_bsucceq).
    apply pr_bsucc_sub.
    apply pr_refl_succeq.
    apply pr_bsucceq_sub.
    apply pr_trans_succ.
    apply pr_trans_succeq.
  Defined.

End WP_Proj.

(***********************************************************************)
(** reduction pair associated to a non-permutative non-collapsing
arguments filtering *)

Require Import AFilterBool VecUtil VecBool.

Section F.

  Variable Sig: Signature.

  Class Filter := {
    b_pi : forall f: Sig, bools (arity f)}.

End F.

Section WP_Filter.
  
  Variable Sig: Signature.
  Context {F  : Filter Sig}.

  Definition FSig := filter_sig (@b_pi _ _).

  Context {WR: DS_WeakRedPair FSig}.

  Definition fb_succ      := filter_ord         (@wp_succ    FSig (@ds_weak_rp FSig WR)).
  Definition fb_wf_succ   := WF_filter          (@wp_succ_wf FSig (@ds_weak_rp FSig WR)).
  Definition fb_sc_succ   := filter_subs_closed (@wp_subs FSig (@ds_weak_rp FSig WR)).
  Definition fb_bsucc t u := (@ds_wr_bsucc FSig WR) (filter (@b_pi _ _) t)
                                                 (filter (@b_pi _ _) u).

  Lemma fb_bsucc_sub : rel_of_bool fb_bsucc << fb_succ.

  Proof. intros t u h. apply ds_wr_bsucc_sub. hyp. Qed.

  Definition fb_succeq    := filter_ord         (@wp_succ_eq     FSig (@ds_weak_rp FSig WR)).
  Definition fb_sc_succeq := filter_subs_closed (@wp_subs_eq     FSig (@ds_weak_rp FSig WR)).
  Definition fb_cc_succeq := filter_cont_closed (@ds_wr_refl_succeq FSig WR)
                                                (@wp_cont_eq     FSig (@ds_weak_rp FSig WR)).
  
  Lemma fb_refl_succeq : reflexive fb_succeq.

  Proof.
    intro x. unfold succeq. apply ds_wr_refl_succeq.
  Qed.

  Lemma fb_succ_succeq_compat : absorbs_left fb_succ fb_succeq.

  Proof.
    unfold absorbs_left, fb_succ, fb_succeq.
    intros t v [u [h1 h2]].
    unfold filter_ord in *. apply wp_absorb.
    exists (filter (@b_pi _ _) u).
    auto.
  Qed.

  Definition fb_bsucceq t u := (@ds_wr_bsucceq FSig WR)(filter (@b_pi _ _) t)
                                                    (filter (@b_pi _ _) u).

  Lemma fb_bsucceq_sub : rel_of_bool fb_bsucceq << fb_succeq.

  Proof.
    intros t u h. apply ds_wr_bsucceq_sub. hyp.
  Qed.

  Lemma fb_trans_succ : transitive fb_succ.

  Proof.
    apply filter_trans. apply ds_wr_trans_succ.
  Qed.

  Lemma fb_trans_succeq : transitive fb_succeq.

  Proof.
    apply filter_trans. apply ds_wr_trans_succeq.
  Qed.

  (* Define an Instance for WeakRedPair. *)

  Definition impl_weak_rp_fb := @mkWeak_reduction_pair Sig fb_succ fb_succeq
    fb_sc_succ fb_sc_succeq fb_cc_succeq fb_succ_succeq_compat fb_wf_succ.

  Global Instance WP_Filter : DS_WeakRedPair Sig.
  
  Proof.
    apply mkDS_WeakRedPair with
    (ds_weak_rp  := impl_weak_rp_fb)
    (ds_wr_bsucc := fb_bsucc)
    (ds_wr_bsucceq := fb_bsucceq).
    apply fb_bsucc_sub.
    apply fb_refl_succeq.
    apply fb_bsucceq_sub.
    apply fb_trans_succ.
    apply fb_trans_succeq.
  Defined.

End WP_Filter.
