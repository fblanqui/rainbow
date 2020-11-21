(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-07-03

* Rule elimination with reduction pairs.
*)

Set Implicit Arguments.

Require Import ATrs LogicUtil ARelation RelUtil SN ListUtil AMannaNess 
  ACompat BoolUtil.

Section S.

  Section WeakRedPair.

  Variable Sig : Signature.

  Notation term := (@term Sig).

  (***********************************************************************)
  (** ** Weak reduction pair. *)

  (* TEST: this record will be use in the AMonAlg. *)

  Record bWeakRedPair : Type := mkbWeakRedPair {
    succ : relation term;
    wf_succ : WF succ;
    sc_succ : substitution_closed succ;

    bsucc : term -> term -> bool;
    bsucc_sub : rel_of_bool bsucc << succ;
    
    succeq : relation term;
    sc_succeq : substitution_closed succeq;
    cc_succeq : context_closed succeq;
    refl_succeq : reflexive succeq;

    succ_succeq_compat : absorbs_left succ succeq;
    
    bsucceq : term -> term -> bool;
    bsucceq_sub : rel_of_bool bsucceq << succeq;
    
    trans_succ : transitive succ;
    trans_succeq : transitive succeq
  }.

  (* TEST: define a new record bweakredpair, where assume [>] is
   closed by context.  this will be use in the argument filtering
   below. *)

  Record bWeakRedPair2 : Type := mkbWeakRedPair2 {
    succ2 : relation term;
    wf_succ2 : WF succ2;
    sc_succ2 : substitution_closed succ2;

    bsucc2 : term -> term -> bool;
    bsucc_sub2 : rel_of_bool bsucc2 << succ2;
    
    succeq2 : relation term;
    sc_succeq2 : substitution_closed succeq2;
    cc_succeq2 : context_closed succeq2;
    refl_succeq2 : reflexive succeq2;
    cc_succ2 : context_closed succ2; (* FIXME: add [>] is close by context. *)
    refl_succ2 : reflexive succ2; (* FIXME: add [>] is reflexivity. *)

    succ_succeq_compat2 : absorbs_left succ2 succeq2;
    
    bsucceq2 : term -> term -> bool;
    bsucceq_sub2 : rel_of_bool bsucceq2 << succeq2;
    
    trans_succ2 : transitive succ2;
    trans_succeq2 : transitive succeq2
  }.

End WeakRedPair.

  (***********************************************************************)
  (** ** Properties of reduction pairs. *)

  Section WeakRedPairProps.
    
    Variable Sig: Signature.

    Variable bwp : bWeakRedPair Sig. 

    Lemma WF_wp_hd_red_mod : forall E R,
      forallb (brule (bsucceq bwp)) E = true ->
      forallb (brule (bsucceq bwp)) R = true ->
      WF (hd_red_mod E (filter (brule (neg (bsucc bwp))) R)) ->
      WF (hd_red_mod E R).

    Proof.
      intros. set (Rge := filter (brule (neg (bsucc bwp))) R).
      set (Rgt := removes (@eq_rule_dec Sig) Rge R).
      apply WF_incl with (hd_red_mod E (Rgt ++ Rge)).
      apply hd_red_mod_incl. refl. apply incl_removes_app.
      apply rule_elimination_hd_mod with (wp := mkWeak_reduction_pair
        (sc_succ bwp) (sc_succeq bwp) (cc_succeq bwp) (succ_succeq_compat bwp)
        (wf_succ bwp)).
      (* E << succeq *)
      intros l r h. apply (bsucceq_sub bwp). rewrite forallb_forall in H.
      change (brule (bsucceq bwp) (mkRule l r) = true). apply H. hyp.
      (* Rge << succeq *)
      apply incl_compat with R. unfold Rge. apply filter_incl.
      (* R << succeq *)
      intros l r h. apply (bsucceq_sub bwp). rewrite forallb_forall in H0.
      change (brule (bsucceq bwp) (mkRule l r) = true). apply H0. hyp.
      (* Rgt << succ *)
      intros l r h. unfold Rgt in h. rewrite In_removes in h. destruct h.
      unfold Rge in H3. rewrite (notIn_filter _ (@eq_rule_dec Sig)) in H3.
      destruct H3. contradiction. destruct H3. clear H3.
      apply (bsucc_sub bwp). unfold rel. unfold brule, neg in H4. simpl in H4.
      rewrite negb_lr in H4. hyp.
      (* WF (hd_red_mod E Rge) *)
      hyp.
    Qed.

    (* FIXME: move cc_scc inside the Record of bwp. *)

    Variable cc_succ : context_closed (succ bwp).

    Lemma WF_rp_red_mod : forall E R,
      forallb (brule (bsucceq bwp)) E = true ->
      forallb (brule (bsucceq bwp)) R = true ->
      WF (red_mod (filter (brule (neg (bsucc bwp))) E)
                  (filter (brule (neg (bsucc bwp))) R)) ->
      WF (red_mod E R).

    Proof.
      intros. set (Rge := filter (brule (neg (bsucc bwp))) R).
      set (Ege := filter (brule (neg (bsucc bwp))) E).
      set (Rgt := removes (@eq_rule_dec Sig) Rge R).
      set (Egt := removes (@eq_rule_dec Sig) Ege E).
      apply WF_incl with (red_mod (Egt ++ Ege) (Rgt ++ Rge)).
      apply red_mod_incl;  apply incl_removes_app.
      eapply rule_elimination_mod with (rp := mkReduction_pair
        (sc_succ bwp) (sc_succeq bwp) cc_succ (cc_succeq bwp) (* FIXME: cc_succ *)
        (succ_succeq_compat bwp) (wf_succ bwp)).
      (* Rgt << succ *)
      intros l r h. unfold Rgt in h. rewrite In_removes in h. destruct h.
      unfold Rge in H3. rewrite (notIn_filter _ (@eq_rule_dec Sig)) in H3.
      destruct H3. contradiction. destruct H3. clear H3.
      apply (bsucc_sub bwp). unfold rel. unfold brule, neg in H4. simpl in H4.
      rewrite negb_lr in H4. hyp.
      (* Rge << succeq *)
      apply incl_compat with R. unfold Rge. apply filter_incl.
      (* R << succeq *)
      intros l r h. apply (bsucceq_sub bwp). rewrite forallb_forall in H0.
      change (brule (bsucceq bwp) (mkRule l r) = true). apply H0. hyp.
      (* Egt << succ *)
      intros l r h. unfold Egt in h. rewrite In_removes in h. destruct h.
      unfold Ege in H3. rewrite (notIn_filter _ (@eq_rule_dec Sig)) in H3.
      destruct H3. contradiction. destruct H3. clear H3.
      apply (bsucc_sub bwp). unfold rel. unfold brule, neg in H4. simpl in H4.
      rewrite negb_lr in H4. hyp.
      (* Ege << succeq *)
      apply incl_compat with E. unfold Ege. apply filter_incl.
      (* E << succeq *)
      intros l r h. apply (bsucceq_sub bwp). rewrite forallb_forall in H.
      change (brule (bsucceq bwp) (mkRule l r) = true). apply H. hyp.
      (* WF (hd_red_mod Ege Rge) *)
      hyp.
    Qed.

    Lemma WF_rp_red : forall R,
      forallb (brule (bsucceq bwp)) R = true ->
      WF (red (filter (brule (neg (bsucc bwp))) R)) ->
      WF (red R).
      
    Proof.
      intros. rewrite <- red_mod_empty. apply WF_rp_red_mod. refl. hyp.
      simpl. rewrite red_mod_empty. hyp.
    Qed.
    
  End WeakRedPairProps.

  (* TEST: define a new Lemma use the second record type. where
  red_mod and red use the assumption [>] is closed by context. *)

  Section WeakRedPairProps2.
    
    Variable Sig: Signature.

    Variable bwp : bWeakRedPair2 Sig. 

    Lemma WF_wp_hd_red_mod2 : forall E R,
      forallb (brule (bsucceq2 bwp)) E = true ->
      forallb (brule (bsucceq2 bwp)) R = true ->
      WF (hd_red_mod E (filter (brule (neg (bsucc2 bwp))) R)) ->
      WF (hd_red_mod E R).

    Proof.
      intros. set (Rge := filter (brule (neg (bsucc2 bwp))) R).
      set (Rgt := removes (@eq_rule_dec Sig) Rge R).
      apply WF_incl with (hd_red_mod E (Rgt ++ Rge)).
      apply hd_red_mod_incl. refl. apply incl_removes_app.
      apply rule_elimination_hd_mod with (wp := mkWeak_reduction_pair
        (sc_succ2 bwp) (sc_succeq2 bwp) (cc_succeq2 bwp)(succ_succeq_compat2 bwp)
        (wf_succ2 bwp)).
      (* E << succeq *)
      intros l r h. apply (bsucceq_sub2 bwp). rewrite forallb_forall in H.
      change (brule (bsucceq2 bwp) (mkRule l r) = true). apply H. hyp.
      (* Rge << succeq *)
      apply incl_compat with R. unfold Rge. apply filter_incl.
      (* R << succeq *)
      intros l r h. apply (bsucceq_sub2 bwp). rewrite forallb_forall in H0.
      change (brule (bsucceq2 bwp) (mkRule l r) = true). apply H0. hyp.
      (* Rgt << succ *)
      intros l r h. unfold Rgt in h. rewrite In_removes in h. destruct h.
      unfold Rge in H3. rewrite (notIn_filter _ (@eq_rule_dec Sig)) in H3.
      destruct H3. contradiction. destruct H3. clear H3.
      apply (bsucc_sub2 bwp). unfold rel. unfold brule, neg in H4. simpl in H4.
      rewrite negb_lr in H4. hyp.
      (* WF (hd_red_mod E Rge) *)
      hyp.
    Qed.

    (* FIXME: move cc_scc inside the Record of bwp. *)

    (*Variable cc_succ2 : context_closed (succ2 bwp).*)

    Lemma WF_rp_red_mod2 : forall E R,
      forallb (brule (bsucceq2 bwp)) E = true ->
      forallb (brule (bsucceq2 bwp)) R = true ->
      WF (red_mod (filter (brule (neg (bsucc2 bwp))) E)
                  (filter (brule (neg (bsucc2 bwp))) R)) ->
      WF (red_mod E R).

    Proof.
      intros. set (Rge := filter (brule (neg (bsucc2 bwp))) R).
      set (Ege := filter (brule (neg (bsucc2 bwp))) E).
      set (Rgt := removes (@eq_rule_dec Sig) Rge R).
      set (Egt := removes (@eq_rule_dec Sig) Ege E).
      apply WF_incl with (red_mod (Egt ++ Ege) (Rgt ++ Rge)).
      apply red_mod_incl;  apply incl_removes_app.
      eapply rule_elimination_mod with (rp := mkReduction_pair
        (sc_succ2 bwp) (sc_succeq2 bwp) (cc_succ2 bwp) (cc_succeq2 bwp) (* FIXME: cc_succ *)
        (succ_succeq_compat2 bwp) (wf_succ2 bwp)).
      (* REMOVE later REMARK: mkReduction_pair require > is close by context. *)
      (* Rgt << succ *)
      intros l r h. unfold Rgt in h. rewrite In_removes in h. destruct h.
      unfold Rge in H3. rewrite (notIn_filter _ (@eq_rule_dec Sig)) in H3.
      destruct H3. contradiction. destruct H3. clear H3.
      apply (bsucc_sub2 bwp). unfold rel. unfold brule, neg in H4. simpl in H4.
      rewrite negb_lr in H4. hyp.
      (* Rge << succeq *)
      apply incl_compat with R. unfold Rge. apply filter_incl.
      (* R << succeq *)
      intros l r h. apply (bsucceq_sub2 bwp). rewrite forallb_forall in H0.
      change (brule (bsucceq2 bwp) (mkRule l r) = true). apply H0. hyp.
      (* Egt << succ *)
      intros l r h. unfold Egt in h. rewrite In_removes in h. destruct h.
      unfold Ege in H3. rewrite (notIn_filter _ (@eq_rule_dec Sig)) in H3.
      destruct H3. contradiction. destruct H3. clear H3.
      apply (bsucc_sub2 bwp). unfold rel. unfold brule, neg in H4. simpl in H4.
      rewrite negb_lr in H4. hyp.
      (* Ege << succeq *)
      apply incl_compat with E. unfold Ege. apply filter_incl.
      (* E << succeq *)
      intros l r h. apply (bsucceq_sub2 bwp). rewrite forallb_forall in H.
      change (brule (bsucceq2 bwp) (mkRule l r) = true). apply H. hyp.
      (* WF (hd_red_mod Ege Rge) *)
      hyp.
    Qed.

    Lemma WF_rp_red2 : forall R,
      forallb (brule (bsucceq2 bwp)) R = true ->
      WF (red (filter (brule (neg (bsucc2 bwp))) R)) ->
      WF (red R).
      
    Proof.
      intros. rewrite <- red_mod_empty. apply WF_rp_red_mod2. refl. hyp.
      simpl. rewrite red_mod_empty. hyp.
    Qed.
    
  End WeakRedPairProps2.

  (***********************************************************************)
  (** Reduction pair associated to a non-permutative non-collapsing
   arguments filtering. *)

  Require Import AFilterBool VecUtil.

  Section Filter.

    Variable Sig: Signature.
    
    Record Filter := mkFilter {
      pi: forall f, vector bool (@arity Sig f)
    }.

    Variable fil : Filter.

    Definition Sig_fil : Signature := filter_sig (pi fil).
    
  End Filter.

  Section WP_Filter.
    
    Variable Sig: Signature.
    Variable F : Filter Sig.

    Variable bwp: bWeakRedPair2 (Sig_fil F). (* FIXME: use the definition of second record *)

    Definition succ_f := filter_ord (succ2 bwp).   
    Definition wf_succ_f := WF_filter (wf_succ2 bwp).
    Definition sc_succ_f := filter_subs_closed (sc_succ2 bwp).

    Definition bsucc_f t u := (bsucc2 bwp) (filter (pi F) t) (filter (pi F) u).
    
    Lemma bsucc_sub_f : rel_of_bool bsucc_f << succ_f.

    Proof.
      intros t u h. apply bsucc_sub2. hyp.
    Qed.

    Definition succeq_f := filter_ord (succeq2 bwp).
    Definition sc_succeq_f := filter_subs_closed (sc_succeq2 bwp).
    Definition cc_succeq_f := filter_cont_closed (refl_succeq2 bwp) (cc_succeq2 bwp).
    
    (* FIXME: add cc_succ_f [>] is closed by context. *)
    Definition cc_succ_f := filter_cont_closed (refl_succ2 bwp) (cc_succ2 bwp).
    Lemma refl_succ_f : reflexive succ_f.
    Proof.
      intro x. unfold succ_f. apply refl_succ2.
    Qed.
    
    Lemma refl_succeq_f : reflexive succeq_f.
    Proof.
      intro x. unfold succeq_f. apply refl_succeq2.
    Qed.

    Lemma succ_succeq_compat_f : absorbs_left succ_f succeq_f.

    Proof.
      unfold absorbs_left, succ_f, succeq_f. intros t v [u [h1 h2]].
      unfold filter_ord in *. apply succ_succeq_compat2. exists (filter (pi F) u).
      auto.
    Qed.
      
    Definition bsucceq_f t u := (bsucceq2 bwp) (filter (pi F) t) (filter (pi F) u).
    
    Lemma bsucceq_sub_f : rel_of_bool bsucceq_f << succeq_f.

    Proof.
      intros t u h. apply bsucceq_sub2. hyp.
    Qed.

    Lemma trans_succ_f : transitive succ_f.
    
    Proof.
      apply filter_trans. apply trans_succ2.
    Qed.

    Lemma trans_succeq_f : transitive succeq_f.

    Proof.
      apply filter_trans. apply trans_succeq2.
    Qed.

    (** Record type bWeaRedPair for Filter . *)
    (* FIXME: use the definition of second record *)

    Definition bwrp_filter : bWeakRedPair2 Sig := mkbWeakRedPair2 
      wf_succ_f sc_succ_f bsucc_sub_f sc_succeq_f cc_succeq_f
      refl_succeq_f cc_succ_f refl_succ_f succ_succeq_compat_f
      bsucceq_sub_f trans_succ_f trans_succeq_f.

    (* TEST: filter with bWeakRedPair *)

    Definition bwrp_filter2 : bWeakRedPair Sig :=
      mkbWeakRedPair wf_succ_f sc_succ_f bsucc_sub_f
    sc_succeq_f cc_succeq_f refl_succeq_f succ_succeq_compat_f
    bsucceq_sub_f trans_succ_f trans_succeq_f.

  End WP_Filter.

  (***********************************************************************)
  (** Reduction pair associated to a permutative non-collapsing
     arguments filtering. *)
  
  Require Import AFilterPerm.

  Section Perm.

    Variable Sig: Signature.

    Record Perm := mkPerm {
      pi_perm : forall f: Sig, nat_lts (arity f);
      pi_perm_ok: non_dup pi_perm
      }.

    Variable perm : Perm.
    Definition Sig_perm : Signature := filter_sig (pi_perm perm).

  End Perm.

  Section WP_Perm.
    
    Variable Sig: Signature.
    Variable P : Perm Sig.
    
    Variable bwp : bWeakRedPair2 (Sig_perm P). (* FIXME: use the definition of second record.*)

    Notation aterm := (term Sig).

    Definition succ_p := filter_ord (succ2 bwp).

    Definition wf_succ_p := WF_filter (wf_succ2 bwp).
    Definition sc_succ_p := filter_subs_closed (sc_succ2 bwp).

    Definition bsucc_p (t u: aterm) : bool := (bsucc2 bwp) (filter (pi_perm P) t)
      (filter (pi_perm P) u).
   
    Lemma bsucc_sub_p : rel_of_bool bsucc_p << succ_p.

    Proof.
      intros t u h. apply bsucc_sub2. hyp.
    Qed.

    Definition succeq_p := filter_ord (succeq2 bwp).

    Definition sc_succeq_p := filter_subs_closed (sc_succeq2 bwp).

    Definition cc_succeq_p := filter_weak_cont_closed (pi_perm_ok P)
      (refl_succeq2 bwp) (cc_succeq2 bwp).

    (* FIXME: define cc_succ [>] is closed by context. *)

    Definition cc_succ_p := filter_weak_cont_closed (pi_perm_ok P)
      (refl_succ2 bwp) (cc_succ2 bwp).

    (* Proving [>] is reflexivity. *)

    Lemma refl_succ_p : reflexive succ_p.
    Proof.
      intro x. unfold succ_p. apply refl_succ2.
    Qed.
    
    Lemma refl_succeq_p : reflexive succeq_p.

    Proof.
      intro x. unfold succeq_p. apply refl_succeq2.
    Qed.

    Lemma succ_succeq_compat_p : absorbs_left succ_p succeq_p.

    Proof.
      unfold absorbs_left, succ_p, succeq_p. intros t v [u [h1 h2]].
      unfold filter_ord in *. apply succ_succeq_compat2.
      exists (filter (pi_perm P) u).
      auto.
    Qed.

    Definition bsucceq_p (t u: aterm) : bool := (bsucceq2 bwp) (filter (pi_perm P) t)
      (filter (pi_perm P) u).

    Lemma bsucceq_sub_p : rel_of_bool bsucceq_p << succeq_p.

    Proof.
      intros t u h. apply bsucceq_sub2. hyp.
    Qed.

    Lemma trans_succ_p : transitive succ_p.

    Proof.
      apply filter_trans. apply trans_succ2.
    Qed.

    Lemma trans_succeq_p : transitive succeq_p.

    Proof.
      apply filter_trans. apply trans_succeq2.
    Qed.

    (** Record type bWeaRedPair for Perm . *)
    (* FIXME: use the definition of second record. *)

  Definition bwrp_perm : bWeakRedPair2 Sig := mkbWeakRedPair2 wf_succ_p
    sc_succ_p bsucc_sub_p sc_succeq_p cc_succeq_p refl_succeq_p
    cc_succ_p refl_succ_p succ_succeq_compat_p bsucceq_sub_p
    trans_succ_p trans_succeq_p.

  (* TEST: perm with bWeakRedPair *)

  Definition bwrp_perm2 : bWeakRedPair Sig := mkbWeakRedPair wf_succ_p
    sc_succ_p bsucc_sub_p sc_succeq_p cc_succeq_p refl_succeq_p
    succ_succeq_compat_p bsucceq_sub_p trans_succ_p trans_succeq_p.

End WP_Perm.

  (***********************************************************************)
  (** Reduction pair associated to collapsing arguments filtering. *)

  Require Import AProj.

  Section Proj.

    Variable Sig: Signature.

    Record Proj := mkProj {
      pi_proj : forall f: Sig, option {k | k < arity f}
    }.

  End Proj.

  Section WP_Proj.

    Variable Sig: Signature.
    Variable Pj : Proj Sig.

    Variable bwp : bWeakRedPair2 Sig. (* FIXME: use the definition of second record. *)

    Definition succ_pj := proj_ord (pi_proj Pj) (succ2 bwp).

    Definition wf_succ_pj := WF_proj (pi_proj Pj) (wf_succ2 bwp).

    Definition sc_succ_pj := proj_subs_closed (pi_proj Pj) (sc_succ2 bwp).

    Notation aterm := (term Sig).

    Definition bsucc_pj (t u: aterm): bool := (bsucc2 bwp) (proj (pi_proj Pj) t)
      (proj (pi_proj Pj) u).

    Lemma bsucc_sub_pj : rel_of_bool bsucc_pj << succ_pj.

    Proof.
      intros t u h. apply bsucc_sub2. hyp.
    Qed.

    Definition succeq_pj := proj_ord (pi_proj Pj) (succeq2 bwp).

    Definition sc_succeq_pj := proj_subs_closed (pi_proj Pj) (sc_succeq2 bwp).

    Definition cc_succeq_pj := proj_cont_closed (pi_proj Pj)
      (refl_succeq2 bwp) (cc_succeq2 bwp).

    (* FIXME: define [>] is closed by context. *)

    Definition cc_succ_pj := proj_cont_closed (pi_proj Pj)
       (refl_succ2 bwp) (cc_succ2 bwp).

    (* Proving [>] is reflexivity. *)

    Lemma refl_succ_pj : reflexive succ_pj.
    Proof.
      intro x. unfold succ_pj. apply refl_succ2.
    Qed.
    
    Lemma refl_succeq_pj : reflexive succeq_pj.

    Proof.
      intro x. unfold succeq_pj. apply refl_succeq2.
    Qed.

    Lemma succ_succeq_compat_pj : absorbs_left succ_pj succeq_pj.

    Proof.
      unfold absorbs_left, succ_pj, succeq_pj. intros t v [u [h1 h2]].
      unfold proj_ord in *. apply succ_succeq_compat2.
      exists (proj (pi_proj Pj) u).
      auto.
    Qed.

    Definition bsucceq_pj (t u: aterm) : bool :=
      (bsucceq2 bwp) (proj (pi_proj Pj) t)(proj (pi_proj Pj) u).

    Lemma bsucceq_sub_pj : rel_of_bool bsucceq_pj << succeq_pj.

    Proof.
      intros t u h. apply bsucceq_sub2. hyp.
    Qed.

    Lemma trans_succ_pj : transitive succ_pj.

    Proof.
      apply proj_trans. apply trans_succ2.
    Qed.

    Lemma trans_succeq_pj : transitive succeq_pj.

    Proof.
      apply proj_trans. apply trans_succeq2.
    Qed.

    (** Record type bWeaRedPair for Proj. *)
    (* FIXME: use the definition of second record. *)

    Definition bwrp_proj : bWeakRedPair2 Sig := mkbWeakRedPair2
      wf_succ_pj sc_succ_pj bsucc_sub_pj sc_succeq_pj cc_succeq_pj
      refl_succeq_pj cc_succ_pj refl_succ_pj succ_succeq_compat_pj
      bsucceq_sub_pj trans_succ_pj trans_succeq_pj.

    Definition bwrp_proj2 : bWeakRedPair Sig := mkbWeakRedPair
      wf_succ_pj sc_succ_pj bsucc_sub_pj sc_succeq_pj cc_succeq_pj
      refl_succeq_pj succ_succeq_compat_pj
      bsucceq_sub_pj trans_succ_pj trans_succeq_pj.


  End WP_Proj.

  (***********************************************************************)
  (* REMARK: move WF_MonAlg here because [succ] used in Filter need to
     write as [Top.S.succ] if import [AMonAlg2.v] *)

  (***********************************************************************)
  (** ** Reduction pair associated to a monotone algebra. *)

  Require Import AMonAlg2.

  Section WF_MonAlg.
    
    Variable Sig: Signature.
    (*Variable MA : bMonoAlgType Sig. (* FIXME *)*)
    Variable MA : bMonoAlgType Sig. (* FIXME *)

    Definition succ_ma := IR (I Sig MA) (succ Sig MA).
    Definition wf_succ_ma := IR_WF (I Sig MA) (succ_wf Sig MA). 
    Definition sc_succ_ma := @IR_substitution_closed _ _ (succ Sig MA).

    Definition bsucc_ma := bool_of_rel (succ'_dec Sig MA).

    Lemma bsucc_sub_ma : rel_of_bool (bsucc_ma) << (succ_ma).
      
    Proof.
      intros t u. unfold rel_of_bool, bsucc_ma, bool_of_rel.
      case ((succ'_dec Sig MA) t u); intros.
      apply succ'_sub. hyp. discr.
    Qed.

    Definition succeq_ma := IR (I Sig MA) (succeq Sig MA).
    Definition sc_succeq_ma := @IR_substitution_closed _ _ (succeq Sig MA).
    Definition cc_succeq_ma := @IR_context_closed _ _ _ (monotone_succeq Sig MA).
    Definition refl_succeq_ma := @IR_reflexive _ _ _ (refl_succeq Sig MA).

    Lemma succ_succeq_compat_ma : absorbs_left succ_ma succeq_ma.
      
    Proof.
      intros x z xz val. apply succ_succeq_compat.
      destruct xz as [y [ge_xy gt_yz]]. exists (term_int val y). split; auto.
    Qed.

    Definition bsucceq_ma := bool_of_rel (succeq'_dec Sig MA).

    Lemma bsucceq_sub_ma : rel_of_bool bsucceq_ma << succeq_ma.
      
    Proof.
      intros t u. unfold rel_of_bool, bsucceq_ma, bool_of_rel. 
      case ((succeq'_dec Sig MA) t u); intros.
      apply (succeq'_sub Sig MA). hyp. discr.
    Qed.

    Definition trans_succ_ma := IR_transitive (trans_succ Sig MA).
    Definition trans_succeq_ma := IR_transitive (trans_succeq Sig MA).

    (** Record type bWeaRedPair. *)
    
    Definition bwrp := mkbWeakRedPair wf_succ_ma sc_succ_ma
      bsucc_sub_ma sc_succeq_ma cc_succeq_ma refl_succeq_ma
      succ_succeq_compat_ma bsucceq_sub_ma trans_succ_ma
      trans_succeq_ma.

  End WF_MonAlg.

End S.