(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Hans Zantema, 2007-03

  This file contains a definition of weakly monotone algebra and
  extended monotone algebra and some results concerning them, based
  on:

References:
  J. Endrullis, J. Waldmann and H. Zantema,
  "Matrix Interpretations for Proving Termination of Term Rewriting",
  Proceedings of the 3rd International Joint Conference (IJCAR 2006), 2006.
*)

Require Import ATrs RelUtil SN ListUtil ARelation LogicUtil ACompat.
Require Export AWFMInterpretation.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig).

  (***********************************************************************)
  (** * Module type specifying a weakly monotone algebra.                *)

  (**
     A weakly monotone algebra consist of:
     - interpretation [I]
     - [succ] and [succeq] relations
     along with the following conditions:
     - [IM]: [I] is monotone with respect to [succ]
     - [succ_wf]: [succ] is well-founded
     - [succ_succeq_compat]: compatibility between [succ] and [succeq]
     - [succ_dec] ([succeq_dec]): decidability of [succ] ([succeq])

     An extended monotone algebra additionaly requires that every 
   operation is monotone with respect to [succ] but we demand
   it as an extra hypothesis in respective theorems (dealing with
   extended monotone algebras). *)

  Record bMonoAlgType : Type := mkbMonoAlgType {
    I : interpretation Sig;
    succ : relation I;
    succeq : relation I;

    refl_succeq : reflexive succeq;
    trans_succ : transitive succ;
    trans_succeq : transitive succeq;

    monotone_succeq : monotone I succeq;

    (*monotone_succ : monotone I succ; (* FIXME: [>] is monotone [test] *)
    refl_succ : reflexive succ; (* FIXME: add reflexivity of [>] *)
     *)

    succ_wf : WF succ;

    succ_succeq_compat : absorbs_left succ succeq;

    IR_succ := (IR I succ);
    IR_succeq := (IR I succeq);

    succ' : relation term;
    succeq' : relation term;
    succ'_sub : succ' << IR_succ;
    succeq'_sub : succeq' << IR_succeq;
    succ'_dec : rel_dec succ';
    succeq'_dec : rel_dec succeq'
}.

(***********************************************************************)
(** * Functor with a theory of weakly monotone algebras                *)

  Section MonotoneAlgebraResults.

    Variable ma : bMonoAlgType.

    Lemma absorb_succ_succeq : absorbs_left (IR_succ ma) (IR_succeq ma).
      
    Proof.
      intros x z xz val.
      apply succ_succeq_compat.
      destruct xz as [y [ge_xy gt_yz]].
      exists (term_int val y). split; auto.
    Qed.
    
    Lemma IR_rewrite_ordering : forall S,
      monotone (I ma) S -> rewrite_ordering (IR (I ma) S).

    Proof.
      split.
      apply IR_substitution_closed.
      apply IR_context_closed; hyp.
    Qed.
    
    Lemma ma_succeq_rewrite_ordering : rewrite_ordering (IR_succeq ma).
      
    Proof.
      apply IR_rewrite_ordering.
      exact (monotone_succeq ma).
    Qed.

    Definition part_succeq := rule_partition (succeq'_dec ma).
    Definition part_succ := rule_partition (succ'_dec ma).
    
    Lemma partition_succ_compat : forall R,
      compat (IR_succ ma) (fst (partition part_succ R)).
      
    Proof.
      intros R l r lr.
      apply succ'_sub.
      apply partition_by_rel_true with S.term (succ'_dec ma).
      apply rule_partition_left with R; hyp.
    Qed.

    (** Relative termination criterion with monotone algebras. *)

    Section RelativeTermination.
      
      Variable R E : rules Sig.

      Lemma ma_compat_red_mod : monotone (I ma) (succ ma) ->
        compat (IR_succ ma) R ->
        compat (IR_succeq ma) E -> WF (red_mod E R).

      Proof.
        intros. apply WF_incl with (IR_succ ma).
        apply compat_red_mod with (IR_succeq ma); trivial.
        apply IR_rewrite_ordering; trivial.
        exact ma_succeq_rewrite_ordering.
        exact absorb_succ_succeq.
        apply IR_WF. exact (succ_wf ma).
      Qed.

    End RelativeTermination.
  
    (** Top termination (for DP setting) criterion with monotone algebras. *)

    Section RelativeTopTermination.

      Variable R E : rules Sig.

      Lemma ma_compat_hd_red_mod : compat (IR_succ ma) R ->
        compat (IR_succeq ma) E ->
        WF (hd_red_mod E R).
        
      Proof.
        intros. apply WF_incl with (IR_succ ma).
        apply compat_hd_red_mod with (IR_succeq ma); trivial.
        apply IR_substitution_closed.
        exact ma_succeq_rewrite_ordering.
        exact absorb_succ_succeq.
        apply IR_WF. exact (succ_wf ma).
      Qed.

    End RelativeTopTermination.
  
    (** Results and tactics for proving relative termination 
       of concrete examples. *)

    Section RelativeTerminationCriterion.
      
      Variable R E : rules Sig.
      
      Lemma partition_succeq_compat : forall R,
        snd (partition part_succeq R) = nil ->
        compat (IR_succeq ma) (snd (partition part_succ R)).
        
      Proof.
        clear R. intros R Rpart l r lr.
        apply succeq'_sub.
        apply partition_by_rel_true with S.term (succeq'_dec ma).
        apply rule_partition_left with R. fold part_succeq.
        ded (partition_complete part_succeq (mkRule l r) R).
        simpl in H. rewrite Rpart in H. destruct H.
        apply partition_inright with part_succ. hyp.
        hyp. destruct H.
      Qed.

      Lemma ma_relative_termination : 
        let E_gt := partition part_succ E in
        let E_ge := partition part_succeq E in
        let R_gt := partition part_succ R in
        let R_ge := partition part_succeq R in
          monotone (I ma) (succ ma) ->
          snd R_ge = nil ->
          snd E_ge = nil ->
          WF (red_mod (snd E_gt) (snd R_gt)) ->
          WF (red_mod E R).

      Proof.
        intros. unfold red_mod.
        set (Egt := fst E_gt) in *. set (Ege := snd E_gt) in *.
        set (Rgt := fst R_gt) in *. set (Rge := snd R_gt) in *.
        apply WF_incl with ((red Egt U red Ege)# @ (red Rgt U red Rge)).
        comp. apply clos_refl_trans_inclusion. apply rule_partition_complete. 
        apply rule_partition_complete.
        apply wf_rel_mod. fold (red_mod Ege Rge); hyp.
        apply WF_incl with (red_mod (Rge ++ Ege) (Rgt ++ Egt)).
        unfold red_mod. comp. 
        apply clos_refl_trans_inclusion. apply red_union_inv. apply red_union_inv.
        apply ma_compat_red_mod; trivial.
        apply compat_app.
        unfold Rgt, R_gt, part_succ; apply partition_succ_compat.
        unfold Egt, E_gt, part_succ; apply partition_succ_compat.
        apply compat_app.
        unfold Rge, R_gt. apply partition_succeq_compat; hyp.  
        unfold Ege, E_gt. apply partition_succeq_compat; hyp. 
      Qed.

    End RelativeTerminationCriterion.

    (** Results and tactics for proving termination (as a special
       case of relative termination) of concrete examples. *)

    Section TerminationCriterion.
      
      Variable R : rules Sig.
      
      Lemma ma_termination :       
        let R_gt := partition part_succ R in
        let R_ge := partition part_succeq R in
          monotone (I ma) (succ ma) ->
          snd R_ge = nil ->
          WF (red (snd R_gt)) ->
          WF (red R).

      Proof.
        intros. apply WF_incl with (red_mod nil R). apply red_incl_red_mod.
        apply ma_relative_termination. hyp. hyp. trivial.
        simpl. apply WF_incl with (red (snd (partition part_succ R))).
        apply red_mod_empty_incl_red. hyp.
      Qed.
      
    End TerminationCriterion.
  
    (** Results and tactics for proving relative top termination 
    of concrete examples. *)

    Section RelativeTopTerminationCriterion.

      Variable R E : rules Sig.
      
      Lemma partition_succeq_compat_fst : forall R,
        compat (IR_succeq ma) (fst (partition part_succeq R)).
        
      Proof.
        clear R. intros R l r lr.
        apply succeq'_sub.
        apply partition_by_rel_true with S.term (succeq'_dec ma).
        apply rule_partition_left with R. hyp.
      Qed.

      Lemma partition_succeq_compat_snd : forall R,
        snd (partition part_succeq R) = nil ->
        compat (IR_succeq ma)(snd (partition part_succ R)).
        
      Proof.
        clear R. intros R Rpart l r lr.
        apply succeq'_sub.
        apply partition_by_rel_true with S.term (succeq'_dec ma).
        apply rule_partition_left with R. fold part_succeq.
        ded (partition_complete part_succeq (mkRule l r) R).
        simpl in H. rewrite Rpart in H. destruct H.
        apply partition_inright with part_succ. hyp. 
        hyp. destruct H.
      Qed.

      Lemma ma_relative_top_termination :
        let E_ge := partition part_succeq E in
        let R_gt := partition part_succ R in
        let R_ge := partition part_succeq R in
          snd R_ge = nil ->
          snd E_ge = nil ->
          WF (hd_red_mod E (snd R_gt)) ->
          WF (hd_red_mod E R).
        
      Proof.
        intros. unfold hd_red_mod.
        set (Rgt := fst R_gt) in *. set (Rge := snd R_gt) in *.
        apply WF_incl with (red E # @ (hd_red Rgt U hd_red Rge)).
        comp. incl_trans (hd_red Rgt U hd_red Rge).
        apply hd_rule_partition_complete.
        apply wf_rel_mod_simpl. fold (red_mod E Rge). hyp.
        apply WF_incl with (hd_red_mod (Rge ++ E) Rgt).
        unfold hd_red_mod. comp.
        apply clos_refl_trans_inclusion.
        incl_trans (red Rge U red E). union. apply hd_red_incl_red.
        apply red_union_inv.
        apply ma_compat_hd_red_mod; trivial.
        unfold Rgt, R_gt, part_succ. apply partition_succ_compat.
        apply compat_app.
        unfold Rge, R_gt. apply partition_succeq_compat_snd. hyp.
        apply incl_compat with (fst E_ge ++ snd E_ge). unfold incl. intros.
        apply in_or_app. unfold E_ge. apply partition_complete. exact H2.
        rewrite H0. rewrite <- app_nil_end.
        unfold E_ge. apply partition_succeq_compat_fst.
      Qed.
      
    End RelativeTopTerminationCriterion.
  
  End MonotoneAlgebraResults.

End S.