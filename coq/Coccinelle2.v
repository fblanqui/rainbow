(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-02-22, 2009-10-20 (rpo)

convert CoLoR terms into Coccinelle terms

- Ly Kim Quyen, 2013-09-16

Re-define module type into Section.

*)

Set Implicit Arguments.

Require Import LogicUtil VecUtil List Relations SN ASubstitution ASignature.

(***********************************************************************)
(** convert CoLoR terms into Coccinelle terms *)

Section Make_Term.

  Variable Sig: Signature.

  Notation aterm  := (ATerm.term Sig).
  Notation aterms := (vector aterm).
  Notation AVar   := ATerm.Var.
  Notation Fun    := ATerm.Fun.

  Require Import term2.
  
  Fixpoint term_of_aterm (t:aterm): term Sig :=
    match t with
      | AVar x   => Var Sig x
      | Fun f ts =>
        let fix terms_of_aterms n (ts : aterms n) :=
          match ts with
            | Vnil         => nil
            | Vcons u k us => term_of_aterm u :: terms_of_aterms k us
          end in Term f (terms_of_aterms (arity f) ts)
    end.

  Fixpoint terms_of_aterms n (ts : aterms n) :=
    match ts with
      | Vnil         => nil
      | Vcons u k us => term_of_aterm u :: terms_of_aterms us
    end.

    Lemma terms_of_aterms_eq : forall n (ts : aterms n),
    (fix terms_of_aterms n (ts : aterms n) :=
      match ts with
        | Vnil         => nil
        | Vcons u k us => term_of_aterm u :: terms_of_aterms k us
      end) n ts = terms_of_aterms ts.

  Proof.
    induction ts; simpl; intros. refl. rewrite IHts. refl.
  Qed.

  Lemma term_of_aterm_fun : forall f ts,
    term_of_aterm (Fun f ts) = Term f (terms_of_aterms ts).

  Proof.
    intros. simpl. rewrite terms_of_aterms_eq. refl.
  Qed.

  Require Import VecUtil.

  Lemma terms_of_aterms_cast : forall n (ts : aterms n) p (e : n=p),
    terms_of_aterms (Vcast ts e) = terms_of_aterms ts.

  Proof.
    induction ts; destruct p; simpl; intros; try discr. refl.
    inversion e. subst p. rewrite IHts. refl.
  Qed.

  Lemma terms_of_aterms_app : forall n (ts : aterms n) p (us : aterms p),
    terms_of_aterms (Vapp ts us) = terms_of_aterms ts ++ terms_of_aterms us.

  Proof.
    induction ts; simpl; intros. refl. rewrite IHts. refl.
  Qed.

  Lemma length_terms_of_aterms : forall n (ts : aterms n),
    length (terms_of_aterms ts) = n.

  Proof.
    induction ts; simpl; intros. refl. rewrite IHts. refl.
  Qed.

  Require Import Datatypes.

  Fixpoint sub_of_asub (s : ASubstitution.substitution Sig) n :=
    match n with
      | 0    => nil
      | S n' => (n', term_of_aterm (s n')) :: sub_of_asub s n'
    end.

  (********************************************************************************)

  Require Import more_list NatUtil EqUtil.
  
  Notation find := (@find _ var_eq_bool _).

  Lemma find_sub_of_asub : forall s n v, find v (sub_of_asub s n) =
    if bgt_nat n v then Some (term_of_aterm (s v)) else None.

  Proof.
    induction n; intros. refl. simpl sub_of_asub. simpl more_list.find.
    rewrite IHn. unfold var_eq_bool. case_beq_nat v n.
    assert (bgt_nat (S v) v = true). rewrite bgt_nat_ok. omega. rewrite H.
    refl.
    case_eq (bgt_nat n v); intros; case_eq (bgt_nat (S n) v); intros.
    refl. rewrite bgt_nat_ok in H0. rewrite bgt_nat_ko in H1. absurd_arith.
    rewrite bgt_nat_ok in H1. rewrite bgt_nat_ko in H0.
    rewrite (beq_ko NatUtil.beq_nat_ok) in H. absurd_arith. refl.
  Qed.
 
  Notation apply_subst := (@apply_subst Sig).

  Lemma term_of_aterm_sub : forall s k t, k > ATerm.maxvar t ->
    term_of_aterm (sub s t) = apply_subst (sub_of_asub s k) (term_of_aterm t).

  Proof.
    intros s k t; pattern t; apply ATerm.term_ind
      with (Q := fun n (ts : aterms n) =>
        k > ATerm.maxvars ts -> terms_of_aterms (Vmap (sub s) ts) =
        map (apply_subst (sub_of_asub s k)) (terms_of_aterms ts)); clear t.
    simpl in *. intros.
    rewrite find_sub_of_asub. case_eq (bgt_nat k x); intros.
    refl. rewrite bgt_nat_ko in H0. absurd_arith.
    intros. simpl sub. rewrite !term_of_aterm_fun. simpl.
    apply (f_equal (Term f)). apply H. hyp.
    refl. intros t n ts. simpl. rewrite ATerm.maxvars_cons. rewrite gt_max.
    intros. destruct H1. rewrite H. 2: hyp. rewrite H0. 2: hyp. refl.
  Qed.

  Require Import APosition.
  Require Import AContext.

  Lemma term_of_aterm_fill : forall u t c, term_of_aterm (fill c t) =
    replace_at_pos (term_of_aterm (fill c u)) (term_of_aterm t) (pos_context c).

  Proof.
    induction c; intros. refl. simpl fill. simpl pos_context.
    rewrite !term_of_aterm_fun, replace_at_pos_unfold.
    apply (f_equal (Term f)).
    rewrite !terms_of_aterms_cast, !terms_of_aterms_app. simpl.
    rewrite replace_at_pos_list_replace_at_pos_in_subterm, <- IHc. refl.
    rewrite length_terms_of_aterms. refl.
  Qed.

  Lemma is_a_pos_context : forall u c,
    is_a_pos (term_of_aterm (fill c u)) (pos_context c) = true.

  Proof.
    induction c; intros. refl. simpl fill. rewrite term_of_aterm_fun. simpl.
    rewrite terms_of_aterms_cast. rewrite terms_of_aterms_app. simpl.
    assert (nth_error (terms_of_aterms t ++ term_of_aterm (fill c u) ::
      terms_of_aterms t0) i = nth_error (terms_of_aterms t ++ term_of_aterm
        (fill c u) :: terms_of_aterms t0) (length (terms_of_aterms t))).
    apply (f_equal (nth_error (terms_of_aterms t ++ term_of_aterm (fill c u)
      :: terms_of_aterms t0))). rewrite length_terms_of_aterms. refl.
    rewrite H. rewrite nth_error_at_pos. hyp.
  Qed.

End Make_Term.

(***********************************************************************)
(** module type for using Coccinelle's RPO *)

Require Import rpo_extension.

Section S.

  Section P.

    Variable Sig: Signature.

    Class Pre := mkPrecedence {
      Pre_status         : Sig -> rpo.status_type;
      Pre_prec_nat       : Sig -> nat;
      Pre_bb             : nat}.

  End P.

(***********************************************************************)
(** convert Coccinelle RPO into a CoLoR WeakRedPair *)

Require Import ARedPair2 ARelation RelUtil BoolUtil.

Section WP_PRO.

  (* Assume bb is a variable in rpo. *)

  Variable bb  : nat.
  Variable Sig : Signature.
  Context {Pr  : Pre Sig}.

  Parameter Pre_prec_eq_status : forall f g,
   rpo_extension.prec_eq (@Pre_prec_nat Sig Pr) f g ->
   Pre_status f = Pre_status g.

  Definition Prec := rpo_extension.Precedence (@Pre_status _ _)
                                              (@Pre_prec_nat _ _) 
                                              (@Pre_prec_eq_status).

  Require Import rpo2.

  Notation rpo := (@rpo Sig Prec bb).

  Definition succ := transp (Rof rpo (term_of_aterm (Sig:=Sig))).

  Require Import Inverse_Image.

  Lemma wf_succ : WF succ.

  Proof.
    apply wf_WF_transp.
    apply wf_inverse_image with (f:=@term_of_aterm Sig).
    apply wf_rpo. apply prec_wf.
  Qed.

  Require Import Max Datatypes.

  Lemma sc_succ : substitution_closed succ.

  Proof.
    intros t u s h. unfold succ, transp, Rof. set (k:=max(maxvar t)(maxvar u)).
    rewrite term_of_aterm_sub with (k:=S k). 2: apply le_n_S; apply le_max_r.
    rewrite term_of_aterm_sub with (k:=S k). 2: apply le_n_S; apply le_max_l.
    apply rpo_subst. hyp. 
   Qed.

  Notation empty_rpo_infos   := (@empty_rpo_infos Sig Prec bb).
  Notation rpo_eval          := (@rpo_eval Sig Prec empty_rpo_infos bb).
  Notation rpo_eval_is_sound := (rpo_eval_is_sound_weak empty_rpo_infos bb).

  Require Import ordered_set.

  Definition bsucc t u :=
    match rpo_eval ((term_of_aterm (Sig:=Sig))t)
          ((term_of_aterm (Sig:=Sig))u) with
      | Some Greater_than => true
      | _ => false
    end.

  Lemma bsucc_ok : forall t u, bsucc t u = true -> succ t u.

  Proof.
    intros t u. unfold bsucc.
    gen (rpo_eval_is_sound (term_of_aterm t) (term_of_aterm u)).
    case (rpo2.rpo_eval empty_rpo_infos bb (term_of_aterm t) (term_of_aterm u));
      try discr.
    destruct c; try discr. unfold succ, transp, Rof. auto.
  Qed.

  Lemma bsucc_sub : rel_of_bool bsucc << succ.

  Proof.
    intros t u. unfold rel_of_bool. intro h. apply bsucc_ok. hyp.
  Qed.

  Definition equiv_aterm := Rof (@equiv Sig Prec)(@term_of_aterm Sig).

  Definition succeq := succ U equiv_aterm.

  Lemma sc_succeq : substitution_closed succeq.

  Proof.
    intros t u s [h|h]. left. apply sc_succ. hyp. right.
    unfold equiv_aterm, Rof. set (k := max (maxvar t) (maxvar u)).
    rewrite term_of_aterm_sub with (k:=S k). 2: apply le_n_S; apply le_max_l.
    rewrite term_of_aterm_sub with (k:=S k). 2: apply le_n_S; apply le_max_r.
    apply equiv_subst. hyp.
  Qed.

  Notation AVar := ATerm.Var.

  Lemma cc_succ : context_closed succ.

  Proof.
    intros t u c h. unfold succ, transp, Rof.
    rewrite term_of_aterm_fill with (u := AVar 0) (t:=t).
    rewrite term_of_aterm_fill with (u := AVar 0) (t:=u).
    eapply rpo_add_context. hyp. apply is_a_pos_context.
  Qed.

  Lemma cc_equiv_aterm : context_closed equiv_aterm.

  Proof.
    intros t u c h. unfold equiv_aterm, Rof.
    rewrite term_of_aterm_fill with (u := AVar 0) (t:=t).
    rewrite term_of_aterm_fill with (u := AVar 0) (t:=u).
    apply equiv_add_context. hyp. apply is_a_pos_context.
  Qed.

  Lemma cc_succeq : context_closed succeq.

  Proof.
    intros t u c [h|h]. left. apply cc_succ. hyp.
    right. apply cc_equiv_aterm. hyp.
  Qed.

  Lemma refl_succeq : reflexive succeq.

  Proof.
    intro t. right.
    apply rpo2.Eq.
  Qed.

  Lemma succ_succeq_compat : absorbs_left succ succeq.

  Proof.
    intros t v [u [[h1|h1] h2]]. apply rpo_trans with (term_of_aterm u); hyp.
    unfold succ, transp, Rof. rewrite equiv_rpo_equiv_1. apply h2.
    hyp.
  Qed.

  Definition bsucceq t u :=
    match rpo_eval (@term_of_aterm Sig t) (@term_of_aterm Sig u) with
      | Some Greater_than | Some Equivalent => true
      | _ => false
    end.

  Lemma bsucceq_ok : forall t u, bsucceq t u = true -> succeq t u.

  Proof.
    intros t u. unfold bsucceq.
    gen (rpo_eval_is_sound (term_of_aterm t) (term_of_aterm u)).
    case (rpo_eval (term_of_aterm t) (term_of_aterm u)); try discr.
    destruct c; try discr; unfold succeq, Relation_Operators.union,
      equiv_aterm, succ, transp, Rof; auto.
  Qed.

  Definition bsucceq_sub : rel_of_bool bsucceq << succeq.

  Proof.
    intros t u. unfold rel_of_bool. intro h. apply bsucceq_ok. hyp.
  Qed.

  Lemma trans_succ : transitive succ.

  Proof.
    unfold succ. apply transp_trans. apply Rof_trans.
    intros t u v htu huv. apply rpo_trans with u; hyp.
  Qed.

  Lemma trans_equiv_aterm : transitive equiv_aterm.

  Proof.
    unfold equiv_aterm. apply Rof_trans.
    apply (equiv_trans _ _ (equiv_equiv Sig Prec)).
  Qed.

  Lemma trans_succeq : transitive succeq.

  Proof.
    unfold succeq, Relation_Operators.union, transitive.
    intuition.
    left. apply trans_succ with y; hyp.
    left. revert H. unfold equiv_aterm, succ, transp, Rof. intro.
    rewrite <- equiv_rpo_equiv_2. apply H1. hyp.
    left. revert H1. unfold equiv_aterm, succ, transp, Rof. intro.
    rewrite equiv_rpo_equiv_1. apply H. hyp.
    right. apply trans_equiv_aterm with y; hyp.
  Qed.

  (** Record type bWeaRedPair. *)

  Definition impl_weak_rp := @mkWeak_reduction_pair Sig succ succeq
    sc_succ sc_succeq cc_succeq succ_succeq_compat wf_succ.

  Global Instance WP_RPO : DS_WeakRedPair Sig.
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
  
End WP_PRO.  

End S.