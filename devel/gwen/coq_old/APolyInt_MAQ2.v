(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Hans Zantema, 2007-04-25

* Polynomial interpretations in the setting of monotone algebras.

- Kim Quyen Ly, 2013-08-29

* Polynomial interpretations in the setting of monotone algebras on
  domain rational numbers.

*)

Require Import NewAPolyInt2 AMonAlg2 ZUtil RelUtil NewPositivePolynom2
  ATrs ListForall NewMonotonePolynom2 LogicUtil BoolUtil NewPolynom2
  OrdRingType2.

Section S.

  Variable Sig : Signature.

  Section TPolyIntQ.

    Record TPolyIntQ : Type := mkbTPolyInt {
      trsIntQ : forall f: Sig, Qpoly (arity f);
      trsIntQ_wm : PolyWeakMonotone trsIntQ
    }.

  End TPolyIntQ.

  Section PolyIntQ.

    Variable pi : TPolyIntQ.

    Definition I := Int_of_PI (trsIntQ_wm pi).

    Definition succQ := QDgt.

    Definition succeqQ := QDge.

    Lemma refl_Dge : reflexive QDge.
    Proof.
      intros [x hs]. unfold QDge. simpl. unfold QgeA. intuition.
    Qed.

    Lemma trans_Dgt : transitive QDgt.
    Proof.
      intros [x hx] [y hy] [z hz].
      unfold QDgt. simpl. apply QgtA_trans.
    Qed.

    Lemma trans_Dge : transitive QDge.
    Proof.
      intros [x hx] [y hy] [z hz].
      unfold QDge. simpl. apply QgeA_trans.
    Qed.

    Definition refl_succeqQ := refl_Dge.

    Definition trans_succQ := trans_Dgt.

    Definition trans_succeqQ := trans_Dge.

    Lemma monotone_succeq : AWFMInterpretation.monotone I succeqQ.

    Proof.
      unfold I. apply pi_monotone_eq. 
    Qed.

    Definition succ_wfQ := WF_DgtQ.

    Lemma succ_succeq_compat : absorbs_left succQ succeqQ.

    Proof.
      unfold succQ, succeqQ. intros p q pq. destruct pq as [r [pr rq]].
      unfold QDgt. unfold QDge in pr. unfold QDgt in rq.
      apply QgeA_gtA_trans with (proj1_sig r); auto. 
    Qed.

    Definition rulePoly_gtQ del l r := rulePoly_gtQ (trsIntQ pi) del (@mkRule Sig l r).

    Definition succ' del l r := coef_not_neg (rulePoly_gtQ del l r).

    Definition bsucc' del l r := bcoef_not_neg (rulePoly_gtQ del l r).

    Lemma bsucc'_ok : forall del l r, bsucc' del l r = true <-> succ' del l r.

    Proof.
      intros del l r. unfold bsucc', succ'. apply bcoef_not_neg_ok.
    Qed.

    Lemma succ'_dec: forall del, rel_dec (succ' del).

    Proof.
      intros del l r. unfold succ'. eapply dec. apply bcoef_not_neg_ok.
    Defined.

    Definition rulePoly_geQ l r := rulePoly_geQ (trsIntQ pi) (@mkRule Sig l r).

    Definition succeq' l r := coef_not_neg (rulePoly_geQ l r).

    Definition bsucceq' l r := bcoef_not_neg (rulePoly_geQ l r).

    Lemma bsucceq'_ok : forall l r, bsucceq' l r = true <-> succeq' l r.

    Proof.
      intros l r. unfold bsucceq', succeq'. apply bcoef_not_neg_ok.
    Qed.

    Lemma succeq'_dec : rel_dec succeq'.

    Proof.
      intros l r. unfold succeq'. eapply dec. apply bcoef_not_neg_ok.
    Defined.

    Lemma succ'_sub : forall del, (succ' del) << IR I succQ.

    Proof.
      intros del t u tu. unfold I, succQ. set (r := mkRule t u).
      change t with (lhs r). change u with (rhs r).
      apply pi_compat_rule with (del:=del). hyp.
    Qed.

    Lemma succeq'_sub : succeq' << IR I succeqQ.

    Proof.
      intros t u tu. unfold I, succQ. set (r := mkRule t u).
      change t with (lhs r). change u with (rhs r).
      apply pi_compat_rule_weak. hyp.
    Qed.

    (** Record type of MonotoneAlgType. *)

    Variable del: QArith_base.Q.

    Definition matQ := mkbMonoAlgType Sig I QDgt QDge refl_succeqQ
      trans_Dgt trans_Dge monotone_succeq succ_wfQ succ_succeq_compat
      (succ' del) succeq' (succ'_sub del) succeq'_sub (succ'_dec del) succeq'_dec.

    Section ExtendedMonotoneAlgebra.

      Lemma monotone_succ : PolyStrongMonotone (trsIntQ pi)->
        AWFMInterpretation.monotone I succQ.

      Proof.
        unfold I. apply pi_monotone.
      Qed.

    End ExtendedMonotoneAlgebra.
    
    Require Import List.

    Section fin_Sig.

      Variable Fs : list Sig.
      Variable Fs_ok : forall f : Sig, In f Fs.

      Lemma fin_monotone_succ :
        forallb (fun f => bQpstrong_monotone (trsIntQ pi f)) Fs = true ->
        AWFMInterpretation.monotone I succQ.

      Proof.
        intro H. apply monotone_succ. intro f. rewrite <- bpstrong_monotone_ok.
        rewrite forallb_forall in H. apply H. apply Fs_ok.
      Qed.
      
    End fin_Sig.

  End PolyIntQ.

End S.