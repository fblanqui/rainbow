(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Hans Zantema, 2007-04-25

* Polynomial interpretations in the setting of monotone algebras.

*)

Require Import APolyInt2 AMonAlg2 ZUtil RelUtil PositivePolynom2 ATrs
  ListForall MonotonePolynom2 LogicUtil BoolUtil Polynom2 OrdSemiRing2
  AWFMInterpretation VecUtil.

(* Define TPolyInt as Record type *)

Section S.

  Variable Sig : Signature.
  Context {OR  : OrderedRing}.
  
  Section TPolyInt.

    Record TPolyInt : Type := mkbTPolyInt {
      trsInt    : forall f: Sig, poly (arity f);
      trsInt_wm : PolyWeakMonotone trsInt }.
    
  End TPolyInt.
  
  Section PolyInt.

    Variable pi : TPolyInt.

    Import OR_Notations.

    Notation "x >>= y" := (@or_ge _ x y) (at  level 70).
    Notation not_neg   := (fun z => z >>= 0).
    Notation D         := (sig not_neg).
    Notation val       := (@proj1_sig s_typ not_neg).
    Notation vec       := (vector D). 
    Notation vals      := (@Vmap D s_typ val _).

    Definition I      := Int_of_PI (trsInt_wm pi).
    Definition succ   := Dgt.
    Definition succeq := Dge.
    
    (* MOVE *)

    Lemma refl_Dge : reflexive Dge.
    Proof.
      intros [x hs]. unfold Dge. simpl. apply or_ge_refl.
    Qed.

    (* MOVE *)

    Lemma trans_Dgt : transitive Dgt.
    Proof.
      intros [x hx] [y hy] [z hz].
      unfold Dgt. simpl. intros. 
      trans y. apply H. apply H0.
    Qed.
    
    (* MOVE *)

    Lemma trans_Dge : transitive Dge.
    Proof.
      intros [x hx] [y hy] [z hz].
      unfold Dge. simpl. intros.
      eapply or_ge_trans. apply H. apply H0.
    Qed.
    
    Definition refl_succeq  := refl_Dge.
    Definition trans_succ   := trans_Dgt.
    Definition trans_succeq := trans_Dge.
    
    Lemma monotone_succeq : monotone I succeq.
    
    Proof.
      unfold I. apply pi_monotone_eq. 
    Qed.
    
    Definition succ_wf := APolyInt2.WF_Dgt.
    
    Lemma succ_succeq_compat : absorbs_left succ succeq.
    
    Proof.
      unfold succ, succeq. intros p q pq. destruct pq as [r [pr rq]].
      unfold Dgt, Dge in *. unfold or_ge in pr.
      destruct pr.
      apply or_gt_trans with (val r); auto.
      rewrite H. apply rq.
    Qed.
    
    Definition rulePoly_gt l r := rulePoly_gt   (trsInt pi) (@mkRule Sig l r).
    Definition succ' l r       := coef_not_neg              (rulePoly_gt l r).
    Definition bsucc' l r      := bcoef_not_neg             (rulePoly_gt l r).
    
    Lemma bsucc'_ok : forall l r, bsucc' l r = true <-> succ' l r.
    
    Proof.
      intros l r. unfold bsucc', succ'. apply bcoef_not_neg_ok.
    Qed.
    
    Lemma succ'_dec : rel_dec succ'.
    
    Proof.
      intros l r. unfold succ'. eapply dec. apply bcoef_not_neg_ok.
    Defined.
    
    (* REMARK: rulePoly_gt for domain rational number taking [del] as argument *)

    Definition rulePoly_gtQ del l r := rulePoly_gtQ  (trsInt pi) del (@mkRule Sig l r).
    Definition succQ' del l r       := coef_not_neg                  (rulePoly_gtQ del l r).
    Definition bsuccQ' del l r      := bcoef_not_neg                 (rulePoly_gtQ del l r).

    Lemma bsuccQ'_ok : forall del l r, bsuccQ' del l r = true <-> succQ' del l r.

    Proof.
      intros del l r. unfold bsuccQ', succQ'. apply bcoef_not_neg_ok.
    Qed.

    Lemma succQ'_dec : forall del, rel_dec (succQ' del).

    Proof.
      intros del l r. unfold succQ'. eapply dec. apply bcoef_not_neg_ok.
    Qed.

    Definition rulePoly_ge l r := rulePoly_ge   (trsInt pi) (@mkRule Sig l r).
    Definition succeq' l r     := coef_not_neg  (rulePoly_ge l r).
    Definition bsucceq' l r    := bcoef_not_neg (rulePoly_ge l r).
    
    Lemma bsucceq'_ok : forall l r, bsucceq' l r = true <-> succeq' l r.
    
    Proof.
      intros l r. unfold bsucceq', succeq'. apply bcoef_not_neg_ok.
    Qed.
    
    Lemma succeq'_dec : rel_dec succeq'.
    
    Proof.
      intros l r. unfold succeq'. eapply dec. apply bcoef_not_neg_ok.
    Defined.
    
    Lemma succ'_sub : succ' << IR I succ.
    
    Proof.
      intros t u tu. unfold I, succ. set (r := mkRule t u).
      change t with (lhs r). change u with (rhs r).
      apply (@pi_compat_rule _ _ _ _ r). hyp.
    Qed.
    
    Lemma succQ'_sub : forall del, (succQ' del) << IR I succ.
    Proof.
      intros del t u tu. unfold I, succ. set (r := mkRule t u).
      change t with (lhs r). change u with (rhs r).
      eapply pi_compat_ruleQ. apply tu.
    Qed.
    
    Lemma succeq'_sub : succeq' << IR I succeq.
    
    Proof.
      intros t u tu. unfold I, succ. set (r := mkRule t u).
      change t with (lhs r). change u with (rhs r).
      apply (pi_compat_rule_weak _). hyp.
    Qed.
    
    (** Instance type of MonotoneAlgType. *)  

    Global Instance MonotoneAlgebra : MonotoneAlgebraType Sig.
    
    Proof.
      apply Build_MonotoneAlgebraType with
      (ma_int     := I)
      (ma_succ    := succ)
      (ma_succeq  := succeq)
      (ma_succeq' := succeq')
      (ma_succ'   := succ').
      apply refl_succeq.
      apply trans_succ.
      apply trans_succeq.
      apply monotone_succeq.
      apply succ_wf.
      apply succ_succeq_compat.
      apply succ'_sub.
      apply succeq'_sub.
      apply succ'_dec.
      apply succeq'_dec.
    Defined.

    (** Instance type of MonotoneAlgType for domain rational. *)

    Import OR_Notations.

    Variable del: s_typ.

    Global Instance MonotoneAlgebraQ : MonotoneAlgebraType Sig.
    
    Proof.
      apply Build_MonotoneAlgebraType with
      (ma_int     := I)
      (ma_succ    := succ)
      (ma_succeq  := succeq)
      (ma_succeq' := succeq')
      (ma_succ'   := succQ' del).
      apply refl_succeq.
      apply trans_succ.
      apply trans_succeq.
      apply monotone_succeq.
      apply succ_wf.
      apply succ_succeq_compat.
      apply succQ'_sub.
      apply succeq'_sub.
      apply succQ'_dec.
      apply succeq'_dec.
    Defined.
    
    Section ExtendedMonotoneAlgebra.
      
      Lemma monotone_succ : PolyStrongMonotone (trsInt pi) ->
                            AWFMInterpretation.monotone I succ.
      
      Proof.
        unfold I. apply pi_monotone.
      Qed.
      
    End ExtendedMonotoneAlgebra.
    
    Require Import List.
    
    Section fin_Sig.
      
      Variable Fs : list Sig.
      Variable Fs_ok : forall f : Sig, In f Fs.
      
      Lemma fin_monotone_succ :
        forallb (fun f => bpstrong_monotone ((trsInt pi) f)) Fs = true ->
        AWFMInterpretation.monotone I succ.
      
      Proof.
        intro H. apply monotone_succ. intro f. rewrite <- bpstrong_monotone_ok.
        rewrite forallb_forall in H. apply H. apply Fs_ok.
      Qed.
      
    End fin_Sig.

 End PolyInt.

End S.