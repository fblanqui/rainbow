(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-20
- Frederic Blanqui, 2004-12-13
- Adam Koprowski, 2007-04-26 (modular removal of rules) 
                  2008-05-27 (weakly monotone polynomials)

Proof of the termination criterion based on polynomial interpretations

- Kim Quyen Ly, 2013-08-26

Proof of the termination criterion based on polynomial interpretations
over domain rational numbers.

*)

Set Implicit Arguments.

Require Import ATerm ABterm ListUtil ListForall VecUtil PositivePolynom2
  AInterpretation ZUtil NaryFunction ARelation RelUtil LogicUtil SN Polynom2
  NatUtil OrdSemiRing2 MonotonePolynom2. 

Section S.

  Context {OR : OrderedRing}. Import OR_Notations.

  Variable Sig : Signature.
  
  Notation bterm := (bterm Sig).
  
  (***********************************************************************)
  (** Definition of polynomial interpretation. *)
  
  Definition PolyInterpretation := forall f : Sig, poly (arity f).

  (***********************************************************************)
  (** Polynomial associated to a bterm *)

  Section pi.
    
    Variable PI : PolyInterpretation.

    Fixpoint poly_of_bterm k (t : bterm k) {struct t} : poly (S k) :=
      match t with
        | BVar x H => (1, mxi (gt_le_S (le_lt_n_Sm H))) :: List.nil
        | BFun f v => pcomp (PI f) (Vmap (@poly_of_bterm k) v)
      end.

    (***********************************************************************)
    (** Monotony properties. *)

    Definition PolyWeakMonotone   := forall f : Sig, pweak_monotone (PI f).
    Definition PolyStrongMonotone := forall f : Sig, pstrong_monotone (PI f).
        
    Section fin_Sig.

      Variables (Fs : list Sig) (Fs_ok : forall f : Sig, List.In f Fs).

      Lemma fin_PolyWeakMonotone :
        forallb (fun f => bpweak_monotone (PI f)) Fs = true -> PolyWeakMonotone.

      Proof.
        rewrite forallb_forall. intros H f. rewrite <- bpweak_monotone_ok.
        apply H. apply Fs_ok.
      Qed.

    End fin_Sig.

    (***********************************************************************)
    (** Assuming that, in the polynomial interpretation, all
    coefficients are non-negative, then in the polynomial of every
    bterm, all coefficients are non-negative. *)
    
    Variable (PI_WM : PolyWeakMonotone) (PI_SM : PolyStrongMonotone).

    Section coef_not_neg.
      
      Let P := fun (k : nat)   (t  : bterm k)            => coef_not_neg (poly_of_bterm t).
      Let Q := fun (k n : nat) (ts : vector (bterm k) n) => Vforall (@P k) ts.
      
      Lemma bterm_poly_not_neg : forall (k : nat) (t : bterm k), P t.
        
      Proof.
        intros k t. apply (bterm_ind (@P k) (@Q k)).
        intros v Hv. unfold P. simpl. intuition. unfold or_ge. 
        left. apply or_one_gt_zero.
        unfold Q. intros f ts H. unfold P. simpl.
        apply coef_not_neg_pcomp.
        apply (PI_WM f).
        unfold P in H. apply Vforall_map_intro. auto.
        unfold Q. simpl. trivial.
        intros t' n' s' H1. unfold Q. intro H2. simpl. split; assumption.
      Qed.
      
    End coef_not_neg.
    
    (***********************************************************************)
    (** Interpretation in the set D of non-negative elements. *)
    
    Notation "x >>= y" := (@or_ge _ x y) (at  level 70).
    Notation not_neg := (fun z => z >>= 0).

    Lemma Zero_in_D : not_neg 0.
      
    Proof.
      simpl. unfold or_ge. right. refl.
    Qed.
  
    Notation D := (sig not_neg).
    Notation inj := (@exist s_typ not_neg _).
    Notation D0 := (inj Zero_in_D). 
    Notation val := (@proj1_sig s_typ not_neg).
    Notation vec := (vector D). 
    Notation vals := (@Vmap D s_typ val _).

    Implicit Arguments peval_D [n p].

    Definition Int_of_PI := mkInterpretation D0 (fun f => peval_D _ (PI_WM f)).

    Let I := Int_of_PI.

    (***********************************************************************)
    (** Interpretation monotony. *)

    Require Import AWFMInterpretation.

    Lemma pi_monotone : monotone I Dgt.
      
    Proof.
      intro f. apply (pmonotone_imp_monotone_peval_Dgt (proj1 (PI_SM f)) (PI_SM f)).
    Qed.

    Lemma pi_monotone_eq : monotone I Dge.
      
    Proof.
      intro f.
      apply (coef_not_neg_monotone_peval_Dge _ (PI_WM f)).
    Qed.
    
    (***********************************************************************)
    (** Reduction ordering *)

    Let succ := IR I Dgt.

    (* MOVE *)

    Require Import Inclusion Wellfounded.
    
    (* TODO *)
    Lemma WF_Dgt : WF Dgt.
    Proof.
      apply wf_transp_WF.      
      unfold transp, Dgt.
     
    Admitted.

    Lemma pi_red_ord : reduction_ordering succ.
      
    Proof.
    unfold succ. apply IR_reduction_ordering. apply pi_monotone.
    apply WF_Dgt.
    Qed.

    (***********************************************************************)
    (** Reduction pair *)
    
    Let succ_eq := IR I Dge.

    Lemma pi_absorb : absorbs_left succ succ_eq.
      
    Proof.
      unfold absorbs_left, inclusion. intros. do 2 destruct H.
      unfold succ_eq, succ, IR, Dge, Dgt, transp, Dle, Dlt in *.
      intro. eapply ge_gt_trans.
      apply H. apply H0.
    Qed.
    
    Definition rp := @mkReduction_pair Sig
    (*rp_succ : relation term;*)
      succ
    (*rp_succ_eq : relation term;*)
      succ_eq
    (*rp_subs : substitution_closed rp_succ;*)
      (@IR_substitution_closed _ I Dgt)
    (*rp_subs_eq : substitution_closed rp_succ_eq;*)
      (@IR_substitution_closed _ I Dge)
    (*rp_cont : context_closed rp_succ;*)
      (@IR_context_closed _ _ _ pi_monotone)
    (*rp_cont_eq : context_closed rp_succ_eq;*)
      (@IR_context_closed _ _ _ pi_monotone_eq)
    (*rp_absorb : absorb rp_succ rp_succ_eq;*)
      pi_absorb
    (*rp_succ_wf : WF rp_succ*) 
      (@IR_WF _ I _ WF_Dgt).
    
    (***********************************************************************)
    (** Equivalence between (xint) and (vec_of_val xint) *)
    
    Let f1 (xint : valuation I) k (t : bterm k) := proj1_sig (bterm_int xint t).
    
    Let f2 (xint : valuation I) k (t : bterm k) :=
      proj1_sig (peval_D _ (bterm_poly_not_neg t) (vec_of_val xint (S k))).
    
    Let P (xint : valuation I) k (t : bterm k) := f1 xint t == f2 xint t.
    
    Let Q (xint : valuation I) k n (ts : vector (bterm k) n) :=
      Vforall (@P xint k) ts.
    
    Lemma termpoly_v_eq_1 : forall x k (H : (x<=k)%nat),
      poly_of_bterm (BVar H) = (1, mxi (gt_le_S (le_lt_n_Sm H))) :: pzero (S k).
      
    Proof.
      intros. simpl. refl.
    Qed.
    
    Add Ring R: r_th.

    Lemma termpoly_v_eq_2 : forall x k (H : (x<=k)%nat) (v : vector s_typ (S k)),
      peval (poly_of_bterm (BVar H)) v == meval (mxi (gt_le_S (le_lt_n_Sm H))) v.

    Proof.
      intros x k H v. rewrite termpoly_v_eq_1. unfold pzero. unfold peval at 1. 
      ring.
    Qed.

    (* MOVE *)

    Require Import BoolUtil.
    
    Context {R: Ring}.

    Lemma meval_eq : forall n  (m : monom n) (v1 v2 : vector s_typ n),
                       beq_vec bool_s_eq v1 v2 = true -> meval m v1 == meval m v2.

    Proof.
      induction n; simpl; intros. refl. gen H. VSntac v1. VSntac v2. simpl.
      rewrite andb_eq. rewrite bool_s_eq_ok. intuition. simpl in *.
      rewrite (IHn _ _ _ H4). (*rewrite H3. refl.
    Qed.*)
    Admitted.
    
    Implicit Arguments meval_eq [n m v1 v2].
    
    Lemma peval_eq : forall n (p : poly n) (v1 v2 : vector s_typ n),
                       beq_vec bool_s_eq v1 v2 = true -> peval p v1 == peval p v2.
    
    Proof.
      induction p; simpl; intros. refl. destruct a. rewrite (IHp _ _ H).
      rewrite (meval_eq H). refl.
    Qed.

    Lemma PI_bterm_int_eq : forall xint k (t : bterm k), P xint t.
      
    Proof.
      intros xint k t. apply (bterm_ind (@P xint k) (@Q xint k)).
      (* BVar *)
      intros v Hv. unfold P, f1, f2. simpl bterm_int.
      rewrite val_peval_D.
      rewrite termpoly_v_eq_2.
      rewrite meval_xi. rewrite Vnth_map.
      pattern (xint v) at 1.
      rewrite <- (Vnth_vec_of_val xint (gt_le_S (le_lt_n_Sm Hv))).
      refl.
      (* BFun *)
      intros f ts. unfold Q. intro H. unfold P, f1, f2. simpl bterm_int.
      rewrite val_peval_D. simpl. unfold P in H.
      rewrite peval_comp. 
      rewrite Vmap_map. rewrite Vmap_map. change
      (peval (PI f) (Vmap (@f1 xint k) ts) == peval (PI f)
        (Vmap (@f2 xint k) ts)).
      apply peval_eq. gen H. gen ts. generalize (arity f).
      induction ts0; simpl; intros. refl.
      rewrite andb_eq. rewrite bool_s_eq_ok. intuition.
      (* Vnil *)
      unfold Q, P. simpl. trivial.
      (* Vcons *)
      intros t' n' ts' H1 H2. unfold Q. simpl. intuition.
    Qed.
    
    Lemma PI_term_int_eq : forall (xint : valuation I) t k 
      (H : (maxvar t <= k)%nat),
      proj1_sig (term_int xint t)
      == proj1_sig (peval_D _ (bterm_poly_not_neg (inject_term H))
        (vec_of_val xint (S k))).
      
    Proof.
      intros xint t k H. rewrite <- (term_int_eq_bterm_int xint H).
      generalize (PI_bterm_int_eq xint (inject_term H)). intuition.
    Qed.
    
    Implicit Arguments PI_term_int_eq [t k].
    
    (***********************************************************************)
    (** Polynomial associated to a rule *)
    
    Bind Scope poly_scope with poly.

    Open Scope poly_scope.

    Infix "+" := padd : poly_scope.
    Notation "- y" := (popp y) : poly_scope.
    Notation "x - y" := (x + (- y)) : poly_scope.
    Notation "'0'" := (pconst _ 0) : poly_scope.
    Notation "'1'" := (pconst _ 1) : poly_scope.

    Require Import Max ATrs.

    Hint Unfold maxvar_le.
    Hint Resolve le_max_l le_max_r.
    
    (* FIXME *)
    Program Definition rulePoly_ge rule := 
      let l := lhs rule in let r := rhs rule in
      let m := max (maxvar l) (maxvar r) in
      poly_of_bterm (@inject_term _ m l _) - poly_of_bterm (@inject_term _ m r _).

    (*Definition rulePoly_ge r := 
      let mvl := maxvar (lhs r) in
        let mvr := maxvar (rhs r) in
        let m := max mvl mvr in
        padd (poly_of_bterm (inject_term (le_max_l mvl mvr)))
             (popp (poly_of_bterm (inject_term (le_max_r mvl mvr)))). *)

    (* P_x - P_y - 1 *)

    Definition rulePoly_gt rule := rulePoly_ge rule - 1.

    (* Remark: Define a rulePoly_gt of domain rational: P_x - P_y - del *)

    Definition rulePoly_gtQ del rule := rulePoly_ge rule - (pconst _ del).

    (***********************************************************************)
    (** Compatibility *)
    
    (* MOVE inside OrderedRing *)
    (* TODO *)

    Close Scope poly_scope.

    Lemma not_neg_gt : forall x y, y - x - 1 >>= 0 -> y >> x.
    Proof.
      intros. unfold or_ge in H. destruct H. 
    Admitted.

    Lemma not_neg_ge : forall x y, y - x >>= 0 -> y >>= x.
    Proof.
      intros. 
    Admitted.
      
    Lemma pi_compat_rule : forall r,
      coef_not_neg (rulePoly_gt r) -> succ (lhs r) (rhs r).
      
    Proof.
      intros r H_coef_pos. unfold succ, IR.
      intro xint. unfold Dgt, Dlt, transp.
      set (mvl := maxvar (lhs r)). set (mvr := maxvar (rhs r)).
      rewrite (PI_term_int_eq xint (le_max_l mvl mvr)).
      rewrite (PI_term_int_eq xint (le_max_r mvl mvr)).
      do 2 rewrite val_peval_D.
      pose (v := (Vmap (proj1_sig (P:=not_neg))
                       (vec_of_val xint (S (max mvl mvr))))). fold v.
      apply not_neg_gt. 
      rewrite <- (peval_const 1 v). rewrite <- peval_minus.
      unfold v. rewrite <- peval_minus. apply not_neg_peval.
      exact H_coef_pos.
    Qed.

    (* Proving pi_compat_rule for rational number *)
    Lemma pi_compat_ruleQ : forall r del ,
      coef_not_neg (rulePoly_gtQ del r) -> succ (lhs r) (rhs r).
      
    Proof.
      intros r del H_coef_pos. unfold succ, IR.
      intro xint. unfold Dgt, Dlt, transp.
      set (mvl := maxvar (lhs r)). set (mvr := maxvar (rhs r)).
      rewrite (PI_term_int_eq xint (le_max_l mvl mvr)).
      rewrite (PI_term_int_eq xint (le_max_r mvl mvr)).
      do 2 rewrite val_peval_D.
      pose (v := (Vmap (proj1_sig (P:=not_neg))
                       (vec_of_val xint (S (max mvl mvr))))). fold v.
      (* TODO : having a different proof about not_neg_gt with a del argument *)
      (*apply not_neg_gt. 
      rewrite <- (peval_const del v). rewrite <- peval_minus.
      unfold v. rewrite <- peval_minus. apply not_neg_peval.
      exact H_coef_pos.
    Qed.*)
    Admitted.

    Lemma pi_compat_rule_weak : forall r,
      coef_not_neg (rulePoly_ge r) -> succ_eq (lhs r) (rhs r).

    Proof.
      intros r H_coef_pos. unfold succ_eq, IR. intro xint.
      unfold Dge, Dle, transp. 
      set (mvl := maxvar (lhs r)). set (mvr := maxvar (rhs r)).
      rewrite (PI_term_int_eq xint (le_max_l mvl mvr)).
      rewrite (PI_term_int_eq xint (le_max_r mvl mvr)). 
      do 2 rewrite val_peval_D. apply not_neg_ge. rewrite <- peval_minus.
      apply not_neg_peval. exact H_coef_pos.
    Qed.

    Require Import ACompat.

    Lemma pi_compat : forall R,
      lforall (fun r => coef_not_neg (rulePoly_gt r)) R -> compat succ R.

    Proof.
      unfold compat. intros. set (rho := mkRule l r).
      change (succ (lhs rho) (rhs rho)). apply pi_compat_rule.
      apply (lforall_in H H0).
    Qed.

    (***********************************************************************)
    (** termination *)

    Require Import AMannaNess.

    Lemma polyInterpretationTermination : forall R,
      lforall (fun r => coef_not_neg (rulePoly_gt r)) R -> WF (red R).

    Proof.
      intros R0 H. apply manna_ness with (succ := succ). apply pi_red_ord.
      apply pi_compat. exact H.
    Qed.

  End pi.

  (***********************************************************************)
  (** Default polynomial interpretation *)

  Definition default_poly n :=
    List.map (fun x => (sr_1, mxi (prf x))) (mk_nat_lts n).

  Definition default_pi (f : Sig) := default_poly (arity f).

  Lemma pweak_monotone_default : PolyWeakMonotone default_pi.

  Proof.
    intro f. unfold pweak_monotone, coef_not_neg, default_pi.
    rewrite lforall_eq.
    intros. destruct (in_map_elim H). destruct H0. subst. simpl.
    unfold or_ge. left.
    apply or_one_gt_zero.
  Qed.

  Ltac PolyWeakMonotone Fs Fs_ok :=
    match goal with
      | |- PolyWeakMonotone ?PI =>
        apply (PolyWeakMonotone PI Fs Fs_ok);
          (check_eq || fail "could not prove monotony")
    end.

  (***********************************************************************)
  (** Some properties of default polynomial that are not define in CoLoR. *)

  Definition poly_cast n m (Heq : n = m) (p: poly n) : poly m.
  rewrite <- Heq; auto.
  Defined.
    
  (* Check positive coefficient in default polynomial interpretation. *)

  Lemma pcoef_default_check : forall n: nat, coef_not_neg (default_poly n).
  Proof.
    intro n. unfold default_poly, coef_not_neg.
    rewrite lforall_eq. intros x H. destruct (in_map_elim H).
    destruct H0. subst. simpl. unfold or_ge.
    left. apply or_one_gt_zero.
  Qed.

  (* Proving polynomial strong monotone. *)

  Lemma default_poly_mxi_1 n i (H: i < n) : List.In (1, mxi H) (default_poly n).
  Proof.
    apply in_map_iff. exists {|val := i; prf := H|}. intuition.
    assert (List.In (mk_nat_lt H) (mk_nat_lts n)).
    apply mk_nat_lts_complete.
    auto.
  Qed.

End S.