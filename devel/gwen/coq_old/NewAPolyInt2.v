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

Require Import ATerm ABterm ListUtil ListForall VecUtil NewPositivePolynom2
  AInterpretation ZUtil NaryFunction ARelation RelUtil LogicUtil SN NewPolynom2
  NatUtil OrdRingType2 RingType2 NewMonotonePolynom2. 

Section WFOrdRing.

  Variable Sig : Signature.
  
  Notation bterm := (bterm Sig).
  
  (***********************************************************************)
  (** Definition of polynomial interpretation. *)
  
  Definition PolyInterpretation := forall f : Sig, Qpoly (arity f).

  (***********************************************************************)
  (** Polynomial associated to a bterm *)

  Section pi.
    
    Variable PI : PolyInterpretation.
    
    Fixpoint poly_of_bterm k (t : bterm k) {struct t} : Qpoly (S k) :=
      match t with
        | BVar x H => (QA1, Qmxi (gt_le_S (le_lt_n_Sm H))) :: List.nil
        | BFun f v => pcomp (PI f) (Vmap (@poly_of_bterm k) v)
      end.

    (***********************************************************************)
    (** Decide quantification over a finite set. *)

    Section forall_finite.

      Variables (A : Type) (elts : list A) (elts_ok : forall x : A, List.In x elts)
        (P : A -> Prop) (bP : A -> bool) (bP_ok : forall x, bP x = true <-> P x).
      
      Lemma bforall_fin : forallb bP elts = true <-> forall x, P x.
        
      Proof.
        rewrite forallb_forall. firstorder.
      Qed.
      
    End forall_finite.

    (***********************************************************************)
    (** Monotony properties. *)

    Definition PolyWeakMonotone := forall f : Sig, Qpweak_monotone (PI f).
    Definition PolyStrongMonotone := forall f : Sig, Qpstrong_monotone (PI f).
    
    Section fin_Sig.

      Variable Fs : list Sig.
      Variable Fs_ok : forall f : Sig, List.In f Fs.
      
      Lemma bPolyWeakMonotone :
        forallb (fun f => bQpweak_monotone (PI f)) Fs = true <-> PolyWeakMonotone.
        
      Proof.
        apply bforall_fin. hyp. intro. apply bQpweak_monotone_ok.
      Qed.

    End fin_Sig.
    
    (***********************************************************************)
    (** Assuming that, in the polynomial interpretation, all
    coefficients are non-negative, then in the polynomial of every
    bterm, all coefficients are non-negative. *)
    
    Variable PI_WM : PolyWeakMonotone.

    Section coef_not_neg.
      
      Let P := fun (k : nat) (t : bterm k) => coef_not_neg (poly_of_bterm t).
      Let Q := fun (k n : nat) (ts : vector (bterm k) n) => Vforall (@P k) ts.
      
      Lemma coef_not_neg_poly_of_bterm : forall (k : nat) (t : bterm k), P t.
        
      Proof.
        intros k t. apply (bterm_ind (@P k) (@Q k)).
        intros v Hv. unfold P. simpl. intuition. unfold QgeA. left.
        apply one_QgtA_zero.
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

    Require Import QArith.

    Notation "x >=A y" := (QgeA x y) (at level 70).
    Notation "0" := QA0.

    Notation not_neg := (fun z => z >=A 0).

    Lemma Zero_in_D : not_neg 0.
      
    Proof.
      simpl. unfold QgeA. right. refl.
    Qed.
  
    Notation D := (sig not_neg).
    Notation inj := (@exist Q not_neg _).
    Notation D0 := (inj Zero_in_D). 
    
    Implicit Arguments peval_D [n p].

    Definition Int_of_PI := mkInterpretation D0 (fun f => peval_D (PI_WM f)).

    Let I := Int_of_PI.

    (***********************************************************************)
    (** Interpretation monotony. *)

    Require Import AWFMInterpretation.

    Implicit Arguments coef_not_neg_monotone_peval_Dge [n p i j x y].

    Lemma pi_monotone_eq : monotone I QDge.
      
    Proof.
      intro f.
      apply (coef_not_neg_monotone_peval_Dge (PI_WM f)).
    Qed.
    
    Variable PI_SM : PolyStrongMonotone.

    Implicit Arguments pmonotone_imp_monotone_peval_Dgt [H].

    Lemma pi_monotone : monotone I QDgt.
      
    Proof.
      intro f.
      apply pmonotone_imp_monotone_peval_Dgt with (H:= PI_SM f).
    Qed.
    
    (***********************************************************************)
    (** Reduction ordering *)

    Let succ := IR I QDgt.

    Definition Dlt := (transp QDgt).
    
    (* Proof well founded for Dgt of type Q. *)

    Require Import Inclusion Wellfounded.

    Lemma Qlt_well_founded : well_founded Qlt.
    Proof.
    Admitted.

    Lemma well_founded_Dlt : well_founded Dlt.
      
    Proof.
      unfold Dlt. unfold transp. unfold QDgt.
      apply wf_incl with (R2:= (fun x y : D => QgtA (proj1_sig y) (proj1_sig x))).
      unfold inclusion, QgtA. intros (x, Hx) (y, Hy). simpl. intuition.
      apply wf_inverse_image. apply Qlt_well_founded.
    Qed.

    Lemma WF_DgtQ : WF QDgt.
      
    Proof. apply wf_transp_WF. apply well_founded_Dlt.
    Qed.
    
    Lemma pi_red_ord : reduction_ordering succ.
      
    Proof.
    unfold succ. apply IR_reduction_ordering. apply pi_monotone.
    apply WF_DgtQ.
    Qed.
    
    (***********************************************************************)
    (** Reduction pair *)
    
    Let succ_eq := IR I QDge.

    Lemma pi_absorb : absorbs_left succ succ_eq.
      
    Proof.
      unfold absorbs_left, inclusion. intros. do 2 destruct H.
      unfold succ_eq, succ, IR in *. intro. eapply QgeA_gtA_trans.
      apply H. apply H0.
    Qed.
    
    Definition rp := @mkReduction_pair Sig
    (*rp_succ : relation term;*)
      succ
    (*rp_succ_eq : relation term;*)
      succ_eq
    (*rp_subs : substitution_closed rp_succ;*)
      (@IR_substitution_closed _ I QDgt)
    (*rp_subs_eq : substitution_closed rp_succ_eq;*)
      (@IR_substitution_closed _ I QDge)
    (*rp_cont : context_closed rp_succ;*)
      (@IR_context_closed _ _ _ pi_monotone)
    (*rp_cont_eq : context_closed rp_succ_eq;*)
      (@IR_context_closed _ _ _ pi_monotone_eq)
    (*rp_absorb : absorb rp_succ rp_succ_eq;*)
      pi_absorb
    (*rp_succ_wf : WF rp_succ*) 
      (@IR_WF _ I _ WF_DgtQ).
    
    (***********************************************************************)
    (** Equivalence between (xint) and (vec_of_val xint) *)
    
    Let f1 (xint : valuation I) k (t : bterm k) := proj1_sig (bterm_int xint t).
    
    Let f2 (xint : valuation I) k (t : bterm k) :=
      proj1_sig (peval_D (coef_not_neg_poly_of_bterm t) (vec_of_val xint (S k))).
    
    Let P (xint : valuation I) k (t : bterm k) := f1 xint t =A= f2 xint t.
    
    Let Q (xint : valuation I) k n (ts : vector (bterm k) n) :=
      Vforall (@P xint k) ts.
    
    Lemma poly_of_bvar : forall x k (H : (x<=k)%nat),
      poly_of_bterm (BVar H) = (1, Qmxi (gt_le_S (le_lt_n_Sm H))) :: Qpzero (S k).
      
    Proof.
      intros. simpl. refl.
    Qed.
    
    Lemma peval_poly_of_bvar : forall x k (H : (x<=k)%nat) (v : vector QA (S k)),
      peval (poly_of_bterm (BVar H)) v =A= meval (Qmxi (gt_le_S (le_lt_n_Sm H))) v.
      
    Proof.
      intros x k H v. rewrite poly_of_bvar. unfold Qpzero. unfold peval at 1. 
      unfold QeqA. ring.
    Qed.
    
    Require Import BoolUtil.
    
    Lemma PI_bterm_int_eq : forall xint k (t : bterm k), P xint t.
      
    Proof.
      intros xint k t. apply (bterm_ind (@P xint k) (@Q xint k)).
      (* BVar *)
      intros v Hv. unfold P, f1, f2. simpl bterm_int. rewrite val_peval_D.
      rewrite peval_poly_of_bvar. rewrite meval_xi. rewrite Vnth_map.
      pattern (xint v) at 1.
      rewrite <- (Vnth_vec_of_val xint (gt_le_S (le_lt_n_Sm Hv))). refl.
      (* BFun *)
      intros f ts. unfold Q. intro H. unfold P, f1, f2. simpl bterm_int.
      rewrite val_peval_D. simpl. unfold P in H. rewrite peval_comp.
      rewrite Vmap_map. rewrite Vmap_map. change
      (peval (PI f) (Vmap (@f1 xint k) ts) =A= peval (PI f)
        (Vmap (@f2 xint k) ts)).
      apply peval_eqA. gen H. gen ts. generalize (arity f).
      induction ts0; simpl; intros. refl.
      rewrite andb_eq. rewrite QbeqA_ok. intuition.
      (* Vnil *)
      unfold Q, P. simpl. trivial.
      (* Vcons *)
      intros t' n' ts' H1 H2. unfold Q. simpl. intuition.
    Qed.
    
    Lemma PI_term_int_eq : forall (xint : valuation I) t k 
      (H : (maxvar t <= k)%nat),
      proj1_sig (term_int xint t)
      =A= proj1_sig (peval_D (coef_not_neg_poly_of_bterm (inject_term H))
        (vec_of_val xint (S k))).
      
    Proof.
      intros xint t k H. rewrite <- (term_int_eq_bterm_int xint H).
      generalize (PI_bterm_int_eq xint (inject_term H)). intuition.
    Qed.
    
    Implicit Arguments PI_term_int_eq [t k].
    
    (***********************************************************************)
    (** Polynomial associated to a rule *)

    Require Import ATrs.
    Require Import Max.
    
    (* rulePoly_ge x y = P_x - P_y *)

    Definition rulePoly_geQ r := 
      let mvl := maxvar (lhs r) in
        let mvr := maxvar (rhs r) in
          let m := max mvl mvr in
            padd (poly_of_bterm (inject_term (le_max_l mvl mvr)))
            (popp (poly_of_bterm (inject_term (le_max_r mvl mvr)))).
     
    (* Condition for [rulePoly_gt = P_l - P_r - del >= 0] over domain
    rational numbers. *)

    Require Import QArith_base.

    Open Scope Q_scope.

    Definition rulePoly_gtQ (del: QArith_base.Q) r :=
      let mvl := maxvar (lhs r) in
        let mvr := maxvar (rhs r) in
          let m := max mvl mvr in
            padd (rulePoly_geQ r) (popp (Qpconst (S m) del)).

    (***********************************************************************)
    (** Compatibility *)
    
    Require Import ZUtil OrdRingType2 NewPolynom2.

    Open Scope Z_scope.

    Lemma pi_compat_rule : forall r del,
      coef_not_neg (rulePoly_gtQ del r) -> succ (lhs r) (rhs r).
      
    Proof.
      intros r del H_coef_not_neg. unfold succ, IR. intro xint.
      unfold QDgt.
      set (mvl := maxvar (lhs r)). set (mvr := maxvar (rhs r)).
      unfold QgtA.
      rewrite (PI_term_int_eq xint (le_max_l mvl mvr)).
      rewrite (PI_term_int_eq xint (le_max_r mvl mvr)).
      do 2 rewrite val_peval_D.
      pose (v := (Vmap (proj1_sig (P:=not_neg))
        (vec_of_val xint (S (max mvl mvr))))). fold v.
      apply Qnot_neg_gt. 
    (* TODO *)
      (*rewrite <- (peval_const 1 v). rewrite <- peval_minus.
      unfold v. rewrite <- peval_minus. apply not_neg_peval.
      exact H_coef_not_neg.
      Qed.*)
    Admitted.

    Require Import PositivePolynom.

    (* TODO *)
    Lemma pi_compat_rule_weak : forall r,
      coef_not_neg (rulePoly_geQ r) -> succ_eq (lhs r) (rhs r).

    Proof.
      intros r H_coef_not_neg. unfold succ_eq, IR. intro xint.
      unfold QDge. 
      set (mvl := maxvar (lhs r)). set (mvr := maxvar (rhs r)).
      unfold QgeA. left. unfold QgtA.
      rewrite (PI_term_int_eq xint (le_max_l mvl mvr)).
      rewrite (PI_term_int_eq xint (le_max_r mvl mvr)). 
      do 2 rewrite NewPositivePolynom2.val_peval_D. 
      apply Qnot_neg_gt. unfold QgeA. left. unfold QgtA.
      rewrite <- peval_minus. simpl.
      (*
      apply not_neg_peval. exact H_coef_not_neg.
    Qed.*)
    Admitted.

    Require Import ACompat.

    Lemma pi_compat : forall R del,
      lforall (fun r => coef_not_neg (rulePoly_gtQ del r)) R -> compat succ R.

    Proof.
      unfold compat. intros. set (rho := mkRule l r).
      change (succ (lhs rho) (rhs rho)). apply pi_compat_rule with (del:=del).
      apply (lforall_in H H0).
    Qed.

    (***********************************************************************)
    (** termination *)

    Require Import AMannaNess.

    Lemma polyInterpretationTermination : forall R del,
      lforall (fun r => coef_not_neg (rulePoly_gtQ del r)) R -> WF (red R).

    Proof.
      intros R0 del H. apply manna_ness with (succ := succ). apply pi_red_ord.
      apply pi_compat with (del:=del). exact H.
    Qed.

  End pi.

  (***********************************************************************)
  (** Default polynomial interpretation *)

  Definition default_poly n :=
    List.map (fun x => (1, Qmxi (prf x))) (mk_nat_lts n).

  Open Local Scope nat_scope.
  
  (*
  Lemma coef_default_poly : forall n i (h : i<n), 
    Qcoef (Qmxi h) (default_poly n) =A= 1.
    
  Proof.

  Admitted. *)

  Definition default_pi (f : Sig) := default_poly (arity f).

  Lemma pweak_monotone_default : PolyWeakMonotone default_pi.

  Proof.
    intro f. unfold Qpweak_monotone, coef_not_neg, default_pi.
    rewrite lforall_eq.
    intros. destruct (in_map_elim H). destruct H0. subst. simpl.
    unfold QgeA. left.
    apply one_QgtA_zero.
  Qed.

  (*
  Lemma pstrong_monotone_default : PolyStrongMonotone default_pi.

  Proof.
    intro f. split. apply pweak_monotone_default. 
    intros. 

  Abort. *)

  (***********************************************************************)
  (** tactics *)
  
  (*REMOVE: to be removed: tactic used in an old version of Rainbow
     
     Ltac poly_int PI := solve
     [match goal with
     |- WF (red ?R) =>
     apply (polyInterpretationTermination PI R);
     vm_compute; intuition; discriminate
     end] || fail "invalid polynomial interpretation".*)
  
  Ltac PolyWeakMonotone Fs Fs_ok :=
    match goal with
      | |- PolyWeakMonotone ?PI =>
        apply (bPolyWeakMonotone PI Fs Fs_ok);
          (check_eq || fail "could not prove monotony")
    end.
  
End WFOrdRing.