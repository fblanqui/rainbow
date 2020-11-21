(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2011-04-06

* CPF correctness checker of full termination

*)

Set Implicit Arguments.

Require Import ATrs SN ZArith EqUtil String List ListDec ListForall
  ListUtil ZUtil LogicUtil BoolUtil VecUtil NArith RelUtil RelMidex
  AMannaNess ARedPair2 ARelation NatUtil ADP ADuplicateSymb AMorphism
  ADecomp ADPUnif ACalls cpf2color cpf color_matrix_nat
  rainbow_full_termin SemiRing2 OrdSemiRing2 Matrix2 AMatrixInt2
  AMatrixBasedInt2_Nat AVarCond cpf_util cpf2color_interpret Polynom
  MonotonePolynom PositivePolynom APolyInt poly OrdRingType2.

Section S.

  Variable arity : symbol -> nat.

  (** REMARK: Do not define [Sig] as Notation, to be able to define
     [Sig] with [filter_arity] later in the case of [Filter] with
     non-collapsing. *)

  Notation aterm := (aterm arity).
  Notation arule := (arule arity).
  Notation arules := (arules arity).
  Notation abrule := (abrule arity).
  
  Implicit Type R : arules.

  Section Full_Termination.

  (***********************************************************************)
  (** * Check that [is] is a valid termination proof for [red R]. *)

  (** Polynomial interpretion over naturals. *)

    Lemma polynomial_interpretation_nat_ok :
      forall (R R': arules) is
             (h : match polynomial_naturals arity is with
                    | Ok (bsucc_ge, bsucc_gt) =>
                      if forallb (brule bsucc_ge) R
                      then Ok (filter (brule (neg bsucc_gt)) R)
                      else Ko arules ERuleNotInLargeOrdering_poly
                    | Ko e => Ko arules e
                  end = Ok R') (wf : WF (red R')), WF (red R).
    
    Proof.
      intros R R' is h wf.
      case_eq (polynomial_naturals arity is); intros p H; rewrite H in h;
      try discr.
      destruct p as [bge bgt].
      case_eq (forallb (brule bge) R); intro H0; rewrite H0 in h;
      try discr.
      inversion h. subst R'. clear h.
      unfold polynomial_naturals in H.
      case_eq (map_rev (color_interpret_poly arity) is); intros l H1;
      rewrite H1 in H; try discr.

      (*COQ: case_eq (forallb (fun x : {H : symbol & poly (arity H)} =>
       let (x0, p) := x in bcoef_pos p && forallb (fun x0 : nat_lt
       (arity f) => is_pos (coef (mxi (prf x0)) p)) (mk_nat_lts (arity
       f))) l) does not work! *)

      gen H.
      set (b := forallb (fun x : {f : symbol & poly (arity f)} =>
      let (f, p) := x in bcoef_pos p) l && forallb (fun x : {f : symbol
       & poly (arity f)} => let (f, p) := x in forallb (fun x0 : nat_lt
      (arity f) => is_pos (coef (mxi (prf x0)) p)) (mk_nat_lts (arity f))) l).
      case_eq b; intros H2 H3; subst b; try discr.
      inversion H3. clear H3.
      set (trsInt := fun f: Sig arity => fun_of_pairs_list arity f l).
      cut (forall f: Sig arity, pweak_monotone (trsInt f)).
      intro trsInt_wm.

      (* Proving polynomial is weak monotone. *)

      Focus 2. intro f. apply trsInt_wm. rewrite andb_eq in H2.
      destruct H2. hyp. 

      (* Proving [WF (red R)]. *)

      rewrite andb_eq in H2. destruct H2.
      apply WF_rp_red with (bwp := poly_wrp arity l H2).

      (** A proof of [>] are closed by context: IR_context_closed. *)
      
      change (context_closed (AWFMInterpretation.IR (APolyInt_MA2.I (Sig arity)
              (TPolyInt arity l H2)) APolyInt_MA2.succ)).
      apply AWFMInterpretation.IR_context_closed.
      apply pi_monotone. simpl. intro f.
      
      (* Proving polynomial is strong monotone. *)

      apply trsInt_pw. rewrite andb_eq. split. hyp. hyp.

      (* Check that all rules [R] are included in [>=]. *)

      simpl; unfold ATrs.brule, bsucceq_ma, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite forallb_forall in H0. ded (H0 x Hx). destruct x as [t u].
      simpl in *. 
      case_eq (APolyInt_MA2.succeq'_dec (Sig arity) (TPolyInt arity l H2) t u);
        intros s Hs. auto.
      unfold ATrs.brule in H4. unfold APolyInt_MA2.succeq' in s.
      rewrite bcoef_pos_ok in H4. contradiction.
      
      (* Remove all rules [R] are included in [>]. *)
      
      apply WF_incl with (S := red (filter (ATrs.brule (neg bgt))R)).
      unfold inclusion. intros t u H7. redtac. unfold red.
      exists l0. exists r. exists c. exists s. intuition.
      apply filter_In. apply filter_In in lr. intuition.
      unfold ATrs.brule, neg. unfold ATrs.brule, neg in H7. simpl in *.
      unfold bsucc_ma, bool_of_rel in H7. simpl in *.
      destruct (APolyInt_MA2.succ'_dec) in H7. discr.
      unfold APolyInt_MA2.succ' in n.
      rewrite <- bcoef_pos_ok in n. apply eq_true_not_negb in n.
      subst bgt. apply n. hyp.
    Qed.

    (***********************************************************************)
    (** Polynomial interpretation over rational numbers common proof. *)

    Require Import NewPolynom2 NewPositivePolynom2 NewAPolyInt2
            NewMonotonePolynom2 OrdRingType2 QArith_base poly_rat.

    Lemma polynomial_interpretation_comm_rat_ok:
      forall (R R': arules) del is
             (h: match polynomial_rationals arity is del with
                   | Ok (bsucc_ge, bsucc_gt) =>
                     if forallb (brule bsucc_ge) R
                     then Ok (filter (brule (neg bsucc_gt)) R)
                     else Ko arules ERuleNotInLargeOrdering_poly
                   | Ko e => Ko arules e
                 end = Ok R') (wf : WF (red R')), WF (red R).

    Proof.
      intros R R' del is h wf.
      case_eq (polynomial_rationals arity is del);
        intros p H1; rewrite H1 in h; try discr.
      destruct p as [bge bgt].
      case_eq (forallb (brule bge) R); intro H2; rewrite H2 in h; try discr.
      unfold polynomial_rationals in H1.
      case_eq (map_rev (color_interpret_polyQ arity) is); intros l H3;
      rewrite H3 in H1; try discr.
      gen H1.
      set (b:=  forallb
                  (fun x : {f : symbol & Qpoly (arity f)} =>
                     let (f, p) := x in bcoef_not_neg p) l &&
                  forallb
                  (fun x : {f : symbol & Qpoly (arity f)} =>
                     let (f, p) := x in
                     forallb
                       (fun x0 : nat_lt (arity f) => QbgtA (Qcoef (Qmxi (prf x0)) p) 0)
                       (mk_nat_lts (arity f))) l).
      case_eq b; intros H4 H5; subst b; try discr.
      inversion H5. clear H5.
      set (trsInt:=fun f : symbol => fun_of_pairs_list_q arity f l).
      cut (forall f: Sig arity, Qpweak_monotone (trsInt f)).
      intro trsInt_wm.
      
      (* Proving polynomial is weak monotone. *)

      Focus 2. intro f. apply trsInt_wm. rewrite andb_eq in H4.
      destruct H4. hyp. rewrite andb_eq in H4. destruct H4.

      (* Proving [WF (red R)]. *)

      apply WF_rp_red with (bwp := poly_wrpQ arity l H del).

      (* A proof of [>] are closed by context: IR_context_closed. *)
      
      change (context_closed (AWFMInterpretation.IR (APolyInt_MAQ2.I (Sig arity)
              (TPolyIntQ arity l H)) APolyInt_MAQ2.succQ)).
      apply AWFMInterpretation.IR_context_closed.
      apply pi_monotone. simpl. intro f.
      
      (* Proving polynomial is strong monotone. *)

      apply trsInt_pw. rewrite andb_eq. intuition.

      (* Check that all rules [R] are included in [>=]. *)

      simpl; unfold brule, bsucceq_ma, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite forallb_forall in H2. ded (H2 x Hx).
      destruct x as [t u]. simpl in *.
      case_eq (APolyInt_MAQ2.succeq'_dec (Sig arity) (TPolyIntQ arity l H) t u);
        intros s Hs. auto.
      unfold brule in H0. unfold APolyInt_MAQ2.succeq' in s.
      rewrite bcoef_not_neg_ok in H0. contradiction.
      
      (* Remove all rules [R] are included in [>]. *)

      apply WF_incl with (S := red (filter (ATrs.brule (neg bgt))R)).
      unfold inclusion. intros t u H7. redtac. unfold red.
      exists l0. exists r. exists c. exists s. intuition.
      apply filter_In. apply filter_In in lr. intuition.
      unfold brule, neg. unfold brule, neg in H7. simpl in *.
      unfold bsucc_ma, bool_of_rel in H7. simpl in *.
      destruct (APolyInt_MAQ2.succ'_dec) in H7. discr.
      unfold APolyInt_MAQ2.succ' in n.
      rewrite <- bcoef_not_neg_ok in n. apply eq_true_not_negb in n.
      subst bgt. apply n. inversion h. subst R'. clear h.
      hyp.
    Qed.
    
    (***********************************************************************)
    (** Polynomial interpretation over rational numbers. *)

    Lemma polynomial_interpretation_rat_ok :
      forall n (R R': arules) is
             (h:  match type_poly_rationals arity n is with
                    | Ok (bsucc_ge, bsucc_gt) =>
                      if forallb (brule bsucc_ge) R
                      then Ok (filter (brule (neg bsucc_gt)) R)
                      else Ko arules ERuleNotInLargeOrdering_poly
                    | Ko e => Ko arules e
                  end = Ok R') (wf : WF (red R')), WF (red R).

    Proof.
      intros n R R' is h wf.
      unfold type_poly_rationals in h.
      destruct n; simpl in h; try discr.
      
      (** In the case where coefficient are in domain of natural
    numbers. Convert it to rational numbers by divide to 1. *)

      set (del:=inject_Z i). fold del in h.
      apply polynomial_interpretation_comm_rat_ok with (R':=R')(del:=del)(is:=is).
      hyp. hyp.
      
      (** In the case where coefficient are in domain of natural
       numbers. *)
      
      set (t := (Qmake i p)). fold t in h.
      apply polynomial_interpretation_comm_rat_ok with (R':=R')(del:=t)(is:=is).
      hyp. hyp.
    Qed.

    (***********************************************************************)
    (** Matrix interpretation over natural numbers. *)

    Lemma matrix_interpretation_nat_ok :
      forall (R R': arules)(d:dimension) is
             (h : matrix_interpretation R is Domain_naturals
             (Pos.to_nat d) = Ok R') (wf : WF (red R')), WF (red R).
    
    Proof.
      intros R R' d is h wf.
      unfold matrix_interpretation in h.
      destruct Domain_naturals; simpl in h; try discr.
      case_eq (type_matrix_naturals arity is (Pos.to_nat d));
        intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt].
      case_eq (forallb (ATrs.brule bge) R); intro H0;
      rewrite H0 in h; try discr. inversion h. subst R'. clear h.
      unfold type_matrix_naturals in H. 
      case_eq (map_rev (color_interpret_matrix arity (Pos.to_nat d)) is);
        intros l H1; rewrite H1 in H; try discr.
      gen H. 
      set (b := forallb (fun x : {f : symbol & matrixInt matrix (Pos.to_nat d)
          (arity f)} => let (f, mi) := x in bVforall (fun m : matrix
          (Pos.to_nat d) (Pos.to_nat d) => bgt_nat (get_elem m (dim_pos
          (Pos.to_nat d)) (dim_pos (Pos.to_nat d))) 0) (args mi)) l).
      case_eq b; intros H2 H3; subst b; try discr. inversion H3.
      clear H3.

      (* Proving [WF(red R)]. *)

      apply WF_rp_red with (bwp := matrix_wrp arity l).

      (* A proof of [>] are closed by context: IR_context_closed. *)
      
      change (context_closed (AWFMInterpretation.IR (AMatrixInt2.I
             (TMatrixInt arity l))(succ(dim:=(Pos.to_nat d))))).
      apply AWFMInterpretation.IR_context_closed. 

      (* Proving [>] is monotone. *)

      apply monotone_succ. simpl. intro f.
      apply trsInt_nat_mon. hyp.
      
      (* Check that rules [R] is included in [>=]. *)
      
      simpl; unfold ATrs.brule, bsucceq_ma, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite forallb_forall in H0. ded (H0 x Hx).
      destruct x as [t u]. simpl in *. 
      unfold bsucceq_ma, bool_of_rel; simpl.
      case_eq (AMatrixInt2.succeq'_dec (TMatrixInt arity l) t u);
        intros ss Hs; auto. unfold ATrs.brule in H3.
      unfold term_ge, term_ord, mint_ge in ss.
      eapply bmint_ge_ok in H3.
      unfold mint_ge in H3. contradiction.
      
      (* Remove all rules [>] in [R]. *)
      
      apply WF_incl with (S := red (filter (ATrs.brule (neg bgt)) R)).
      unfold inclusion. intros t u H7. redtac. unfold red.
      exists l0. exists r. exists c. exists s. intuition.
      apply filter_In. apply filter_In in lr. intuition.
      unfold ATrs.brule, neg. unfold ATrs.brule, neg in H4. simpl in *.
      unfold bsucc_ma, bool_of_rel in H4.
      destruct AMonAlg2.succ'_dec in H4; try discr.
      simpl in *. unfold Matrix_MonoAlgType, matAlg, AMatrixInt2.succ',
                  AMatrixInt2.term_gt, term_gt, term_gt, term_ord in n; simpl in *;
                  auto. unfold mint_gt in n.
      rewrite <- bmint_gt_ok in n. apply eq_true_not_negb in n.
      subst bgt. apply n. hyp.
    Qed.

    (************************************************************************)
    (** Check that [is] is a valid termination proof for [red R]. *)
    
    Lemma redPair_interpretation_ok :
      forall (R R': arules) t is,
        redPair_interpretation R t is = Ok R' -> WF (red R') -> WF (red R).
    
    Proof.
      intros R R' t is h wf. destruct t as [d |de]; simpl in h;
                             try discr. unfold polynomial_interpretation in h.
      destruct d; simpl in h; try discr.

      (** Polynomial interpretion over naturals. *)
      
      apply polynomial_interpretation_nat_ok with (R':=R')(is:=is).
      apply h. apply wf.
      
      (** Polynomial interpretation over rational numbers.*)

      apply polynomial_interpretation_rat_ok with (n:=n)(R':=R')(is:=is).
      apply h. apply wf.

      (** Matrix interpretation over natural numbers. *)
      
      unfold type_matrixInterpretation in h.
      destruct de; try discr.
      apply matrix_interpretation_nat_ok with (R':=R') (d:=d) (is:=is).
      apply h. apply wf.
    Qed.

    (************************************************************************)
    (** Check that [l][o] are valid termination proof for [red R]. *)

    (** Assume variable [bb] in rpo2. *)

    Variable bb: nat.

    Require Import Coccinelle2 ordered_set rpo2 cpf2color_rpo ARedPair2
            cpf2color_argfilter AProj AFilterPerm.

    (** Correctness proof of RPO without argument filtering method *)

    Lemma rpo_without_af_ok :
      forall (R R': arules) l
             (h:match pathOrder_term arity bb l with
                  | Ok (bsucc_ge, bsucc_gt) =>
                    if forallb (brule bsucc_ge) R
                    then Ok (List.filter (brule (neg bsucc_gt)) R)
                    else Ko arules ENotpathOrder
                  | Ko e => Ko arules e
                end = Ok R') (wf: WF (red R')), WF (red R).
    
    Proof.
      intros R R' l h wf.
      case_eq (pathOrder_term arity bb l);
        intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt]; try discr.
      case_eq (forallb (brule bge) R); intro H1; rewrite H1 in h; try discr.
      inversion h. subst R'. clear h.    
      unfold pathOrder_term in H. gen H.

      (* FIXME?: change the condition of boolean function. *)
      set (b:=  forallb
                  (fun f : Sig arity =>
                     forallb (fun g : Sig arity => bprec_eq_status_symb l f g)
                             (list_sig l)) (list_sig l)).
      case_eq b; intros H2 H3; subst b; try discr.
      inversion H3. clear H3.
      
      (* REMARK: use [WF_rp_red2] where assume [>] is closed by context.
     If use [WF_rp_red] then prove [>] is closed by context by the
     Lemma [cc_succ_rpo] below. *)

      apply ARedPair2.WF_rp_red2 with (bwp:=Coccinelle2.bwrp_rpo bb (P arity l bb)).

      (* A proof of [>] are closed by context. *)
      
      (*apply cc_succ_rpo.*)

      (* Check that all rules [R] are included in [>=] *)
      
      simpl; unfold brule, bsucceq_rpo.
      rewrite forallb_forall. intros x Hx.
      subst bge.
      rewrite forallb_forall in H1.
      ded (H1 x Hx). destruct x as [t u].
      simpl in *.
      unfold brule in H0. hyp.

      (* Remove all rules [R] are included in [>]. *)
      
      apply WF_incl with (S:= red (List.filter (brule (neg bgt))R)).
      unfold inclusion. intros u v H3. redtac. unfold red.
      exists l0. exists r. exists c. exists s. intuition.
      apply filter_In. apply filter_In in lr. intuition.
      unfold brule, neg. unfold brule, neg in H3. simpl in *.
      unfold bsucc_rpo in H3. simpl in *.
      subst bgt. hyp. hyp.
    Qed.
    
    (***********************************************************************)
    (** Correctness proof of RPO with argument filtering method. *)

    Lemma rpo_with_af_ok :
      forall (R R': arules) a l
             (h: match pathOrder_term_rpo_af arity bb l a with
                   | Ok (bsucc_ge, bsucc_gt) =>
                     if forallb (brule bsucc_ge) R
                     then Ok (List.filter (brule (neg bsucc_gt)) R)
                     else Ko arules ENotpathOrder_AF
                   | Ko e => Ko arules e
                 end = Ok R') (wf: WF (red R')), WF (red R).

    Proof.   
      intros R R' args l h wf.
      case_eq (pathOrder_term_rpo_af arity bb l args);
        intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt]; try discr.
      case_eq (forallb (brule bge) R); intro H1; rewrite H1 in h; try discr.
      inversion h. subst R'. clear h.

      unfold pathOrder_term_rpo_af in H.
      destruct args; try discr.
      destruct p; try discr.
      destruct p; try discr.
      
      (** Argument filtering method. *)
      
      case_eq (is_col_noncol t); intro H2; rewrite H2 in H; try discr.
      set (ls:= (s, a, t):: args). fold ls in H.
      case_eq (pathOrder_rpo_proj_filter arity bb l ls);
        intros p H3; rewrite H3 in H; try discr.
      inversion H. subst p. clear H.
      unfold pathOrder_rpo_proj_filter in H3.
      gen H3.

      (* Remark: do not test two conditions: non-duplication; and
      permutations. *)

      set (b:=  forallb
                  (fun f : Sig arity =>
                     forallb (fun g : Sig arity => bprec_eq_status_symb l f g)
                             (list_sig l)) (list_sig l)).
      case_eq b; intros; subst b; try discr.
      inversion H0. clear H0.
    
    (*
    (* REMARK: use [WF_rp_red], then need to 
     - prove [context_closed succ] for Perm.  *)

    apply ARedPair2.WF_rp_red with (bwp:= @ARedPair2.bwrp_perm2 (Sig arity)
      (color_Perm ls arity)
      (@ARedPair2.bwrp_proj (Sig (@ASignature.arity (color_Sig_perm ls arity)))
        (@color_Proj ls (@ASignature.arity (color_Sig_perm ls arity)))
        (Coccinelle2.bwrp_rpo bb (P (@ASignature.arity (color_Sig_perm ls arity)) l bb)))).
    
    (* Proving [>] is closed by context in Perm, then need to prove 2 conditions:
     - arguments non-duplication 
     - if all filters are permutations. *)

    apply filter_strong_cont_closed.
    do 2 rewrite andb_eq in H. do 2 destruct H.
    (* Verifying arguments are non-duplication. *)
    simpl. unfold color_build_pi. 
    rewrite <- bnon_dup_ok. apply H4.
    (* Verifying if arguments are permutations. *)
    do 2 rewrite andb_eq in H. do 2 destruct H.
    simpl. unfold color_build_pi. rewrite <- bpermut_ok.
    apply H0.
    (* Proving [>] is closed by context by Proj.
     Then prove : [>] is reflexive relation. *)
    apply proj_cont_closed.
    Focus 2.
    (* Proving [>] is closed by context in [rpo]. *)
    apply cc_succ_rpo. *)
      
      (* Use [WF_rp_red2] where assume [>] is closed by context in the
      record type. Then do not need to prove [>] is closed by context.
      But need to prove [>] in rpo is a reflexive relation. *)

      apply ARedPair2.WF_rp_red2 with (bwp:= @ARedPair2.bwrp_perm (Sig arity)
      (color_Perm ls arity)
      (@ARedPair2.bwrp_proj (Sig (@ASignature.arity (color_Sig_perm ls arity)))
        (@color_Proj ls (@ASignature.arity (color_Sig_perm ls arity)))
        (Coccinelle2.bwrp_rpo bb (P (@ASignature.arity (color_Sig_perm ls arity)) l bb)))).

      (* Check that all rules [R] are included in [>=] *)   

      simpl; unfold brule, bsucceq.
      rewrite forallb_forall. intros x Hx.
      subst bge. clear H3.
      rewrite forallb_forall in H1.
      ded (H1 x Hx). destruct x as [u v].
      simpl in *.
      unfold brule, color_proj, color_filter in H0.
      simpl in *.
      unfold bsucceq_rpo. unfold rpo_eval in H0. simpl in *. 
      unfold empty_rpo_infos in H0. apply H0.

      (* Remove all rules [R] are included in [>] *)

      apply WF_incl with (S := red (List.filter (brule (neg bgt)) R)).
      unfold inclusion. intros u v H4. redtac. unfold red.
      exists l0. exists r. exists c. exists s0. intuition.
      apply filter_In. apply filter_In in lr. intuition.
      unfold brule, neg. unfold brule, neg in H4. simpl in *.
      unfold bsucc_rpo in H4. simpl in *.
      subst bgt. apply H4. apply wf.
    Qed.
    
    (***********************************************************************)
    (** Correctness proof of path ordering: RPO, RPO + AF. *)

    Lemma pathOrdering_ok :
      forall (R R': arules) l o,
        pathOrder bb R l o = Ok R' -> WF (red R') -> WF (red R).
    
    Proof.
      intros R R' l o h wf.
      unfold pathOrder in h.
      destruct o; try discr.

      (** RPO with argument filtering method. *)

      apply rpo_with_af_ok with (R':=R')(a:=a) (l:=l).
      apply h. apply wf.
      
      (** RPO without argument filtering method. *)
      
      apply rpo_without_af_ok with (R':=R')(l:=l).
      hyp. hyp.
    Qed.

  End Full_Termination.

  (***********************************************************************)
  (** * Check that [is] is a valid termination proof for [red_mod R]. *)
  
  Section Rel_Termination.

    (***********************************************************************)
    (** Relative Termination: Polynomial interpretation over natural numbers. *)

    Lemma rel_poly_naturals_ok :
      forall (R D D': arules) is
             (h:  match polynomial_naturals arity is with
                    | Ok (bsucc_ge, bsucc_gt) =>
                      if forallb (brule bsucc_ge) R && forallb (brule bsucc_ge) D
                      then Ok (List.filter (brule (neg bsucc_gt)) D)
                      else Ko arules ERuleNotInLargeOrdering_poly
                    | Ko e => Ko arules e
                  end = Ok D')(wf: WF (red_mod R D')), WF (red_mod R D).
    
    Proof.
      intros R D D' is h wf.
      case_eq (polynomial_naturals arity is);
        intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt].
      case_eq (forallb (brule bge) R && forallb (brule bge) D);
        intros H0; rewrite H0 in h; try discr.
      inversion h. subst D'. clear h.
      unfold polynomial_naturals in H.
      case_eq (map_rev (color_interpret_poly arity) is);
        intros l H1; rewrite H1 in H; try discr.
      gen H. set (b := forallb (fun x : {f : symbol & poly (arity f)} =>
      let (f, p) := x in bcoef_pos p) l  &&
       forallb
         (fun x : {f : symbol & poly (arity f)} =>
          let (f, p) := x in
          forallb (fun x0 : nat_lt (arity f) => is_pos (coef (mxi (prf x0)) p))
            (mk_nat_lts (arity f))) l).
      case_eq b; intros H2 H3; subst b; try discr.
      inversion H3. clear H3.
      set (trsInt := (fun f: (Sig arity) => fun_of_pairs_list arity f l)).
      cut (forall f: (Sig arity), pweak_monotone (trsInt f)).
      intros trsInt_wm. Focus 2.

      (* Polynomial weak is monotone. *)

      intro f. apply poly.trsInt_wm. rewrite andb_eq in H2. destruct H2. hyp.

      (** Proving wellfound of [red_mod]. *)

      rewrite andb_eq in H2. destruct H2.
      apply WF_rp_red_mod with (bwp := poly_wrp arity l H2).

      (** Relation [>] is closed by context. *)

      change (context_closed (AWFMInterpretation.IR (APolyInt_MA2.I (Sig arity)
        (TPolyInt arity l H2)) APolyInt_MA2.succ)).
      apply AWFMInterpretation.IR_context_closed.
      apply APolyInt.pi_monotone. simpl. intro f.
      
      (** Polynomial strong is monotone. *)

      apply poly.trsInt_pw. rewrite andb_eq. split. hyp. hyp.

      (** All relation [>=] are including in rules [R]. *)
      
      simpl. unfold brule, bsucceq_ma, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      rewrite forallb_forall in H0. ded (H0 x Hx).
      destruct x as [t u]. simpl in *.
      case_eq (APolyInt_MA2.succeq'_dec (Sig arity) (TPolyInt arity l H2) t u);
        intros s Hs. auto. unfold brule in H5.
      unfold APolyInt_MA2.succeq' in s. rewrite bcoef_pos_ok in H5.
      contradiction.

      (** All relation [>=] are including in rule [dp R = D]. *)
      
      simpl. unfold brule, bsucceq_ma, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      rewrite forallb_forall in H4. ded (H4 x Hx).
      destruct x as [t u]. simpl in *.
      case_eq (APolyInt_MA2.succeq'_dec (Sig arity) (TPolyInt arity l H2) t u);
        intros s Hs. auto. unfold brule in H5.
      unfold APolyInt_MA2.succeq' in s. rewrite bcoef_pos_ok in H5.
      contradiction.

      (* TODO *)

    Admitted.

    (***********************************************************************)
    (** Polynomial interpretation over rational numbers. *)
    (* FIXME: add R'? WF (red_mod R' D') -> WF (red_mod R D) *)

    Lemma rel_poly_rationals_common_ok :
      forall del (R D D': arules) is
             (h : match polynomial_rationals arity is del with
             | Ok (bsucc_ge, bsucc_gt) =>
               if forallb (brule bsucc_ge) R && forallb (brule bsucc_ge) D
               then Ok (List.filter (brule (neg bsucc_gt)) D)
               else Ko arules ERuleNotInLargeOrdering_poly
             | Ko e => Ko arules e
              end = Ok D')(wf : WF (red_mod R D')), WF (red_mod R D).
      
    Proof.
      intros del R D D' is h wf.
      case_eq (polynomial_rationals arity is del);
        intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt].
      case_eq (forallb (brule bge) R && forallb (brule bge) D);
        intros H0; rewrite H0 in h; try discr.
      inversion h. subst D'. clear h.
      unfold polynomial_rationals in H.
      case_eq (map_rev (color_interpret_polyQ arity) is);
        intros l H1; rewrite H1 in H; try discr.
      gen H. set (b:= forallb (fun x : {f : symbol & Qpoly (arity f)} =>
      let (f, p) := x in bcoef_not_neg p) l &&
      forallb (fun x : {f : symbol & Qpoly (arity f)} =>
      let (f, p) := x in
      forallb(fun x0 : nat_lt (arity f) =>
      OrdRingType2.QbgtA (Qcoef (Qmxi (prf x0)) p) 0)
      (mk_nat_lts (arity f))) l).
      case_eq b; intros H2 H3; subst b; try discr.
      inversion H3. clear H3.
      set (trsInt := (fun f: symbol => fun_of_pairs_list_q arity f l)).
      cut (forall f: symbol, Qpweak_monotone (trsInt f)).
      intros trsInt_wm. Focus 2.

      (** Polynomial weak is monotone. *)
      
      intro f. apply poly_rat.trsInt_wm. rewrite andb_eq in H2.
      destruct H2. hyp.
      
      (** Proving [WF (red_mod R D)]. *)

      rewrite andb_eq in H2. destruct H2.
      apply WF_rp_red_mod with (bwp:= poly_wrpQ arity l H2 del).

      (** Proving the relation [>] is close by context. *)

      change (context_closed (AWFMInterpretation.IR (APolyInt_MAQ2.I (Sig arity)
      (TPolyIntQ arity l H2)) APolyInt_MAQ2.succQ)).
      apply AWFMInterpretation.IR_context_closed.
      apply NewAPolyInt2.pi_monotone. simpl. intro f.
      apply poly_rat.trsInt_pw. rewrite andb_eq. split. hyp. hyp.

      (** Proving the relation [>=] are in rules [R]. *)

      simpl. unfold brule, bsucceq_ma, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      rewrite forallb_forall in H0. ded (H0 x Hx).
      destruct x as [t u]. simpl in *.
      case_eq (APolyInt_MAQ2.succeq'_dec (Sig arity) (TPolyIntQ arity l H2) t u);
        intros s Hs. auto.
      unfold brule in H5. unfold APolyInt_MAQ2.succeq' in s.
      rewrite bcoef_not_neg_ok in H5. contradiction.

      (** Proving the relation [>=] are in rules [D]. *)
      
      simpl. unfold brule, bsucceq_ma, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      rewrite forallb_forall in H4. ded (H4 x Hx).
      destruct x as [t u]. simpl in *.
      case_eq (APolyInt_MAQ2.succeq'_dec (Sig arity) (TPolyIntQ arity l H2) t u);
        intros s Hs. auto. unfold brule in H5.
      unfold APolyInt_MAQ2.succeq' in s. rewrite bcoef_not_neg_ok in H5.
      contradiction.

      (** Proving [red_mod] is well founded when remove all relation
      [>] in [R] and [D]. *)

      apply WF_incl with (S := red_mod (List.filter (brule (neg bgt)) R)
                                       (List.filter (brule (neg bgt)) D)).
     
      (* TODO *)      

    Admitted.

    (***********************************************************************)
    (** Polynomial interpretation over rational numbers. *)
    (* FIXME: add R'? WF (red_mod R' D') -> WF (red_mod R D) *)

    Lemma rel_poly_rationals_ok:
      forall (R D D': arules) is n
             (h:  match type_poly_rationals arity n is with
                    | Ok (bsucc_ge, bsucc_gt) =>
                      if forallb (brule bsucc_ge) R && forallb (brule bsucc_ge) D
                      then Ok (List.filter (brule (neg bsucc_gt)) D)
                      else Ko arules ERuleNotInLargeOrdering_poly
                    | Ko e => Ko arules e
                  end = Ok D')(wf: WF (red_mod R D')), WF (red_mod R D).
    
    Proof.
      intros R D D' is n h wf.
      unfold type_poly_rationals in h.
      destruct n; simpl in h; try discr.
      set (del:= inject_Z i).
      fold del in h.

      (** In the case of rationals -> natural numbers, where it convert a
       natural number to rational number by divide by 1. *)
      
      apply rel_poly_rationals_common_ok with (del:=del)(D':=D')(is:=is).
      hyp. hyp.
      
      (** In the case of rationals -> rational numbers. *)
      
      set (t:= Qmake i p). fold t in h.
      apply rel_poly_rationals_common_ok with (del:=t)(D':=D')(is:=is).
      hyp. hyp.
      Qed.

    (***********************************************************************)
    (** Polynomial interpretation over natural numbers and rational
     numbers. *)
    (* FIXME: add R'? WF (red_mod R' D') -> WF (red_mod R D) *)

    Lemma rel_polynomial_interpretation_ok: forall (R D D': arules)
      is (d:domain) (h: rel_polynomial_interpretation R D is d = Ok D')
      (wf : WF (red_mod R D')), WF (red_mod R D).

    Proof.
      intros R D D' is d h wf.
      unfold rel_polynomial_interpretation in h.
      unfold type_polynomial in h.
      destruct d; simpl in h; try discr.

      (** Domain naturals. *)

      apply rel_poly_naturals_ok with (D':=D')(is:=is).
      hyp. hyp.

      (** Domain rationals. *)
      
      apply rel_poly_rationals_ok with (D':=D')(is:=is)(n:=n).
      hyp. hyp.
    Qed.    

    (***********************************************************************)
    (** Relative termination: Matrix interpretation over natural numbers. *)

    Lemma rel_matrix_interpretation_nat_ok : forall (R D D': arules)
      (d:dimension) is (h: rel_matrix_interpretation R D is Domain_naturals
        (Pos.to_nat d) = Ok D') (wf : WF (red_mod R D')), WF (red_mod R D).

    Proof.
      intros R D D' d is h wf.
      unfold rel_matrix_interpretation in h.
      destruct Domain_naturals; simpl in h; try discr.
      case_eq (type_matrix_naturals arity is (Pos.to_nat d));
        intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt].
      case_eq (forallb (brule bge) D && forallb (brule bge) R);
        intro H0; rewrite H0 in h; try discr.
      inversion h. subst D'. clear h. unfold type_matrix_naturals in H.
      case_eq (map_rev (color_interpret_matrix arity (Pos.to_nat d)) is);
        intros l H1; rewrite H1 in H; try discr. gen H.
      set (b :=  forallb
         (fun x : {f : symbol & matrixInt matrix (Pos.to_nat d) (arity f)} =>
          let (f, mi) := x in
          bVforall
            (fun m : matrix (Pos.to_nat d) (Pos.to_nat d) =>
             bgt_nat
               (get_elem m (dim_pos (Pos.to_nat d)) (dim_pos (Pos.to_nat d)))
               0) (args mi)) l).
      case_eq b; intros H2 H3; subst b; try discr.
      inversion H3. clear H3.
      apply WF_rp_red_mod with (bwp := matrix_wrp arity l).

      (** Proving the relation [>] is closed by context. *)
      
      change (context_closed (AWFMInterpretation.IR (AMatrixInt2.I
      (TMatrixInt arity l))(AMatrixInt2.succ(dim:=(Pos.to_nat d))))).
      apply AWFMInterpretation.IR_context_closed. 
      apply AMatrixInt2.monotone_succ. simpl. intro f.
      apply trsInt_nat_mon. hyp.

      (** Proving the relation [>=] are in rules [R]. *)

       simpl; unfold ATrs.brule, bsucceq_ma, bool_of_rel; simpl.
       rewrite forallb_forall. intros x Hx. subst bge. rewrite andb_eq in H0.
       destruct H0. rewrite forallb_forall in H3. ded (H3 x Hx).
       destruct x as [t u]. simpl in *.
       unfold bsucceq_ma, bool_of_rel; simpl.
       case_eq (AMatrixInt2.succeq'_dec (TMatrixInt arity l) t u);
         intros ss Hs; auto. unfold ATrs.brule in H4.
       unfold term_ge, term_ord, mint_ge in ss.
       eapply bmint_ge_ok in H4.
       unfold mint_ge in H4. contradiction.

       (** Proving the relation [>=] are in rules [D]. *)

       unfold ATrs.brule, bsucceq, bool_of_rel; simpl.
       rewrite forallb_forall. intros x Hx. subst bge.
       rewrite andb_eq in H0. destruct H0.
       rewrite forallb_forall in H0.
       ded (H0 x Hx). destruct x as [t u]. simpl in *.
       unfold bsucceq_ma, bool_of_rel.
       case_eq (AMonAlg2.succeq'_dec (Sig arity) (Matrix_MonoAlgType arity l) t u);
         intros ss Hs; auto. unfold brule in H4.
       simpl in *.
       unfold AMatrixInt2.succeq', succeq', term_ge, term_ord, mint_ge in ss.
       apply bmint_ge_ok in H4. contradiction.

       (** Proving [WF (red_mod R D')]. *)
    
        apply WF_incl with (S := red_mod (List.filter (brule (neg bgt)) R)
                                         (List.filter (brule (neg bgt)) D)).
        unfold inclusion. intros t u H3. redtac.
        
        (* TODO *)
        (*
        unfold hd_red_mod. unfold compose. ∃ t0.
        intuition. unfold hd_red. ∃ l0. ∃ r. ∃ s.
        intuition. apply filter_In. apply filter_In in lr. intuition.
        unfold ATrs.brule, neg. unfold ATrs.brule, neg in H7. simpl in ×.
        unfold bsucc_ma, bool_of_rel in H7.
        destruct AMonAlg2.succ'_dec in H7; try discr.
        simpl in ×. unfold AMatrixInt2.succ' in n.
        unfold AMatrixInt2.term_gt, term_gt, term_ord in n.
        simpl in ×. unfold mint_gt in n.
        rewrite <- bmint_gt_ok in n. apply eq_true_not_negb in n.
        subst bgt. apply n. hyp.*)

    Admitted.

  (***********************************************************************)
  (** Relative termination *)

  Lemma rel_redPair_interpretation_ok : forall (R D D' : arules) t is,
    rel_redPair_interpretation R D t is = Ok D' -> WF (red_mod R D')
    -> WF (red_mod R D).

  Proof.
    intros R D D' t is h wf. destruct t; simpl in h; try discr.

    (** Polynomial interpretation over natural numbers and rational
    numbers. *)

    apply rel_polynomial_interpretation_ok with (D':=D')(is:=is)(d:=d).
    apply h. apply wf.

    (** Matrix interpretation over natural numbers. *)

    destruct d; simpl in h; try discr.
    apply rel_matrix_interpretation_nat_ok with (D':=D')(d:=d0)(is:=is).
    apply h. apply wf.

    (* REMARK: There is no arctic domain for relative termination. *)
  Qed.

  End Rel_Termination.

End S.

