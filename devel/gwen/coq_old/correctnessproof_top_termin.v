(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2011-04-06

* CPF correctness checker top termination - Dependency pair proof

*)

Set Implicit Arguments.

Require Import ATrs SN ZArith EqUtil String List ListDec ListForall
  ListUtil ZUtil LogicUtil BoolUtil VecUtil NArith RelUtil RelMidex
  AMannaNess ARedPair2 ARelation NatUtil ADP ADuplicateSymb AMorphism
  ADecomp ADPUnif ACalls cpf2color cpf color_matrix_nat
  rainbow_top_termin SemiRing2 OrdSemiRing2 Matrix2 AMatrixInt2
  AMatrixBasedInt2_Nat AVarCond cpf_util cpf2color_interpret
  QArith_base NewPositivePolynom2 NewPolynom2 NewMonotonePolynom2
  APolyInt_MAQ2 NewAPolyInt2 poly_rat.

(***********************************************************************)
(** * Check that [is] is a valid termination proof for dependency pair
proof [hd_red_mod R D]. *)

Section Top_Termination.

  (***********************************************************************)
  (** Correctness proof of polynomial interpretation over different
  domain. *)
  
  Section poly.

    (** Polynomial interpretation over domain rational numbers with
     common proof. *)

    Lemma poly_rationals_dp_common_ok: forall a del (R D D': arules a) is
      (H:match polynomial_rationals_dp a is del with
           | Ok (bsucc_ge, bsucc_gt) =>
             if forallb (brule bsucc_ge) D && forallb (brule bsucc_ge) R
               then Ok (filter (brule (neg bsucc_gt)) D)
               else Ko (list (ATrs.rule (Sig a))) ERuleNotInLargeOrdering_dp
           | Ko e => Ko (list (ATrs.rule (Sig a))) e
         end = Ok D')(wf : WF (hd_red_mod R D')), WF (hd_red_mod R D).
      
    Proof.
      intros a del R D D' is h wf.
      case_eq (polynomial_rationals_dp a is del);
        intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt].
      case_eq (forallb (brule bge) D && forallb (brule bge) R);
        intros H0; rewrite H0 in h; try discr.
      inversion h. subst D'. clear h.
      unfold polynomial_rationals_dp in H.
      case_eq (map_rev (color_interpret_polyQ a) is);
        intros l H1; rewrite H1 in H; try discr.
      gen H.
      set (b:= forallb (fun x : {f : symbol & Qpoly (a f)} =>
        let (f, p) := x in bcoef_not_neg p) l).
      case_eq b; intros H2 H3; subst b; try discr.
      inversion H3. clear H3.
      set (trsInt := (fun f: (Sig a) => fun_of_pairs_list_q a f l)).
      cut (forall f: (Sig a), Qpweak_monotone (trsInt f)).
      intros trsInt_wm. Focus 2.
      intro f. apply trsInt_wm. hyp.
      apply WF_wp_hd_red_mod with (bwp := poly_wrpQ a l H2 del).
      
      (** Check that all rules [R] are included in [>=]. *)
      
      simpl. unfold brule, bsucceq_ma, bool_of_rel; simpl. 
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      rewrite forallb_forall in H3. ded (H3 x Hx).
      destruct x as [t u]. simpl in *.
      case_eq (succeq'_dec (Sig a) (TPolyIntQ a l H2) t u);
        intros s Hs. auto. unfold abrule, ATrs.brule in H4.
      unfold succeq' in s. rewrite bcoef_not_neg_ok in H4.
      contradiction.
      
      (** Check that all rules [D = dp R] are included in [>=]. *)
      
      simpl. unfold brule, bsucceq_ma, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      rewrite forallb_forall in H0. ded (H0 x Hx).
      destruct x as [t u]. simpl in *.
      case_eq (succeq'_dec (Sig a) (TPolyIntQ a l H2) t u);
        intros s Hs. auto. unfold abrule, brule in H4.
      unfold succeq' in s. rewrite bcoef_not_neg_ok in H4.
      contradiction.
      
      (** Remove all rules [D] that are included in [>]. *)

      apply WF_incl with (S := hd_red_mod R (filter (abrule (neg bgt)) D)).
      unfold inclusion. intros t u H3. redtac.
      Focus 2. hyp. unfold hd_red_mod. unfold compose. exists t0. 
      split. hyp.
      unfold hd_red. exists l0. exists r. exists s. intuition.
      apply filter_In. apply filter_In in lr. intuition. unfold brule, neg.
      unfold brule, neg in H7. simpl in *. unfold bsucc_ma, bool_of_rel in H7.
      simpl in *. destruct succ'_dec in H7.
      discr. unfold succ' in n. rewrite <- bcoef_not_neg_ok in n.
      apply eq_true_not_negb in n. subst bgt. apply n.
    Qed.
  
    (***********************************************************************)
    (** Polynomial interpretation over domain rational numbers. *)

    Lemma poly_rationals_dp_ok: forall a n (R D D': arules a) is
      (h: match type_poly_rationals_dp a n is with
            | Ok (bsucc_ge, bsucc_gt) =>
              if forallb (brule bsucc_ge) D && forallb (brule bsucc_ge) R
                then Ok (filter (brule (neg bsucc_gt)) D)
                else Ko (list (ATrs.rule (Sig a))) ERuleNotInLargeOrdering_dp
            | Ko e => Ko (list (ATrs.rule (Sig a))) e
          end = Ok D') (wf : WF (hd_red_mod R D')), WF (hd_red_mod R D).

    Proof.
      intros a n R D D' is h wf.
      unfold type_poly_rationals_dp in h.
      destruct n; simpl in h; try discr.
      
      (** In the case of rationals -> natural numbers, where it convert a
       natural number to rational number by divide by 1. *)
      
      set (del:= inject_Z i).
      fold del in h.
      apply poly_rationals_dp_common_ok with (is:=is)(del:=del)(D':=D').
      hyp. hyp.

      (** In the case of rationals -> rational numbers. *)

      set (t := Qmake i p). fold t in h.
      apply poly_rationals_dp_common_ok with (is:=is)(del:=t)(D':=D').
      hyp. hyp.
    Qed.

    (***********************************************************************)
    (** Polynomial interpretation over natural numbers. *)

    Require Import Polynom PositivePolynom APolyInt_MA2 poly APolyInt
      MonotonePolynom.

    Lemma poly_naturals_dp_ok : forall a (R D D': arules a) is
      (h:  match polynomial_naturals_dp a is with
             | Ok (bsucc_ge, bsucc_gt) =>
               if forallb (brule bsucc_ge) D && forallb (brule bsucc_ge) R
                 then Ok (filter (brule (neg bsucc_gt)) D)
                 else Ko (list (ATrs.rule (Sig a))) ERuleNotInLargeOrdering_dp
             | Ko e => Ko (list (ATrs.rule (Sig a))) e
           end = Ok D') (wf: WF (hd_red_mod R D')), WF (hd_red_mod R D).

    Proof.
      intros a R D D' is h wf.
      case_eq (polynomial_naturals_dp a is);
        intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt].
      case_eq (forallb (ATrs.brule bge) D && forallb (ATrs.brule bge) R);
        intros H0; rewrite H0 in h; try discr.
      inversion h. subst D'. clear h.
      unfold polynomial_naturals_dp in H.
      case_eq (map_rev (color_interpret_poly a) is);
        intros l H1; rewrite H1 in H; try discr.
      gen H. set (b := forallb (fun x : {f : symbol & poly (a f)} =>
      let (f, p) := x in bcoef_pos p) l).
      case_eq b; intros H2 H3; subst b; try discr.
      inversion H3. clear H3.
      set (trsInt := (fun f: (Sig a) => fun_of_pairs_list a f l)).
      cut (forall f: (Sig a), pweak_monotone (trsInt f)).
      intros trsInt_wm. Focus 2.
      intro f. apply trsInt_wm. hyp.
      apply WF_wp_hd_red_mod with (bwp := poly_wrp a l H2).
      
      (** Check that all rules [R] are included in [>=]. *)
      
      simpl. unfold ATrs.brule, bsucceq_ma, bool_of_rel; simpl. 
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0. 
      rewrite forallb_forall in H3. ded (H3 x Hx).
      destruct x as [t u]. simpl in *.
      case_eq (APolyInt_MA2.succeq'_dec (Sig a) (TPolyInt a l H2) t u);
        intros s Hs. auto. unfold abrule, ATrs.brule in H4.
      unfold APolyInt_MA2.succeq' in s. rewrite bcoef_pos_ok in H4.
      contradiction.
      
      (** Check that all rules [D = dp R] are included in [>=]. *)
      
      simpl. unfold ATrs.brule, bsucceq_ma, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge. rewrite andb_eq in H0.
      destruct H0. rewrite forallb_forall in H0. ded (H0 x Hx).
      destruct x as [t u]. simpl in *.
      case_eq (APolyInt_MA2.succeq'_dec (Sig a) (TPolyInt a l H2) t u);
        intros s Hs. auto. unfold abrule, ATrs.brule in H4.
      unfold APolyInt_MA2.succeq' in s. rewrite bcoef_pos_ok in H4.
      contradiction.
      
      (** Remove all rules [D] that are included in [>]. *)

      apply WF_incl with (S := hd_red_mod R (filter (abrule (neg bgt)) D)).
      unfold inclusion. intros t u H3. redtac.
      Focus 2. hyp. unfold hd_red_mod. unfold compose. exists t0.
      split. hyp.
      unfold hd_red. exists l0. exists r. exists s. intuition.
      apply filter_In. apply filter_In in lr. intuition. unfold ATrs.brule, neg.
      unfold ATrs.brule, neg in H7. simpl in *. unfold bsucc_ma, bool_of_rel in H7.
      simpl in *. destruct (APolyInt_MA2.succ'_dec) in H7.
      discr. unfold APolyInt_MA2.succ' in n. rewrite <- bcoef_pos_ok in n.
      apply eq_true_not_negb in n. subst bgt. apply n.
    Qed.

    (***********************************************************************)
    (** Polynomial interpretation over natural numbers and rational
     numbers. *)

    Lemma polynomial_interpretation_dp_ok: forall a (R D D': arules a)
      is (d:domain) (h: polynomial_interpretation_dp R D is d = Ok
        D') (wf : WF (hd_red_mod R D')), WF (hd_red_mod R D).
      
    Proof.
      intros a R D D' is d h wf.
      unfold polynomial_interpretation_dp in h. destruct d; simpl in h;
      try discr.

      (** Polynomial interpretation over natural numbers. *)

      apply poly_naturals_dp_ok with (D':=D')(is:=is).
      apply h. apply wf.

      (** Polynomial interpretation over rational numbers. *)
      
      apply poly_rationals_dp_ok with (n:=n)(D':=D')(is:=is).
      apply h. apply wf.
    Qed.

  End poly.

  (***********************************************************************)
  (** Matrix interpretation over different domains. *)

  Section matrix.
  
    (** Matrix interpretation over natural numbers. *)

    Lemma matrix_interpretation_nat_dp_ok : forall a (R D D': arules a)
      (d:dimension) is (h: matrix_interpretation_dp R D is Domain_naturals
        (Pos.to_nat d) = Ok D') (wf : WF (hd_red_mod R D')), WF
      (hd_red_mod R D).

    Proof.
      intros a R D D' d is h wf.
      unfold matrix_interpretation_dp in h.
      destruct Domain_naturals; simpl in h; try discr.
      case_eq (type_matrix_naturals_dp a is (Pos.to_nat d));
        intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt].
      case_eq (forallb (abrule bge) D && forallb (abrule bge) R);
        intro H0; rewrite H0 in h; try discr.
      inversion h. subst D'. clear h. unfold type_matrix_naturals_dp in H.
      case_eq (map_rev (color_interpret_matrix a (Pos.to_nat d)) is);
        intros l H1; rewrite H1 in H; try discr. gen H.
      set (b := forallb (fun x : {f : symbol &
        matrixInt matrix (Pos.to_nat d) (a f)} =>
      let (f, mi) := x in bVforall (fun m : matrix (Pos.to_nat
        d) (Pos.to_nat d) => bge_nat (get_elem m (dim_pos (Pos.to_nat
          d)) (dim_pos (Pos.to_nat d))) 0) (args mi)) l). case_eq b;
      intros H2 H3; subst b; try discr.
      inversion H3. clear H3.
      apply WF_wp_hd_red_mod with (bwp := matrix_wrp a l).
          
      (** Check that rules [R] is included in [>=]. *)
          
      unfold ATrs.brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0. 
      rewrite forallb_forall in H3.
      ded (H3 x Hx). destruct x as [t u]. simpl in *.
      unfold bsucceq_ma, bool_of_rel.
      case_eq (AMonAlg2.succeq'_dec (Sig a) (Matrix_MonoAlgType a l) t u);
        intros ss Hs; auto. unfold abrule, ATrs.brule in H4. simpl in *.
      unfold AMatrixInt2.succeq', succeq', term_ge, term_ord, mint_ge in ss.
      apply bmint_ge_ok in H4. contradiction.
      
      (** Check that rules [D = dp R] is included in [>=]. *)
      
      unfold ATrs.brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      rewrite forallb_forall in H0.
      ded (H0 x Hx). destruct x as [t u]. simpl in *.
      unfold bsucceq_ma, bool_of_rel.
      case_eq (AMonAlg2.succeq'_dec (Sig a) (Matrix_MonoAlgType a l) t u);
        intros ss Hs; auto. unfold abrule, ATrs.brule in H4.
      simpl in *. unfold AMatrixInt2.succeq', succeq',
      term_ge, term_ord, mint_ge in ss.
      apply bmint_ge_ok in H4. contradiction.
      
      (** Remove all rules [>] in [D]. *)
      
      apply WF_incl with (S := hd_red_mod R (filter (abrule (neg bgt)) D)).
      unfold inclusion. intros t u H3. redtac.
      unfold hd_red_mod. unfold compose. exists t0. split. hyp.
      unfold hd_red. exists l0. exists r. exists s.
      intuition. apply filter_In. apply filter_In in lr. intuition.
      unfold ATrs.brule, neg. unfold ATrs.brule, neg in H7. simpl in *.
      unfold bsucc_ma, bool_of_rel in H7.
      destruct AMonAlg2.succ'_dec in H7; try discr.
      simpl in *. unfold AMatrixInt2.succ' in n.
      unfold AMatrixInt2.term_gt, term_gt, term_ord in n.
      simpl in *. unfold mint_gt in n.
      rewrite <- bmint_gt_ok in n. apply eq_true_not_negb in n.
      subst bgt. apply n. hyp.
    Qed.

    (***********************************************************************)
    (** Matrix interpretation over arctic natural numbers. *)
    
    Require Import color_matrix_arctic_nat AMatrixBasedInt2_ArcticNat.
    
    (* FIXME: is there something wrong with the [map] function? *)

    Lemma matrix_interpretation_arcnat_dp_ok : forall a (R D D': arules
      a) (d:dimension) is (h: matrix_arc_interpretation_dp R D is
        Domain_naturals (Pos.to_nat d) = Ok D') (wf : WF (hd_red_mod R D')),
      WF (hd_red_mod R D).
      
    Proof.
      intros a R D D' d is h wf.
      unfold matrix_arc_interpretation_dp in h.
      destruct Domain_naturals; simpl in h; try discr.
      case_eq (type_matrix_arc_naturals_dp a is (Pos.to_nat d)); intros p H;
        rewrite H in h; try discr.
      destruct p as [bge bgt].
      case_eq (forallb (abrule bge) D && forallb (abrule bge) R);
        intro H0; rewrite H0 in h; try discr.
      inversion h. subst D'. clear h.
      unfold type_matrix_arc_naturals_dp in H.
      case_eq (map_rev (color_matrix_arc_interpret a (Pos.to_nat d)) is);
        intros l H1; rewrite H1 in H; try discr. gen H. 
      set (b := forallb (fun x : {f : symbol & matrixInt_arcnat
        matrix_arcnat (Pos.to_nat d) (a f)} => let (f, mi) := x in
      bVexists (fun m : matrix_arcnat (Pos.to_nat d) (Pos.to_nat
        d) => is_finite (get_elem_arcnat m (dim_pos (Pos.to_nat d))
          (dim_pos (Pos.to_nat d)))) (args_arcnat mi) || is_finite
      (Vnth (const_arcnat mi) (dim_pos (Pos.to_nat d)))) l).
      case_eq b; intros H2 H3; subst b; try discr. inversion H3.
      clear H3.
      apply WF_wp_hd_red_mod with (bwp := matrix_arcnat_wrp a l).
      
      (** Check that rules [R] is included in [>=]. *)
      
      unfold ATrs.brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      rewrite forallb_forall in H3.
      ded (H3 x Hx). destruct x as [t u]. simpl in *.
      unfold bsucceq_ma, bool_of_rel.   
      case_eq (AMonAlg2.succeq'_dec (Sig a)(MatrixArcnat_MonoAlgType a l) t u);
      intros ss Hs; auto.
      unfold abrule, ATrs.brule in H4. 
      simpl in *. unfold AArcticInt2.succeq', succeq_arcnat', 
      term_ge_arcnat, term_ord_arcnat, mint_ge_arcnat in ss.
      apply bmint_arc_ge_ok in H4. contradiction.
      
      (** Check that rules [D = dp R] is included in [>=]. *)
      
      unfold ATrs.brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      rewrite forallb_forall in H0.
      ded (H0 x Hx). destruct x as [t u]. simpl in *.
      unfold bsucceq_ma, bool_of_rel.
      case_eq (AMonAlg2.succeq'_dec (Sig a)
        (MatrixArcnat_MonoAlgType a l) t u);
      intros ss Hs; auto. unfold abrule, ATrs.brule in H4.
      simpl in *. unfold AArcticInt2.succeq', succeq_arcnat',
      term_ge_arcnat, term_ord_arcnat, mint_ge_arcnat in ss.
      apply bmint_arc_ge_ok in H4. contradiction.
      
      (** Remove all rules [>] in [D]. *)

      apply WF_incl with (S := hd_red_mod R (filter (abrule (neg bgt)) D)).
      unfold inclusion. intros t u H3. redtac.
      unfold hd_red_mod. unfold compose. exists t0. split. hyp.
      unfold hd_red. exists l0. exists r. exists s. intuition.
      apply filter_In. apply filter_In in lr. intuition.
      unfold ATrs.brule, neg. unfold ATrs.brule, neg in H7. simpl in *.
      unfold bsucc_ma, bool_of_rel in H7.
      destruct AMonAlg2.succ'_dec in H7; try discr.
      simpl in *. unfold AArcticInt2.succ' in n.
      unfold AArcticBasedInt2.succ', AArcticBasedInt2.term_gt,
        term_ord_arcnat in n. 
      simpl in *. unfold AArcticBasedInt2.mint_gt in n.
      rewrite <- bmint_arc_gt_ok in n. apply eq_true_not_negb in n.
      subst bgt. apply n. hyp.
    Qed.
    
    (***********************************************************************)
    (* REMARK: Relative matrix interpretation over arctic natural
    numbers. There is no arctic domains (natural and integer) in matrix
    interpretation of relative relation.*)

    (** REMARK: By Lemma 2.17 in Adam's thesis, Every arctic linear f
    over A is monotone with respect to [>=]. *)

   (***********************************************************************)
    (** Matrix interpretation over arctic integer numbers (below-zero). *)

    Require Import color_matrix_arctic_below_zero AMatrixBasedInt2_ArcticBZ.
    
    Lemma matrix_interpretation_arcbz_dp_ok : forall a (R D D': arules
      a) (d: dimension) is (h: matrix_arcbz_interpretation_dp R D is
        Domain_integers (Pos.to_nat d) = Ok D') (wf: WF (hd_red_mod R
          D')), WF (hd_red_mod R D).
      
    Proof.
      intros a R D D' d is h wf.
      unfold matrix_arcbz_interpretation_dp in h.
      destruct Domain_integers; simpl in h; try discr.
      case_eq (type_matrix_arcbz_integers_dp a is (Pos.to_nat d));
        intros p H;
          rewrite H in h; try discr.
      destruct p as [bge bgt].
      case_eq (forallb (abrule bge) D && forallb (abrule bge) R);
        intro H0; rewrite H0 in h; try discr.
      inversion h. subst D'. clear h.
      unfold type_matrix_arcbz_integers_dp in H.
      case_eq (map_rev (color_matrix_arcbz_interpret a (Pos.to_nat d)) is);
        intros l H1; rewrite H1 in H; try discr. gen H.  
      set (b := forallb (fun x : {f : symbol & matrixInt_arcbz
        matrix_arcbz (Pos.to_nat d) (a f)} => let (f, mi) := x in
      is_above_zero (Vnth (const_arcbz mi) (dim_pos (Pos.to_nat d))))
      l). case_eq b; intros H2 H3; subst b; try discr. inversion H3.
      clear H3.
      apply WF_wp_hd_red_mod with (bwp := matrix_arcbz_wrp a l).
      
      (** Check that rules [R] is included in [>=]. *)
      
      unfold ATrs.brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      rewrite forallb_forall in H3.
      ded (H3 x Hx). destruct x as [t u]. simpl in *.
      unfold bsucceq_ma, bool_of_rel.   
      case_eq (AMonAlg2.succeq'_dec (Sig a)
        (MatrixArcbz_MonoAlgType a l) t u);
      intros ss Hs; auto.
      unfold abrule, ATrs.brule in H4. 
      simpl in *. unfold succeq', succeq_arcbz',
      term_ge_arcbz, term_ord_arcbz, mint_ge_arcbz in ss.
      apply bmint_arc_bz_ge_ok in H4. contradiction.
      
      (** Check that rules [D = dp R] is included in [>=]. *)
      
      unfold ATrs.brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      rewrite forallb_forall in H0.
      ded (H0 x Hx). destruct x as [t u]. simpl in *.
      unfold bsucceq_ma, bool_of_rel.
      case_eq (AMonAlg2.succeq'_dec (Sig a)
        (MatrixArcbz_MonoAlgType a l) t u);
      intros ss Hs; auto. unfold abrule, ATrs.brule in H4.
      simpl in *. unfold succeq', succeq_arcbz',
      term_ge_arcbz, term_ord_arcbz, mint_ge_arcbz in ss.
      apply bmint_arc_bz_ge_ok in H4. contradiction.
      
      (** Remove all rules [>] in [D]. *)
      
      apply WF_incl with (S := hd_red_mod R (filter (abrule (neg bgt)) D)).
      unfold inclusion. intros t u H3. redtac.
      unfold hd_red_mod. unfold compose. exists t0. split. hyp.
      unfold hd_red. exists l0. exists r. exists s.
      intuition. apply filter_In. apply filter_In in lr. intuition.
      unfold ATrs.brule, neg. unfold ATrs.brule, neg in H7. simpl in *.
      unfold bsucc_ma, bool_of_rel in H7.
      destruct AMonAlg2.succ'_dec in H7; try discr.
      simpl in *. unfold AArcticBZInt2.succ' in n.
      unfold AArcticBasedInt2.succ'bz, AArcticBasedInt2.term_gtbz,
        term_ord_arcbz in n. 
      simpl in *. unfold AArcticBasedInt2.mint_gtbz in n.
      rewrite <- bmint_arc_bz_gt_ok in n. apply eq_true_not_negb in n.
      subst bgt. apply n. hyp.
    Qed.

    (* REMARK: There is no arctic domains (natural and integer) in
        matrix interpretation of relative relation. *)

  End matrix.

  (***********************************************************************)
  (** Correctness proof of reduction pair interpretation in the case of
  top termination problems. *)
    
  Lemma redPair_interpretation_dp_ok : forall a (R D D' : arules a) t is,
    redPair_interpretation_dp R D t is = Ok D' -> WF (hd_red_mod R D')
    -> WF (hd_red_mod R D).
    
  Proof.
    intros a R D D' t is h wf. destruct t; simpl in h; try discr.
    
    (** Polynomial interpretation over natural numbers and rational
    numbers. *)

    apply polynomial_interpretation_dp_ok with (D':=D')(is:=is)(d:=d).
    apply h. apply wf.
    
    (** Matrix interpretation over natural numbers. *)

    destruct d; simpl in h; try discr.
    apply matrix_interpretation_nat_dp_ok with (D':=D')(d:=d0)(is:=is).
    apply h. apply wf.

    (** Matrix interpretation over arctic natural numbers.  *)

    destruct d; simpl in h; try discr.
    apply matrix_interpretation_arcnat_dp_ok with (D':=D')(d:=d0)(is:=is).
    apply h. apply wf.
        
    (** Matrix interpretation over arctic integer numbers. *)

    apply matrix_interpretation_arcbz_dp_ok with (D':=D')(d:=d0)(is:=is).
    apply h. apply wf.
  Qed.

  (***********************************************************************)
  (** Correctness proof of path ordering the case of top termination
  problems. *)

  Variable bb : nat.

  Require Import Coccinelle2 ordered_set rpo2 cpf2color_rpo.

  (* RPO without Argument filtering method. *)

  Lemma rpo_without_af_dp_ok: forall a (R D D': arules a) l
      (h: match pathOrder_term_dp bb a l with
      | Ok (bsucc_ge, bsucc_gt) =>
          if forallb (abrule bsucc_ge) D && forallb (abrule bsucc_ge) R
          then Ok (filter (abrule (neg bsucc_gt)) D)
          else Ko (arules a) ENotpathOrder_dp
      | Ko e => Ko (arules a) e
      end = Ok D')(wf : WF(hd_red_mod R D')), WF(hd_red_mod R D).

  Proof.
    intros a R D D' l h wf.
    case_eq (pathOrder_term_dp bb a l); intros p H;
      rewrite H in h; try discr.
    destruct p as [bge bgt].
    case_eq (forallb (abrule bge) D && forallb (abrule bge) R);
      intros H1; rewrite H1 in h; try discr.
    inversion h. subst D'. clear h.
    unfold pathOrder_term_dp in H.
    gen H.
    set (b:= forallb (fun f : Sig a =>
      forallb (fun g : Sig a => bprec_eq_status_symb l f g) (list_sig l))
    (list_sig l)).
    case_eq b; intros; subst b; try discr.
    inversion H2. clear H2.

    apply WF_wp_hd_red_mod2 with (bwp := bwrp_rpo bb (P a l bb)).

    (** Check that all rules [R] are included in [>=] *)

    simpl. unfold brule, bsucceq_rpo; simpl.
    rewrite forallb_forall. intros x Hx. subst bge.
    rewrite andb_eq in H1. destruct H1.
    rewrite forallb_forall in H2.
    ded (H2 x Hx).
    destruct x as [t u]. simpl in *.
    unfold abrule in H3. apply H3.

    (** Check that all rules in [D = dp R] are included in [>=]. *)
 
    simpl. unfold brule, bsucceq_rpo; simpl.
    rewrite forallb_forall. intros x Hx. subst bge.
    rewrite andb_eq in H1. destruct H1.
    rewrite forallb_forall in H1.
    ded (H1 x Hx).
    destruct x as [t u].
    simpl in *.
    unfold brule in H3. apply H3.

    (** Remove all rules [D] that are included in [>]. *)

    apply WF_incl with (S:= hd_red_mod R (filter (brule (neg bgt)) D)).
    unfold inclusion. intros t u H3. redtac.
    Focus 2. hyp.
    unfold hd_red_mod. unfold compose.
    exists t0. split. hyp.
    unfold hd_red. exists l0. exists r.
    exists s. intuition.
    apply filter_In. apply filter_In in lr. intuition.
    unfold brule, neg. unfold brule, neg in H6.
    simpl in *. subst bgt.
    apply H6.
  Qed.

  (***********************************************************************)
  (** RPO with argument filtering method. *)

  Require Import cpf2color_argfilter.

  Lemma rpo_with_af_dp_ok: forall a (R D D': arules a) l o
    (h:match pathOrder_term_rpo_af_dp bb a l o with
         | Ok (bsucc_ge, bsucc_gt) =>
           if forallb (abrule bsucc_ge) D && forallb (abrule bsucc_ge) R
             then Ok (filter (abrule (neg bsucc_gt)) D)
             else Ko (arules a) ENotpathOrder_AF_dp
         | Ko e => Ko (arules a) e
       end = Ok D') (wf: WF (hd_red_mod R D')), WF (hd_red_mod R D).
  
  Proof.
    intros a R D D' l oaf h wf.
    case_eq (pathOrder_term_rpo_af_dp bb a l oaf);
      intros p H; rewrite H in h; try discr.
    destruct p as [bge bgt].
    case_eq (forallb (abrule bge) D && (forallb (abrule bge) R));
      intros H1; rewrite H1 in h; try discr.
    inversion h. subst D'. clear h.
    unfold pathOrder_term_rpo_af_dp in H.
    destruct oaf; try discr.
    
    destruct p; try discr.
    destruct p; try discr.
    
    (** Argument filtering method. *)
    
    case_eq (is_col_noncol t); intros H2; rewrite H2 in H; try discr.
    set (ls:=(s,a0,t)::oaf). fold ls in H.
    case_eq (pathOrder_rpo_proj_filter_dp bb a l ls); intros p H3;
      rewrite H3 in H; try discr.
    inversion H. clear H. subst p.
    unfold pathOrder_rpo_proj_filter_dp in H3.
    gen H3.
    set (b:=forallb
      (fun f : Sig a =>
        forallb (fun g : Sig a => bprec_eq_status_symb l f g) (list_sig l))
      (list_sig l)).
    case_eq b; intros; subst b; try discr.
    inversion H0. clear H0.

    apply WF_wp_hd_red_mod with (bwp:= @bwrp_perm2 (Sig a)
    (color_Perm ls a)
    (@bwrp_proj (Sig (@ASignature.arity (color_Sig_perm ls a)))
    (@color_Proj ls (@ASignature.arity (color_Sig_perm ls a)))
    (Coccinelle2.bwrp_rpo bb (P (@ASignature.arity (color_Sig_perm ls a)) l bb)))).

    (** Check that all rules [R] are included in [>=] *)

    simpl. unfold brule, bsucceq_rpo; simpl.
    rewrite forallb_forall. intros x Hx. subst bge.
    rewrite andb_eq in H1. destruct H1.
    rewrite forallb_forall in H1.
    ded (H1 x Hx).
    destruct x as [u v]. simpl in *.
    unfold abrule in H4. apply H4.

    (** Check that all rules in [D = dp R] are included in [>=]. *)
 
    simpl. unfold brule, bsucceq_rpo; simpl.
    rewrite forallb_forall. intros x Hx. subst bge.
    rewrite andb_eq in H1. destruct H1.
    rewrite forallb_forall in H0.
    ded (H0 x Hx).
    destruct x as [u v].
    simpl in *.
    unfold brule in H4. apply H4.

    (** Remove all rules [D] that are included in [>]. *)

    apply WF_incl with (S:= hd_red_mod R (List.filter (brule (neg bgt)) D)).
    unfold inclusion. intros u v H7. redtac.
    Focus 2. hyp.
    unfold hd_red_mod. unfold compose.
    exists t0. split. hyp.
    unfold hd_red. exists l0. exists r.
    exists s0. intuition.
    apply filter_In. apply filter_In in lr. intuition.
    unfold brule, neg. unfold brule, neg in H7.
    simpl in *. subst bgt.
    apply H7.
  Qed.

  (***********************************************************************)
  (** Correctness proof of RPO with/without argument filtering method
     in the case of DP.*)

  Lemma pathOrder_dp_ok : forall a (R D D': arules a) l o,
    pathOrder_dp bb R D l o = Ok D' -> WF (hd_red_mod R D') ->
    WF (hd_red_mod R D).

  Proof.
    intros a R D D' l oaf h wf.
    unfold pathOrder_dp in h.
    destruct oaf; try discr.
   
    (** Path ordering with argument filtering. *)

    apply rpo_with_af_dp_ok with (D':=D')(l:=l)(o:=a0).
    hyp. hyp.
    
    (** Path ordering without argument filtering. *)
    
    apply rpo_without_af_dp_ok with (D':=D')(l:=l).
    hyp. hyp.
  Qed.
    
  (***********************************************************************)
  (** ** Check that [dps] is valid termination proof for dependency
  pair proof [hd_red_mod R D]. *)

  (** [nat_of_string]: convert variable map to natural number *)

  Variable nat_of_string: string -> nat.

  Lemma unit_ok : forall u, Ok u = OK.
    
  Proof.
    induction u. unfold OK. unfold Zero. refl.
  Qed.
  
  Lemma dpProof_pIsEmpty_ok : forall a (R D: arules a),
    dpProof_pIsEmpty D = OK -> WF (hd_red_mod R D).
    
  Proof.
    intros a R D. unfold dpProof_pIsEmpty. destruct D; simpl; intro.
    apply WF_hd_red_mod_empty. discr.
  Qed.
     
  (***********************************************************************) 
  (** Correctness proof of dependency pairs. *)

  Require Import AProj AFilterPerm.

  Lemma dpProof_ok : forall n a (R D: arules a) dps,
    dpProof bb nat_of_string n R D dps = OK -> WF (hd_red_mod R D)
    with
    AF_ok : forall n a (R D : arules a) a0 dps,
     AF_dp bb nat_of_string n R D a0 dps = OK -> WF (hd_red_mod R D)                    
    with
      dpProof_depGraphProc_ok: forall n a (R D: arules a) cs,
        depGraphProc bb nat_of_string n R D cs = OK -> WF (hd_red_mod R D).
  
  Proof.
    induction n; try discr; simpl in *.
        
    (** Correctness proof by using dependency pair. *)
        
    destruct dps; try discr.
        
    (** Correctness proof when the dependency pair (D) is empty. *)
        
    intros H. apply dpProof_pIsEmpty_ok. hyp.
        
    (** Correctness proof of rule removal in the case of dependency
    pair method. *)

    Focus 2. destruct o; simpl in *; try discr.
    unfold trsTerminationProof_ruleRemoval_dp.
    destruct o0; simpl in *; try discr.
    unfold orderingConstraintProof_redPair_dp.
    destruct r; simpl in *; try discr.
    case_eq (redPair_interpretation_dp R D t l);
      intros l0 H1 H2; try discr.
    apply redPair_interpretation_dp_ok in H1. hyp.
    eapply dpProof_ok. 
    apply H2.

    (** Correctness proof of path ordering. *)

    case_eq (pathOrder_dp bb R D l o);
      intros l0 H1 H2; try discr.
    apply pathOrder_dp_ok in H1. hyp.
    eapply dpProof_ok. apply H2.
    
    (** Decomposition graph. *)
        
    destruct n; try discr; simpl in *.
    case_eq (forallb (is_notvar_lhs (Sig:=Sig a)) R &&
      forallb (undefined_rhs R) D && brules_preserve_vars D);
    intros H1; try discr.
    case_eq (decomp nat_of_string a l); intros l0 H2; try discr.
    set (l1:= split_list l0). 
    case_eq (equiv_rules (flat l1) D); intros H4; try discr.
    set (approx:= dpg_unif_N (S n) R D).
    case_eq (valid_decomp approx l1); intros H5; try discr.
    case_eq (forallb
      (fun ci : arules a * bool * option (list positiveInteger) *
        option cpf.dpProof =>
          match ci with
            | (dps, true, _, Some pi) => bool_of_result
              (dpProof bb nat_of_string n R dps pi)
            | (dps, true, _, None) => false
            | (dps, false, _, _) => co_scc approx dps
          end) l0); intros H6 H7; try discr. 
    
    eapply WF_decomp_co_scc with (approx:=approx)(cs:=l1).
        
    (** Over graph using a finite number of unification steps. *)
    
    apply dpg_unif_N_correct.
    
    (** [hypR: forallb (@is_notvar_lhs Sig) R = true]. *)

    do 2 rewrite andb_eq in H1. intuition.
        
    (** [hypD: forallb (undefined_rhs R) D = true]. *)

    do 2 rewrite andb_eq in H1. intuition.

    (** [hypD: rules_preserve_vars D]. *)
        
    do 2 rewrite andb_eq in H1. intuition.
    apply brules_preserve_vars_ok. hyp.

    (** [hyp4: D [= flat cs]. *)

    unfold equiv_rules in H4. rewrite equiv_ok in H4. apply H4.
    intros r1 r2. split. intros.
    rewrite ATrs.beq_rule_ok in H. hyp.
    intros. apply ATrs.beq_rule_ok. hyp.
        
    (** [hyp1: flat cs [= D] *)
        
    unfold equiv_rules in H4. apply equiv_ok in H4. apply H4.
    intros r1 r2. split. intros.
    rewrite ATrs.beq_rule_ok in H. hyp. intros.
    apply ATrs.beq_rule_ok. hyp.

    (** [hyp2 : valid_decomp cs = true] *)

    hyp.
        
    (** [hyp3 : lforall (fun ci => co_scc ci = true \/ WF (hd_red_Mod
    S ci)) cs] *)

    clear H2 H4 H5 H7. induction l0; simpl in *; try auto.
    split. Focus 2.
    apply IHl0. rewrite andb_eq in H6. destruct H6.
    apply H0. rewrite andb_eq in H6.
    destruct H6. destruct a0; try discr; simpl in *.
    do 2 destruct p; try discr. destruct b; try discr.
    destruct o; try discr. right.
    unfold bool_of_result in H.
    case_eq (dpProof bb nat_of_string n R l2 d); intros u Hdp;
      rewrite Hdp in H; try discr.
    eapply dpProof_ok. erewrite <- unit_ok. apply Hdp.
    left. apply H. Focus 4.

    (** Correctness of depGraphProc. *)
    
    induction n; simpl in *; try discr; auto.
    intros a R D cs.
    case_eq (forallb (is_notvar_lhs (Sig:=Sig a)) R &&
      forallb (undefined_rhs R) D &&
      brules_preserve_vars D); intros H1; try discr.
    case_eq (decomp nat_of_string a cs); intros l H2; try discr.
    case_eq (equiv_rules (flat (split_list l)) D); intros H3; try discr.
    case_eq (valid_decomp (dpg_unif_N (S n) R D) (split_list l));
      intros H4; try discr.
    case_eq (forallb
      (fun
        ci : arules a * bool * option (list positiveInteger) *
        option cpf.dpProof =>
          match ci with
            | (dps, true, _, Some pi) => bool_of_result
                  (dpProof bb nat_of_string n R dps pi)
            | (dps, true, _, None) => false
            | (dps, false, _, _) => co_scc (dpg_unif_N (S n) R D) dps
          end) l); intros H5 H6; try discr.
    clear H6.
    
    eapply WF_decomp_co_scc.
        
    (** Over graph using a finite number of unification steps. *)
        
    apply dpg_unif_N_correct.
    
    (** [hypR: forallb (@is_notvar_lhs Sig) R = true] *)
        
    do 2 rewrite andb_eq in H1. intuition.
    
    (** [hypD: forallb (undefined_rhs R) D = true] *)
        
    do 2 rewrite andb_eq in H1. intuition.

    (** [hypD: rules_preserve_vars D] *)

    do 2 rewrite andb_eq in H1. intuition.
    apply brules_preserve_vars_ok. hyp.
        
    (** [hyp4: D [= flat cs] *)
        
    unfold equiv_rules in H3. rewrite equiv_ok in H3. apply H3.
    intros r1 r2. split. intros.
    rewrite ATrs.beq_rule_ok in H. hyp. intros.
    apply ATrs.beq_rule_ok. hyp.
        
    (** [hyp1: flat cs [= D] *)

    unfold equiv_rules in H3. apply equiv_ok in H3. apply H3.
    intros r1 r2. split. intros. rewrite ATrs.beq_rule_ok in H. hyp.
    intros. apply ATrs.beq_rule_ok. hyp.
        
    (** [hyp2 : valid_decomp cs = true] *)

    try apply H4.
        
    (** [hyp3 : lforall (fun ci => co_scc ci = true 
       \/ WF (hd_red_Mod S ci)) cs] *)
    
    clear H2 H3 H4. induction l; simpl in *; try auto.
    split. Focus 2. apply IHl. rewrite andb_eq in H5.
    destruct H5. apply H0. rewrite andb_eq in H5. destruct H5.
    destruct a0; try discr. do 2 destruct p; try discr.
    destruct b; try discr. destruct o; try discr. right.
    unfold bool_of_result in H.
    case_eq (dpProof bb nat_of_string n R l0 d); intros u Hdp;
      rewrite Hdp in H; try discr.
    eapply dpProof_ok. erewrite <- unit_ok. apply Hdp.
    left. apply H.
    
    (** monoRedPairProc *)

    destruct o; simpl in *; try discr.
    unfold trsTerminationProof_ruleRemoval_dp.
    destruct o0; simpl in *; try discr.
    unfold orderingConstraintProof_redPair_dp.
    destruct r; simpl in *; try discr.
   
    (** Reduction pair interpretation in DP. *)

    case_eq (redPair_interpretation_dp R D t0 l);
      intros l0 H1 H2; try discr.
    apply redPair_interpretation_dp_ok in H1. hyp. 
    eapply dpProof_ok. apply H2.

    (** Path ordering in DP. *)

    case_eq (pathOrder_dp bb R D l o); intros l0 H1 H2; try discr.
    apply pathOrder_dp_ok in H1. hyp.
    eapply dpProof_ok. apply H2.

    (** Argument filtering in dependency pair. *)
    
    destruct n; try discr; simpl in *.
    destruct a0; try discr.
    destruct p; try discr.
    destruct p; try discr.
    
    (** In the case it is a collapsing. *)

    case_eq (is_collapsing t0); intros H H0; try discr.
    eapply WF_hd_red_mod_proj.
    apply dpProof_ok in H0.
    unfold color_proj_rules, color_pi_proj in H0. 
    apply H0.

    (** In the case it is not a collapsing. *)

    revert H0. 
    case_eq (is_noncollapsing t0 && bnon_dup (Sig a)
         (color_raw_pi_filter a ((s, a1, t0) :: a0))
         (list_split_triple ((s, a1, t0) :: a0)));
      intros H1 H0; try discr.  
    rewrite andb_eq in H1. destruct H1.
    apply dpProof_ok in H0.
    unfold color_filter_rules, color_filter_rule, color_build_pi in H0.
    eapply WF_hd_red_mod_filter.
    rewrite bnon_dup_ok in H2. 
    apply H2. apply H0. eapply AF_ok. apply H0.

    (* Correctness proof of AF. *)

    induction n; simpl in *; try discr.
    intros a R D af dps.
    destruct af; try discr.
    destruct p; try discr.
    destruct p; try discr.

    (* collapsing is true *)

    case_eq (is_collapsing t); intros H H0; try discr.
    eapply WF_hd_red_mod_proj.
    apply dpProof_ok in H0.
    unfold color_proj_rules, color_pi_proj in H0. 
    apply H0.

    (* non-collapsing is true. *)

    revert H0. 
    case_eq (is_noncollapsing t && bnon_dup (Sig a)
         (color_raw_pi_filter a ((s, a0, t) :: af))
         (list_split_triple ((s, a0, t) :: af)));
      intros H1 H0; try discr.  
    rewrite andb_eq in H1. destruct H1.
    apply dpProof_ok in H0.
    unfold color_filter_rules, color_filter_rule, color_build_pi in H0.
    eapply WF_hd_red_mod_filter.
    rewrite bnon_dup_ok in H2. 
    apply H2. apply H0. eapply AF_ok. apply H0.
  Qed. (* REMARK: it takes long time at QED. *)

  (***********************************************************************)
  (** No rule left hand side is a variable in [dp R]. *)

  (*
  Lemma is_notvar_lhs_dp :
    forall a R, forallb (@is_notvar_lhs (Sig a)) (dp R) = true.
  
  Proof.
    unfold dp. induction R; simpl. refl.
    destruct a0 as [l r]. rewrite forallb_app. rewrite andb_eq. split. 
    (* *) 
    rewrite forallb_forall. intros.
    destruct (in_map_elim H). destruct H0.
    rewrite forallb_forall in IHR. ded (IHR x). rewrite H2. auto.
    rewrite filter_In in H0. destruct H0. destruct x. injection H1.
    intros. subst x0. subst lhs. clear H1.
    change (In {| lhs := l; rhs := rhs |} (dp R)).
    eapply dp_intro with (r := rhs). 
    eapply in_appr in H. eapply in_app in H. destruct H. apply H. 
    ded (in_elim H). do 2 destruct H1. Focus 3. apply H3.
  Admitted. *)

  (* REMOVE *)
  (*  
  Variables is_notvar_lhs_dp : forall a R, forallb (@is_notvar_lhs
    (Sig a)) (dp R) = true.
  
  (** No rule right hand side is a variable in [dp R]. *)

  Variables is_notvar_rhs_dp : forall a R, forallb (@is_notvar_rhs
    (Sig a)) (dp R) = true. *)
      
  (***********************************************************************)
  (** ** Check that [p] is a valid termination proof for [red R]. *)
  
  (** [n: nat] is an artificial extra argument which purpose is to
     make the function [dpProof] structually recursive with respect to
     this argument. *)
  
  Variable n : nat.

  (** Prove dependency pair transformation method with mark symbol. *)

  (* FIXME: two conditions [no_lhs_var (R)] and [rules_preserve_vars R]. *)

  Lemma dpTrans_mark_ok : forall a rs dps p (Hm:
    dpTrans_mark bb nat_of_string n rs dps p = OK) 
    (H:  forallb (is_notvar_lhs (Sig:=Sig a)) rs &&
      forallb (is_notvar_lhs (Sig:=Sig a)) (dp rs) &&
      forallb (is_notvar_rhs (Sig:=Sig a)) (dp rs) && 
      brules_preserve_vars rs = true), WF (red rs).
  
  Proof.
    intros a rs dps p Hm H.
    unfold dpTrans_mark in Hm.
    case_eq (color_rules (dp_arity a) nat_of_string dps); intros l H0;
      rewrite H0 in Hm; try discr.
    case_eq (equiv_rules l (Fl (HFSig_of_dup_Sig_eq (arity:=a))
      (dup_hd_rules (dp rs)))); intros H1;
    rewrite H1 in Hm; try discr.

    (* Proving well-founded chain: need to prove two assumptions:
     [no_var_lhs R] and [rules_preserve_vars R]. *)

    apply WF_chain.

    (* No variable at the left hand side of the rules [R]. *)

    do 3 rewrite andb_eq in H. do 3 destruct H. apply H.

    (* Preserve variables of rules [R]. *)

    rewrite andb_eq in H. destruct H.
    apply brules_preserve_vars_ok. apply H2.

    (* Preservation of termination by marking. *)

    apply WF_duplicate_hd_int_red.

    (* No variable on the left hand side of [dp R]. *)

    do 3 rewrite andb_eq in H. do 3 destruct H.
    hyp.
    
    (* No variable on the right hand side of [dp R]. *)

    do 3 rewrite andb_eq in H. do 3 destruct H.
    hyp.

    (* rs [=] dp rs. *)
    
    unfold equiv_rules in H1. intuition. apply equiv_ok in H1.
    apply Fhd_red_mod_WF_fin with (HF:= HFSig_of_dup_Sig_eq (arity:=a)).
    
    apply dpProof_ok in Hm. rewrite <- H1. apply Hm.

    (* beq_rule *)

    intros r1 r2. split. intros. apply ATrs.beq_rule_ok in H2. apply H2.
    intros. rewrite ATrs.beq_rule_ok. apply H2.
  Qed.

  (***********************************************************************)
  (** Prove dependency pair transformation method without mark
  symbol. *)
  
  Lemma dpTrans_unmark_ok : forall a rs dps p
    (Hm: dpTrans_unmark bb nat_of_string n rs dps p = OK)
    (H:  forallb (is_notvar_lhs (Sig:=Sig a)) rs &&
      forallb (is_notvar_lhs (Sig:=Sig a)) (dp rs) &&
      forallb (is_notvar_rhs (Sig:=Sig a)) (dp rs) && 
      brules_preserve_vars rs = true), WF (red rs).
  
  Proof.
    intros a rs dps p Hm H.
    unfold dpTrans_unmark in Hm.
    case_eq (color_rules a nat_of_string dps);
      intros l H0; rewrite H0 in Hm; simpl in *; try discr.
    case_eq (equiv_rules l (dp rs)); intros H1;
      rewrite H1 in Hm; simpl in *; try discr.

    (* Using well-founded induction on chain. *)

    apply WF_chain.

    (* No variables at the left hand side of rules [R]. *)

    do 3 rewrite andb_eq in H. do 3 destruct H. hyp.

    (* Preserve variables of rules [R]. *)

    rewrite andb_eq in H. destruct H. 

    apply brules_preserve_vars_ok. apply H2.

    (* Change [chain] into [hd_red_mod rs [dp rs]]. *)

    rewrite chain_hd_red_mod.

    (* rs [=] dp rs *)

    unfold equiv_rules in H1. rewrite equiv_ok in H1.
    rewrite <- H1.

    (* Correctness proof of dpProof: WF (hd_red_mod rs l). *)

    eapply dpProof_ok. apply Hm.

    (* beq_rule. *)

    intros r1 r2. split. intro. rewrite ATrs.beq_rule_ok in H2; hyp.
    intro. apply ATrs.beq_rule_ok; hyp.
  Qed.

  (***********************************************************************)
  (** Correcntness proof of dependency pair transformation. *)

  Lemma trsTerminationProof_dpTrans_ok : forall a (R: arules a) dps b p,
    trsTerminationProof_dpTrans bb nat_of_string n R dps b p = OK ->  WF (red R).
    
  Proof.
    intros a rs dps b p Hm.
    unfold trsTerminationProof_dpTrans in Hm.
    (* Prove the condition do not have variables in the left hand side
       and preverse variables in rules [R]. *)
    case_eq (forallb (is_notvar_lhs (Sig:=Sig a)) rs &&
                     forallb (is_notvar_lhs (Sig:=Sig a)) (dp rs) &&
                     forallb (is_notvar_rhs (Sig:=Sig a)) (dp rs) &&
                     brules_preserve_vars rs); intro H; rewrite H in Hm; try discr.
    destruct b; try discr.
    (* Proving dependency pair where symbols are marked. *)
    apply dpTrans_mark_ok with (dps:=dps)(p:=p).
    apply Hm. apply H.
    (* Proving dependency pair where symbols are not marked. *)
    apply dpTrans_unmark_ok with (dps:=dps)(p:=p).
    apply Hm. hyp.
  Qed.

    (* TODO *)

    (* Prove the condition do not have variables in the left hand side
       and preverse variables in rules [R]. *)
    (*
    case_eq (forallb (is_notvar_lhs (Sig:=Sig a)) rs 
      && brules_preserve_vars rs); intros H; rewrite H in Hm; try discr.
    destruct b; try discr.  
    apply dpTrans_mark_ok with (dps:=dps)(p:=p).

    apply Hm. apply H.
    apply dpTrans_unmark_ok with (dps:=dps)(p:=p).
    apply Hm. apply H. *)
 
End Top_Termination.