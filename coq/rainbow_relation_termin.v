(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2011-04-06

* CPF correctness checker

 TO BE FINISH: proving relative termination 
*)

Set Implicit Arguments.

Require Import ATrs SN ZArith EqUtil String List ListDec ListForall
  ListUtil ZUtil LogicUtil BoolUtil VecUtil NArith RelUtil RelMidex
  ARelation NatUtil ListExtras RelUtil AVarCond OrdSemiRing2 Polynom2
  MonotonePolynom2 PositivePolynom2 AMannaNess ARedPair2 APolyInt2
  error_monad cpf2color AWFMInterpretation cpf Z_as_SR
  rainbow_full_termin.

Section Top.

  (* We assume given a function translating variable names into
     natural numbers. *)

  Variable nat_of_string : string -> nat.

  (* We assume given an arity function. *)

  Variable arity : symbol -> nat.

  Notation Sig := (Sig arity).
  Notation aterm := (aterm arity).
  Notation arule := (arule arity).
  Notation arules := (arules arity).
  Notation abrule := (abrule arity).
  
  Implicit Type R : arules.   

  (************************************************************************)
  (** Relative termination use polynomial interpretation over
          domain natural and rational numbers.
          Given a pair (>=, >) is a reduction pair.
          if the orders are weakly decreasing in R and D,
          then remove all strictly decreasing in R and D,
          otherwise return error message. *)

  Definition rel_polynomial_interpretation (R D: arules) is dom :
    result arules :=
    match type_polynomial arity is dom with
      | Ok (bge, bgt) =>
        if   ge_R_D R D bge
        then gt_D D bgt (* FIXME : remove R D *)
        else Ko _ (Fail FRuleNotInLargeOrdering_poly)
      | Ko e => Ko _ e
    end.

    (**************************************************************************)
    (** ** Matrix interpretation over domain natural number *)

    Require Import AMatrixBasedInt2 Matrix2 OrdSemiRing2 AMatrixInt2 Nat_as_OSR.
      
    Open Scope nat_scope.

    (***********************************************************************)
    (** Relative termination use matrix interpretation over domain
       natural numbers. Relative termination has the same condition
       like full termination, where the relation [>] is closed by
       context and [>] is monotone. Use the [type_matrix_polynomial]
       of full termination for relative termination. *)
    
    Definition rel_matrix_interpretation (R D: arules) is dom dim := 
      match type_matrix arity is dom dim with
        | Ok (bge, bgt) =>
          if   ge_R_D R D bge
          then gt_D D bgt
          else Ko _ (Error ERuleNotInLargeOrdering_matrix_rel)
        | Ko e => Ko _ e
      end.

    Close Scope nat_scope.
    
    (**********************************************************************)
    (** [type_matrixInterpertation] of relative termination proof.
       REMARK: In domain arctic only occur at top termination and not
       in relative termination. Domain naturals. *)
    
    Definition rel_type_matrix_interpretation (R D: arules) is dom dim :=
      match dom with
        | Domain_naturals => rel_matrix_interpretation R D is dom
                            (nat_of_P dim)
        | Domain_integers =>
          Ko _ (Todo Ttype_polynomialDomain_integers)
        | Domain_rationals delta =>
          Ko _ (Todo Ttype_polynomialDomain_rationals)
        | Domain_tropical _ =>
          Ko _ (Todo Ttype_polynomialDomain_tropical)
        | Domain_arctic dom'=>
          Ko _ (Todo Ttype_polynomialDomain_arctic)
        | Domain_matrices dim sdim dom' =>
          Ko _ (Todo Ttype_polynomialDomain_matrices)
      end.

    (***********************************************************************)
    (** ** Relative termination reduction pair interpretation with
     polynomial and matrix interpretation in domain: natural numbers
     and rational numbers. *)

    Definition rel_redPair_interpretation (R D: arules) (t: type_t9) 
      (is: list (symbol * cpf.arity * function)): result arules :=
      match t with
        | Type_t9_polynomial dom degmax =>
            rel_polynomial_interpretation R D is dom
        | Type_t9_matrixInterpretation dom dim sdim =>
            rel_type_matrix_interpretation R D is dom dim
      end.

    (** Correctness proof of relation redPair interpretation.

      Proof structure:

       1. Correctness proof of polynomial interpretation.

          a. Domain natural numbers.

          b. Domain rational numbers
            - Coefficients are of domain integer.
            - Coefficients are of domain rationals
       2. Correctness proof of matrix interpretation.

          a. Domain natural numbers.

          b. Domain tropical numbers. *)
    
    Require Import APolyInt_MA2. Import OR_Notations.
    
    Lemma rel_poly_nat_ok : forall (R D D': arules) is
      (h:  match poly_nat arity is with
            | Ok (bge, bgt) =>
             if   ge_R_D R D bge
             then gt_D D bgt
             else Ko _ (Fail FRuleNotInLargeOrdering_poly)
            | Ko e => Ko _ e
           end = Ok D')(wf: WF (red_mod R D')), WF (red_mod R D).

    Proof.
      intros R D D' is h wf.
      case_eq (poly_nat arity is); intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt].
      case_eq (ge_R_D R D bge);
        intros H0; rewrite H0 in h; try discr.
      unfold gt_D in h. unfold ge_R_D in H0.
      inversion h. subst D'. clear h. simpl in *.
      unfold poly_nat in H. revert H.
      destruct (map_rev (color_interpret arity) is); intros; try discr.
      case_eq (conditions_poly_nat arity l); intro H1;
      rewrite H1 in H; try discr.
      inversion H. clear H.
      unfold conditions_poly_nat in H1.
      set (trsInt := (fun f: symbol => fun_of_pairs_list arity f l)).
      cut (forall f: Sig, pweak_monotone (trsInt f)).
      intros trsInt_wm. Focus 2.
      (** Polynomial weak is monotone. *)
      intro f. apply trsInt_wm_poly.
      (** Proving wellfound of [red_mod]. *)
      rewrite andb_eq in H1. destruct H1. hyp.
      rewrite andb_eq in H1. destruct H1.
      apply WF_rp_red_mod with (WP:=@WP _ _ l H).
      (** Relation [>] is closed by context. *)
      change (context_closed (IR (@I Sig  _ (TPolyInt_poly arity l H)) succ)).
      apply IR_context_closed. apply pi_monotone.
      simpl. intro f.
      (** Polynomial is strong monotone. *)
      apply trsInt_pw_poly. rewrite andb_eq. split. hyp. hyp.
      (** Check that all rules [R] are included in [>=]. *)
      simpl; unfold brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      rewrite forallb_forall in H2.
      ded (H2 x Hx).
      destruct x as [t u]. simpl in *.
      destruct succeq'_dec; try discr; auto.
      unfold succeq' in n. unfold brule, redpair_poly_nat_ge in H3.
      rewrite bcoef_not_neg_ok in H3. contradiction.
      (** All relation [>=] are including in rule [dp R = D]. *)
      simpl; unfold brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      rewrite forallb_forall in H0. ded (H0 x Hx).
      destruct x as [t u]. simpl in *.
      destruct succeq'_dec; auto.
      unfold brule, redpair_poly_nat_ge in H3. rewrite bcoef_not_neg_ok in H3.
      unfold succeq' in n. contradiction.
      (** Remove all rules [D] that are included in [>]. *)
      apply WF_incl with (S:= red_mod (filter (brule (neg bgt)) R)
                                      (filter (brule (neg bgt)) D)).
      unfold inclusion. intros t u H7. redtac. unfold red_mod.
      unfold compose. exists t0. split. simpl in *.
      Focus 2.
      (* red (filter (brule (neg bgt)) D) t0 u *)
      unfold red. exists l0. exists r. exists c.
      exists s. intuition. apply filter_In.
      apply filter_In in lr. intuition.
      unfold brule, neg. unfold brule, neg in H6.
      simpl in *. unfold bsucc, bool_of_rel in H6.
      destruct AMonAlg2.ma_succ'_dec in H6; try discr.
      simpl in *. unfold succ' in n.
      rewrite <- bcoef_not_neg_ok in n.
      apply eq_true_not_negb in n.
      subst bgt. apply n.
      (* red (filter (brule (neg bgt)) R #) t t0 *)
      (* TODO *)
      
    Admitted.

    (***************************************************************************)
    (** Correctness proof of termination relation [red_mod R D] of
    polynomial interpretation over rational numbers.  *)

    (* REMARK: open scope Q to be able to fold argument [b] in the
    proof. *)

    Open Scope Q_scope. Require Import Q_as_R.

    Lemma rel_poly_rationals_common_ok : forall del (R D D': arules) is
      (h : match poly_rat arity is del with
             | Ok (bge, bgt) =>
               if   ge_R_D R D bge
               then gt_D D bgt
               else Ko _ (Fail FRuleNotInLargeOrdering_poly)
             | Ko e => Ko _ e
           end = Ok D')(wf : WF (red_mod R D')), WF (red_mod R D).
    
    Proof.
      intros del R D D' is h wf.
      case_eq (poly_rat arity is del); intros p H; rewrite H in h;
      try discr.
      destruct p as [bge bgt].
      case_eq (ge_R_D R D bge);
        intros H0; rewrite H0 in h; try discr.
      unfold gt_D in h. unfold ge_R_D in H0.
      inversion h. subst D'. clear h.
      unfold poly_rat in H.
      case_eq (map_rev (color_interpret arity) is);
        intros l H1; rewrite H1 in H; try discr.
      case_eq (conditions_poly_rat arity l); intros H2; rewrite H2 in H;
      try discr.
      inversion H. clear H.
      unfold conditions_poly_rat in H2.
      set (trsInt := (fun f: symbol => fun_of_pairs_list arity f l)).
      cut (forall f: symbol, pweak_monotone (trsInt f)).
      intros trsInt_wm. Focus 2.
      (** Polynomial weak is monotone. *)     
      intro f. apply trsInt_wm_poly.      
      (** Proving [WF (red_mod R D)]. *)
      rewrite andb_eq in H2. destruct H2. hyp.
      rewrite andb_eq in H2. destruct H2.
      apply WF_rp_red_mod with (WP:=@WP_Q _ _ l H del).
      (* A proof of [>] are closed by context: IR_context_closed. *)
      change (context_closed (IR (@I Sig _ (TPolyInt_poly arity l H)) succ)).
      apply IR_context_closed. apply pi_monotone.
      simpl. intro f.     
      (* Polynomial is strong monotone. *)
      apply trsInt_pw_poly. rewrite andb_eq. split. hyp. hyp.
      (* Check that all rules [R] are included in [>=]. *)
      simpl; unfold brule, ds_wr_bsucceq, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      rewrite forallb_forall in H3. ded (H3 x Hx). destruct x as [t u].
      simpl in *. 
      case_eq (succeq'_dec Sig (TPolyInt_poly arity l H) t u);
        intros s Hs. auto.
      unfold brule, redpair_poly_rat_ge in H4. unfold succeq' in s.
      rewrite bcoef_not_neg_ok in H4. contradiction.
      (** Proving the relation [>=] are in rules [D]. *)
      simpl. unfold brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      rewrite forallb_forall in H0. ded (H0 x Hx).
      destruct x as [t u]. simpl in *.
      case_eq (succeq'_dec Sig (TPolyInt_poly arity l H) t u);
        intros s Hs. auto. unfold brule, redpair_poly_rat_ge in H4.
      unfold succeq' in s.
      rewrite bcoef_not_neg_ok in H4. contradiction.
      (** Proving [red_mod] is well founded when remove all relation
      [>] in [R] and [D]. *)
      apply WF_incl with (S := red_mod (List.filter (brule (neg bgt)) R)
                                       (List.filter (brule (neg bgt)) D)).
      unfold inclusion. intros t u H7. redtac. unfold red_mod.
      unfold compose. exists t0. split. simpl in *.
      Focus 2.
      (* red (filter (brule (neg bgt)) D) t0 u *)
      unfold red. exists l0. exists r. exists c. exists s.
      intuition. apply filter_In.
      apply filter_In in lr. intuition.
      unfold brule, neg. unfold brule, neg in H7.
      simpl in *. unfold bsucc, bool_of_rel in H7.
      destruct AMonAlg2.ma_succ'_dec in H7; try discr.
      simpl in *. unfold succQ' in n.
      rewrite <- bcoef_not_neg_ok in n.
      apply eq_true_not_negb in n.
      subst bgt. apply n.
    (* red (filter (brule (neg bgt)) R #) t t0 *)
    (* TODO *)     
    Admitted.

    (**************************************************************************)
    (** Correctness proof of termination relation [red_mod R D] of
    polynomial interpretation over rational numbers.  *)

    Require Import QArith_base.

    Lemma rel_poly_rationals_ok: forall (R D D': arules) is n
      (h:  match type_poly_rationals arity n is with
             | Ok (bge, bgt) =>
               if   ge_R_D R D bge
               then gt_D D bgt
               else Ko _ (Fail FRuleNotInLargeOrdering_poly)
             | Ko e => Ko _ e
           end = Ok D')(wf: WF (red_mod R D')), WF (red_mod R D).

    Proof.
      intros R D D' is n h wf.
      unfold type_poly_rationals in h.
      destruct n; simpl in h; try discr.
      set (del:= inject_Z i). fold del in h.
      (** In the case of rationals -> natural numbers, where it convert a
       natural number to rational number by divide by 1. *)     
      apply rel_poly_rationals_common_ok with (del:=del)(D':=D')(is:=is).
      hyp. hyp.
      (** In the case of rationals -> rational numbers. *)
      set (t:= Qmake i p). fold t in h.
      apply rel_poly_rationals_common_ok with (del:=t)(D':=D')(is:=is).
      hyp. hyp.
    Qed.

    Close Scope Q_scope.

    (**************************************************************************)
    (** Correctness proof of termination relation [red_mod R D] of
    polynomial interpretation over rational numbers.  *)

    Lemma rel_polynomial_interpretation_ok: forall (R D D': arules) is d
      (h: rel_polynomial_interpretation R D is d = Ok D')
      (wf : WF (red_mod R D')), WF (red_mod R D).

    Proof.
      intros R D D' is d h wf.
      unfold rel_polynomial_interpretation in h.
      unfold type_polynomial in h.
      destruct d; simpl in h; try discr.
      (** Domain naturals. *)
      apply rel_poly_nat_ok with (D':=D')(is:=is).
      hyp. hyp.
      (** Domain rationals. *)     
      apply rel_poly_rationals_ok with (D':=D')(is:=is)(n:=n).
      hyp. hyp.
    Qed.

    (*************************************************************************)
    (** Correctness proof of termination relation [red_mod R D] of
    matrix interpretation of domain natural. *)

    Require Import ABterm OrdSemiRing2.

    Open Scope nat_scope.

    Lemma rel_matrix_interpretation_nat_ok : forall (R D D': arules) d is
      (h: rel_matrix_interpretation R D is Domain_naturals (Pos.to_nat d) =Ok D')
      (wf : WF (red_mod R D')), WF (red_mod R D).

    Proof.
      intros R D D' d is h wf.
      unfold rel_matrix_interpretation in h.
      destruct Domain_naturals; simpl in h; try discr.
      case_eq (matrix_nat arity is (Pos.to_nat d));
        intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt].
      case_eq (ge_R_D R D bge);
        intro H0; rewrite H0 in h; try discr.
      unfold gt_D in h. unfold ge_R_D in H0.
      inversion h. subst D'. clear h. unfold matrix_nat in H.
      revert H. 
      case (map_rev (color_interpret_matrix arity (Pos.to_nat d)) is);
        intros l H; try discr.
      case_eq (condition_matrix_nat arity l); intro H2; rewrite H2 in H;
      try discr. inversion H. clear H.     
      apply WF_rp_red_mod with (WP:=@WP_Matrix_Nat _ _ l).
      (** Context closed succ *)
      change (context_closed (IR (@AMatrixBasedInt2.I _ Sig _ _
             (@mi_eval_ok _ _ (@TMatrix_Int arity _ coef_sring_N l)))
             (@AMatrixInt2.succ _ _ (@TMatrix_Int _ _ coef_sring_N l)))).
      apply IR_context_closed. 
      apply AMatrixInt2.monotone_succ. simpl. intro f.
      apply trsInt_nat_mon. hyp.
      (** Check that rules R is included in succeq *)
      simpl; unfold brule, ds_wr_bsucceq, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      unfold redpair_matrix_nat_ge in H0.
      rewrite forallb_forall in H0. ded (H0 x Hx).
      destruct x as [t u]. simpl in *.
      destruct (AMatrixBasedInt2.succeq'_dec t u); intros; try discr; auto.
      unfold brule in H1.
      unfold term_ge, term_ord, mint_ge in n.
      eapply bmint_ge_ok in H1. simpl in *.
      unfold mint_ge in H1. simpl in *. try contradiction.
      (** Check that rules D is included in succeq *)
      unfold brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      unfold redpair_matrix_nat_ge in H.
      rewrite forallb_forall in H.
      ded (H x Hx). destruct x as [t u]. simpl in *.
      unfold bsucceq, bool_of_rel.
      destruct AMonAlg2.ma_succeq'_dec; auto.
      unfold brule in H1. simpl in *.
      unfold succeq', AMatrixBasedInt2.succeq',
      term_ge, term_ord, mint_ge in n.
      apply bmint_ge_ok in H1. try contradiction.
      (** Remove all rules D that are in succ. *)
      apply WF_incl with (S:= red_mod (filter (brule (neg bgt)) R)
                                      (filter (brule (neg bgt)) D)).
      unfold inclusion. intros t u H7. redtac. unfold red_mod.
      unfold compose. exists t0. split. simpl in *.
      Focus 2.
      (* red (filter (brule (neg bgt)) D) t0 u *)
      unfold red. exists l0. exists r. exists c.
      exists s. intuition. apply filter_In.
      apply filter_In in lr. intuition.
      unfold brule, neg. unfold brule, neg in H5.
      simpl in *. unfold bsucc, bool_of_rel in H5.
      destruct AMonAlg2.ma_succ'_dec in H5; try discr.
      simpl in *. unfold AMatrixInt2.term_gt, AMatrixBasedInt2.term_gt,
                  term_ord in n; simpl in *; auto.
      unfold AMatrixInt2.mint_gt in n.
      rewrite <- AMatrixInt2.bmint_gt_ok in n.
      apply eq_true_not_negb in n.
      subst bgt. apply n.
    (* red (filter (brule (neg bgt)) R #) t t0 *)      
    (* FIXME: fixe the condition in the boolen function. *)
    (* TODO *)
    Admitted.

    (*************************************************************************)
    (** Correctness proof of termination relation [red_mod R D] of
    reduction pair interpretation. *)

    Lemma rel_redPair_interpretation_ok : forall (R D D': arules) t is,
      rel_redPair_interpretation R D t is = Ok D' ->
      WF (red_mod R D') -> WF (red_mod R D).
    
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

    (***********************************************************************)
    (** Relative termination of ordering constrainst proof with
     reduction pair interpretation. Ordering constrainst proof with
     reduction pair interpretation of dependency pair
     transformation. Currently support interpretation only. *)
    
    Variable rpo_n: nat.

    Definition rel_orderingConstraintProof_redPair (R D:arules) rp
    : error_monad.result arules :=
      match rp with
        | RedPair_interpretation t is    => rel_redPair_interpretation R D t is
        | RedPair_pathOrder sp oaf       => (*pathOrder rpo_n R sp oaf (* TODO *)*)
          Ko _ (Todo Todo1)
        | RedPair_knuthBendixOrder _ _ _ => Ko _ (Todo TRedPair_knuthBendixOrder)
        | RedPair_scnp _ _ _             => Ko _ (Todo TRedPair_scnp)
      end.

    Definition rel_trsTerminationProof_ruleRemoval (R D: arules) ocp :=
      match ocp with
        | OrderingConstraintProof_redPair rp              =>
          rel_orderingConstraintProof_redPair R D rp
        | OrderingConstraintProof_satisfiableAssumption _ =>
          Ko _ (Todo TOrderingConstraintProof_satisfiableAssumption)
      end.
    
End Top.

(***********************************************************************)
(** Check that [R] is a trivial proof by stating the set of rules
    [R] is empty valid termination proof for [red R]. *)
    
Definition relTerminationProof_rIsEmpty a (D : arules a) :=
  if   is_empty D
  then OK
  else Ko _ (Error ErNotEmptyrIsEmpty).
    
Lemma relTerminationProof_rIsEmpty_ok : forall a (R D: arules a),
  relTerminationProof_rIsEmpty D = OK -> WF (red_mod R D).

Proof.
  intros a R D. unfold relTerminationProof_rIsEmpty.
  destruct D; simpl; intro.
  apply WF_red_mod_empty. discr.
Qed.

(***********************************************************************)
(** Check that [p] is a valid termination proof for [red_mod R D].
     - [rIsEmpty] [sIsEmpty]: state that the relative termination is
       terminating since it has no rules.
     - [ruleRemoval]: use a reduction pair where both the weak and the
     strict ordering are monotone. Delete all strictly decreasing
     rules. The remaining rules have to be given. If the ordering
     constraint proof is only an assumption, the
     orderingConstraints-element becomes mandatory.
     - [stringReversal]: reverse the strings in both R and S, i.e., replace
      f(g(h(x))) -&gt; f(x) by h(g(f(x))) -&gt; f(x).  Note that the
      variable in a reversed rule should be same as the variable in the
      original rule.*)

Section S.
  
  Require Import AUnary AReverse.

  Fixpoint relTerminationProof a (R D: arules a) p : result unit :=
    match p with
      | RelativeTerminationProof_rIsEmpty
      | RelativeTerminationProof_sIsEmpty _                       =>
        relTerminationProof_rIsEmpty D
      | RelativeTerminationProof_ruleRemoval (Some _) _ _ _ _     =>
        Ko _  (Todo TTrsTerminationProof_ruleRemoval)
      | RelativeTerminationProof_ruleRemoval None ocp rs trs p =>
        Match rel_trsTerminationProof_ruleRemoval R D ocp With D' ===>
              relTerminationProof R D' p
      | RelativeTerminationProof_semlab _ _ _ _                   =>
        Ko _ (Todo TTrsTerminationProof_semlab)
      | RelativeTerminationProof_unlab _ _ _                      =>
        Ko _ (Todo TTrsTerminationProof_unlab)
      | RelativeTerminationProof_stringReversal rs rs2 dp         =>
        Ko _ (Todo TTrsTerminationProof_stringReversal)
        (*if   brules_preserve_vars R &&
           brules_preserve_vars D &&
           @bis_unary (Sig a) (symbol_in_rules rs)
        then relTerminationProof (reverse_trs R) (reverse_trs D) dp
        else Ko _ (Todo TTrsTerminationProof_stringReversal)*)
      | RelativeTerminationProof_relativeTerminationAssumption _ =>
        Ko _ (Todo TTrsTerminationProof_terminationAssumption)
      | _  => Ko _ (Todo Todo1)
    end. 

    (***********************************************************************)
    (** Structure proof of relation TRS:
       1. relation TRS is empty.
       2. Rule removal.  *)

  Variable nat_of_string : string -> nat.

  Lemma rel_TerminationProof_ok : forall a R D t i,
    sys_of_input a nat_of_string i = Ok (Red_mod R D) ->
    relTerminationProof R D t      = OK -> WF (red_mod R D).
  
  Proof.
    intros a R D t i H Hs. revert R D H Hs. intros R D Hs.
    clear Hs i. revert t R D.
    induction t; intros R D Hm; simpl in Hm; try discr.
    (** Correctness proof when termination proof is empty. *)
    apply relTerminationProof_rIsEmpty_ok. apply Hm.
    apply relTerminationProof_rIsEmpty_ok. apply Hm.     
    (** Correctness proof of relative termination proof in the case of
       rule removal. *)
    destruct o; try discr.
    unfold rel_trsTerminationProof_ruleRemoval in Hm.
    destruct o0; try discr.
    unfold rel_orderingConstraintProof_redPair in Hm.
    destruct r; try discr. revert Hm.
    case_eq (rel_redPair_interpretation R D t2 l); intros l0 H Hm; try discr.
    eapply rel_redPair_interpretation_ok. apply H.
    apply IHt. apply Hm.
  Qed.

  (* TODO 
      (** Correctness proof of string reverse. *)
      case_eq (brules_preserve_vars R && brules_preserve_vars D &&
      bis_unary (Sig a) (symbol_in_rules t)); intros H; rewrite H in
      Hm; try discr.  do 2 rewrite andb_eq in H. do 2 destruct H.
      apply WF_red_mod_rev_eq.
      (** Proof that [is_unary] is true. *)
      rewrite <- bis_unary_ok. apply H0.
      (** Proof that [Fs_ok] *)
      Focus 2.
      (** Proof that rule_preserve_vars in D. *)
      rewrite <- brules_preserve_vars_ok. apply H1.
      Focus 2.
      (** Proof that rule_preserve_vars in R. *)
      rewrite <- brules_preserve_vars_ok. apply H.
      Focus 2.
     (* TODO *)
     (* Proof [red_mod (reverse_trs R) (reverse_trs D)] is well-founded *)
     *)
  
  (***********************************************************************)
  (* TODO: relative non termination Loop *)
  
  (***********************************************************************)
  (** ** Check that [R] is a violation of variable condition for
    [red_mod R D] *)

  Definition relativeNonTerminationProof_variableConditionViolated a
    (R D: arules a) :=
    if   brules_preserve_vars D
    then Ko _ (Error ErNotVariableConditionViolated)
    else OK.
  
  Lemma relativeNonTerminationProof_variableConditionViolated_ok: forall a
    (R D: arules a),
    relativeNonTerminationProof_variableConditionViolated R D = OK ->
    EIS (red_mod R D).
  
  Proof.
    intros a R D Hm.
    unfold relativeNonTerminationProof_variableConditionViolated in Hm.
    case_eq (brules_preserve_vars D); intros H; rewrite H in Hm; try discr.
    apply var_cond_mod.
    rewrite <- brules_preserve_vars_ok.
    rewrite <- false_not_true.
    apply H.
  Qed.
        
  (***********************************************************************)
  (** ** Check that [p] is a valid non-termination proof for [red_mod
       R D]. Checking that there is a loop in a TRS. *)
  
  Require Import AModLoop List.
  
  Definition relativeNonTerminationProof_loop a (R D: arules a)
    (lo: cpf.loop) : result unit :=
    let '((t, ls), _, c) := lo in
    Match color_term a nat_of_string t With t ===>
          (* FIXME: (ls: nil) == list (list rewriteSequence) *)
    Match color_list_mod_data nat_of_string a (ls::nil) With mds ===>
    Match color_rewriteSteps nat_of_string  a  ls       With ds ===>
    let pos := color_position_of_context c in
    if   is_mod_loop R D t mds ds pos
    then OK
    else Ko _ (Error ErrelativeNonTerminationProof_loop).
  
  Lemma relativeNonTerminationProof_loop_ok: forall a (R D : arules a) l,
    relativeNonTerminationProof_loop R D l = OK -> EIS (red_mod R D).
  
  Proof.
    intros a R D l Hm.
    unfold relativeNonTerminationProof_loop in Hm.
    destruct l; simpl; try discr.
    destruct p; simpl; try discr.
    destruct r; simpl; try discr.
    case_eq (color_term a nat_of_string t);
      intros t1 H1; rewrite H1 in Hm; try discr.
    case_eq (color_rewriteSteps nat_of_string a l);
      intros ds H2; rewrite H2 in Hm; try discr.
    case_eq (color_list_mod_data nat_of_string a (l :: Datatypes.nil));
      intros mds H3; rewrite H3 in Hm; try discr.
    case_eq (is_mod_loop R D t1 mds ds (color_position_of_context c));
      intros H4; rewrite H4 in Hm; try discr.
    set (p := color_position_of_context c).
    apply is_mod_loop_correct with (t:=t1)(mds:=mds)(ds:=ds)(p:=p).
    apply H4.
    case_eq (color_list_mod_data nat_of_string a (l::Datatypes.nil));
      intros l0 H3; rewrite H3 in Hm; try discr.
  Qed.
  
  (***********************************************************************)
  (** ** Check that [p] is a valid termination proof for [red_mod R D] 

       [variableConditionViolated]: There is a rule where the lhs is a
       variable, or the rhs contains variables not occuring in the lhs.
       
       [loop]: a loop is given by a (non-empty) rewrite-sequence t0 ->+
       tn where additional tn = C[t0 sigma]. *)
  
  Definition relativeNonterminationProof a (R D: arules a) p : result unit :=
    match p with
      | RelativeNonterminationProof_loop lo                   =>
        relativeNonTerminationProof_loop R D lo
      | RelativeNonterminationProof_trsNonterminationProof _  =>
        Ko _ (Todo TRelativeNonterminationProof_trsNonterminationProof)
      | RelativeNonterminationProof_variableConditionViolated =>
        relativeNonTerminationProof_variableConditionViolated R D
      | RelativeNonterminationProof_ruleRemoval _ _ _          =>
        Ko _ (Todo TRelativeNonterminationProof_ruleRemoval)
      | RelativeNonterminationProof_nonterminationAssumption _ =>
        Ko _ (Todo TRelativeNonterminationProof_nonterminationAssumption)
    end.
    
End S.