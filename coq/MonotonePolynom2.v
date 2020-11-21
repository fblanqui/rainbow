(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-25
- Adam Koprowski, 2008-05-27, 
    introduced distinction of weak/strong monotonicity

monotone polynomials
*)

Set Implicit Arguments.

Require Import Polynom2 PositivePolynom2 NaryFunction VecUtil LogicUtil
  ListUtil ListForall List ZUtil RelUtil NatUtil OrdSemiRing2 VecArith2 ListExtras.

Section S.

  Context {OR: OrderedRing}.

  Import OR_Notations.

  Notation "x >>= y" := (@or_ge _ x y) (at  level 70).
  Notation not_neg   := (fun z => z >>= 0).
  Notation D         := (sig not_neg).
  Notation inj       := (@exist s_typ not_neg _).
  Notation val       := (@proj1_sig s_typ not_neg).
  Notation vec       := (vector D). 
  Notation vals      := (@Vmap D s_typ val _).

  Definition Dgt x y := val x >> val y.
  Notation Dlt       := (transp Dgt).
  Definition Dge x y := val x >>= val y.
  Notation Dle       := (transp Dge).

  (* TODO : trans and refl *)

  (***********************************************************************)
  (** weak and strong monotony conditions *)

  Definition pweak_monotone n (p : poly n)  := coef_not_neg p.

  Definition pstrong_monotone n (p: poly n) :=
    pweak_monotone p /\ forall i (H: i < n), coef (mxi H) p >> 0.

  (***********************************************************************)
  (** alternative definition of monotony conditions *)

  Definition pstrong_monotone' n (p : poly n) := coef_not_neg p
   /\ forall i (H : i < n), exists p1, exists c, exists p2,
    c >> 0 /\ p = p1 ++ (c, mxi H) :: p2.

  Lemma pmonotone_imp_pmonotone' : forall n (p : poly n),
    pstrong_monotone p -> pstrong_monotone' p.

  Proof.
    intros n p (H1, H2).
    split. auto.
    intros i Hi. gen (H2 i Hi). clear H2.
    generalize dependent p. intro p. elim p. simpl in *.
    intros H1 H2. absurd (coef (mxi Hi) nil = 0).
    apply or_gt_0. hyp. simpl.
    refl.
    intros (c, m) p' Hrec H1. simpl in H1. gen H1. clear H1.
    intros (H1, H2). simpl.
    case_eq (monom_eq_dec (mxi Hi) m); intro Hm; simpl; intro H3.
    elim (or_gt_eq_ge_dec H1); clear H1. intro H1.

    (* If c > 0, it's easy to build the required elements *)
    intro H'. exists (pzero n). exists c. exists p'.
    split. hyp. simpl. subst m. refl.
    
    (* if c = 0, we must use the induction hypothesis *)
    intro Hc. rewrite Hc. subst m. rewrite Aplus_0_l. intros H4.
    elim (Hrec H2 H4). clear Hrec. intros p'1 H. elim H. intros c' H1.
    elim H1. clear H1. intros p'2 (Hc', Hp').
    exists ((c, mxi Hi) :: p'1).
    exists c'. exists p'2.
    split. hyp.
    rewrite Hp'. simpl in *. refl.
    
    intro H. elim (Hrec H2 H). clear H2. clear H.
    intros p'1 H. elim H. clear H. intros c' H. elim H. clear H.
    intros p'2 (Hc', Hp').
    exists ((c, m) :: p'1). exists c'. exists p'2.
    split. hyp.
    subst p'. simpl in *. refl.
  Qed.

  (***********************************************************************)
  (** correctness of monotony conditions *)
   
  Lemma meval_monotone_D : forall i (vi : vec i) (mi : monom i)
    j (vj : vec j) (mj : monom j) k x y (Hx : x >>= 0) (Hy : y >>= 0),
    x >>= y -> 
    meval (Vapp mi (Vcons k mj)) (vals (Vapp vi (Vcons (inj Hx) vj)))
    >>= meval (Vapp mi (Vcons k mj)) (vals (Vapp vi (Vcons (inj Hy) vj))).

  Proof.
    intros. do 2 rewrite Vmap_app. simpl Vmap. do 2 rewrite meval_app.
    apply or_mul_ge_mono_l. apply not_neg_meval. simpl in *.
    apply or_mul_ge_mono_r. apply not_neg_meval.
    apply or_power_ge_compat; hyp.
  Qed.

  Lemma coef_not_neg_monotone_peval_Dge : forall n (p : poly n)
    (H : coef_not_neg p), Vmonotone1 (peval_D p H) Dge.

  Proof.
    unfold Vmonotone1, Vmonotone, peval_D, Vmonotone_i, restrict, monotone.
    intros n p H_coef_not_neg i j Hij vi vj. destruct x as (x, Hx).
    destruct y as (y, Hy). simpl. intro Hxy.
    generalize dependent p. intro p. elim p.
    intro. simpl. apply or_ge_refl. 
    unfold coef_not_neg. intros (c, m) p' Hrec H_coef_not_neg.
    simpl in H_coef_not_neg. generalize H_coef_not_neg. clear H_coef_not_neg.
    intros (H_not_neg_c, H_coef_not_neg_p').
    generalize (Hrec H_coef_not_neg_p'). clear Hrec. intro H.
    lazy beta iota delta [peval]. fold peval.
    apply or_add_ge_compat. 
    2: apply H.
    clear H.
    apply or_mul_ge_mono_l. 
    hyp.
    rewrite (Vbreak_eq_app_cast Hij m).
    set (mi := (fst (Vbreak (n1:=i) (n2:=S j) (Vcast m (sym_equal Hij))))).
    set (mj := (snd (Vbreak (n1:=i) (n2:=S j) (Vcast m (sym_equal Hij))))).
    rewrite (VSn_eq mj).
    case Hij. simpl. repeat rewrite Vcast_refl.
    apply meval_monotone_D.
    hyp.
  Qed.

  Implicit Arguments coef_not_neg_monotone_peval_Dge [n p i j x y].

  Lemma pmonotone'_imp_monotone_peval_Dgt :
  forall n (p : poly n) (H: pstrong_monotone' p), 
    Vmonotone1 (peval_D p (proj1 H)) Dgt.
    
  Proof.
    intros n p (H_coef_pos_p, H_pmonotone_p) i j Hij.
    gen (H_pmonotone_p _ (i_lt_n (sym_equal Hij))).
    intro H. elim H. clear H. intros p1 H. elim H. clear H.
    intros c H. elim H. clear H. intros p2 (H, H'). subst p.
    gen (coef_not_neg_app _ _ H_coef_pos_p).
    intros (H_coef_pos_p1, H').
    gen (coef_not_neg_cons H'). clear H'. intros (H', H_coef_pos_p2).
    clear H'. unfold Vmonotone_i, Dgt, peval_D, monotone, restrict.
    intros vi vj. destruct x as (x, Hx). destruct y as (y, Hy). simpl.
    intro Hxy. clear H_coef_pos_p.
    do 2 rewrite peval_app.
    apply or_add_ge_gt_mono.
    gen (coef_not_neg_monotone_peval_Dge H_coef_pos_p1).
    unfold Vmonotone, Dge, peval_D, Vmonotone_i, restrict, monotone.
    intro H'.
    gen (H' _ _ Hij vi vj (exist not_neg x Hx) (exist not_neg y Hy)).
    simpl. clear H'. intro H'. apply H'. unfold or_ge. left. hyp.
    lazy beta iota delta [peval]. fold peval.
    apply or_add_gt_ge_mono.
    apply or_mul_gt_mono_l. hyp. do 2 rewrite meval_xi.
    do 2 rewrite Vmap_cast. case Hij. simpl.
    clear H_pmonotone_p. clear Hij. generalize dependent i. intro i. elim i.
    intro vi. rewrite (VO_eq vi). simpl. hyp.
    intros i' Hrec vi. rewrite (VSn_eq vi). simpl Vapp.
    simpl Vmap. simpl Vnth. gen (Hrec (Vtail vi)). clear Hrec. intro H'.
    assert (H'' : i_lt_n (refl_equal (i' + S j)%nat) = lt_S_n
     (@i_lt_n (S (i' + S j)) (S i') _ (refl_equal (S (i' + S j))))).
    apply lt_unique.
    rewrite <- H''. hyp.
    gen (coef_not_neg_monotone_peval_Dge H_coef_pos_p2).
    unfold Vmonotone, Dge, peval_D, Vmonotone_i, restrict, monotone.
    intro H'.
    gen (H' _ _ Hij vi vj (exist not_neg x Hx) (exist not_neg y Hy)).
    simpl. clear H'. intro H'. apply H'. unfold or_ge.
    left. hyp.
  Qed.

  Lemma pmonotone_imp_monotone_peval_Dgt : forall n (p : poly n) 
    (wm: pweak_monotone p) (sm: pstrong_monotone p),
     Vmonotone1 (peval_D p wm) Dgt.

  Proof.
    intros n p wm sm.
    gen (pmonotone'_imp_monotone_peval_Dgt (pmonotone_imp_pmonotone' sm)).
    unfold Vmonotone1, Vmonotone, Dgt, Vmonotone_i, peval_D, restrict, monotone.
    intros H0 i j Hij vi vj. destruct x as (x, Hx). destruct y as (y, Hy).
    simpl. intro Hxy.
    gen (H0 i j Hij vi vj (exist _ x Hx) (exist _ y Hy) Hxy).
    clear H0. simpl. intuition.
  Qed.

  (***********************************************************************)
  (** boolean functions for checking monotony conditions *)

  Definition bpweak_monotone    n (p : poly n) := bcoef_not_neg p.
  Definition bpweak_monotone_ok n (p : poly n) := bcoef_not_neg_ok p.

  Implicit Arguments mk_nat_lts [].
  Implicit Arguments mk_nat_lts_aux [].

  Require Import BoolUtil.

  Definition bpstrong_monotone n (p : poly n) :=
    bcoef_not_neg p &&
     forallb (fun x => or_bgt (coef (mxi (prf x)) p) 0) (mk_nat_lts n).

  Open Scope nat_scope.

  Lemma bpstrong_monotone_ok : forall n (p : poly n),
  bpstrong_monotone p = true <-> pstrong_monotone p.

  Proof.
    induction p.
    (* nil *)
    unfold pstrong_monotone, bpstrong_monotone, pweak_monotone. simpl.
    intuition. unfold mk_nat_lts in H. destruct n. absurd_arith.  
    (*destruct n; discr. *)
    (*destruct n. refl. ded (H1 n (le_n (S n))).*)
    Focus 3.
    (* cons *)
    destruct a. intuition.
    (* -> *)
    unfold pstrong_monotone, pweak_monotone.
    unfold bpstrong_monotone, bnot_neg in H1. Opaque coef. simpl in *. 
    rewrite !andb_eq in H1. intuition. change (bnot_neg s = true) in H1.
    rewrite <- bnot_neg_ok. hyp. rewrite <- bcoef_not_neg_ok. hyp.
    assert (In (mk_nat_lt H2) (mk_nat_lts n)). apply mk_nat_lts_complete.
    rewrite forallb_forall in H3. ded (H3 _ H5).
    rewrite or_bgt_ok in H6. simpl in H6. hyp.
    (* <- *)
    unfold pstrong_monotone, pweak_monotone in H1.
    unfold bpstrong_monotone, bcoef_not_neg. simpl in *.
    rewrite !andb_eq. intuition. rewrite bnot_neg_ok. hyp.
    change (bcoef_not_neg p = true). rewrite bcoef_not_neg_ok. hyp.
    rewrite forallb_forall. intros [i hi Hi]. simpl. rewrite or_bgt_ok.
    ded (H3 _ hi). hyp.
    Focus 2. destruct n. refl. ded (H1 n (le_n (S n))). simpl in *.
    rewrite forallb_forall. intros. rewrite or_bgt_ok. apply H.
    rewrite forallb_forall in H.
    rewrite <- or_bgt_ok. eapply H. 

  Admitted.

  (***********************************************************************)
  (** check monotony conditions *)
  
  Definition is_pos_monom n (cm : s_typ * monom n) :=
    let (c, _) := cm in not_neg c.

End S.