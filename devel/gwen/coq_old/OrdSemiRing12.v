(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski, 2007-04-14

* Semi-ring equipped with two (strict and non-strict) orders.

*)

Require Export SemiRing2.
Require Import Morphisms RelDec SN RelExtras2 NatUtil LogicUtil Max ZUtil
  RelUtil Min Setoid.

(***********************************************************************)
(** ** Semi-rings equipped with orders. *)

Section OrdSemiRingType.

  Variable e: Eqset.
  Variable s : SemiRingType e.

  Notation eqA := (eqA e).
  Notation "x =A= y" := (eqA x y) (at level 70).

  Notation Aplus := (Aplus e s).
  Notation "x + y " := (Aplus x y).

  Notation Amult := (Amult e s).
  Notation "x * y" := (Amult x y).

  Record OrdSemiRingType := mkOrdSemiRingType {
    gt : relation A;
    ge : relation A;

    eq_ge_compat : forall x y, x =A= y -> ge x y;
    ge_refl : reflexive ge;
    ge_trans : transitive ge;
    gt_trans : transitive gt;
    
    ge_dec : rel_dec ge;
    gt_dec : rel_dec gt;
    
    ge_gt_compat : forall x y z, ge x y -> gt y z -> gt x z;
    ge_gt_compat2 : forall x y z, gt x y -> ge y z -> gt x z;

    plus_gt_compat : forall m n m' n',
      gt m m' -> gt n n' -> gt (m + n) (m' + n');
    plus_ge_compat : forall m n m' n',
    ge m m' -> ge n n' -> ge (m + n) (m' + n');

    mult_ge_compat : forall m n m' n',
    ge m m' -> ge n n' -> ge (m * n) (m' * n')
  }.

  Hint Resolve ge_refl : arith.

End OrdSemiRingType.

Section OrdSemiRing.

  Variable e: Eqset.

  Variable s: SemiRingType e.

  Variable o : OrdSemiRingType e s.

  Notation eqA := (eqA e).

  Notation sid_theoryA := (sid_theoryA e).

  Notation ge := (ge e s o).
  Notation "x >>= y" := (ge x y) (at level 70).

  Notation ge_refl := (ge_refl e s o).

  Notation ge_trans := (ge_trans e s o).

  Add Setoid A eqA sid_theoryA as A_Setoid.

  Add Relation A ge
    reflexivity proved by ge_refl
    transitivity proved by ge_trans
      as ge_rel.

  Instance ge_mor : Proper (eqA ==> eqA ==> iff) ge.

  Proof.
    intros x y H x0 y0 H0. intuition.
    trans x. apply (eq_ge_compat e s).
    sym. hyp.
    trans x0. hyp. apply (eq_ge_compat e s). hyp.
    trans y. apply eq_ge_compat. hyp.
    trans y0. hyp. apply eq_ge_compat. sym. hyp.
  Qed.

  Notation gt := (gt e s o).
  Notation "x >> y" := (gt x y) (at level 70).

  Notation gt_trans := (gt_trans e s o).

  Add Relation A gt
    transitivity proved by gt_trans
      as gt_rel.

  Instance gt_mor : Proper (eqA ==> eqA ==> iff) gt.

  Proof.
    intros x y H x0 y0 H0.
    intuition. apply ge_gt_compat2 with x0. 2: apply eq_ge_compat; hyp.
    apply ge_gt_compat with x. apply eq_ge_compat. sym. hyp. hyp.
    apply ge_gt_compat2 with y0. 2: apply eq_ge_compat; sym; hyp.
    apply ge_gt_compat with y. apply eq_ge_compat. hyp. hyp.
  Qed.

End OrdSemiRing.

(***********************************************************************)
(** ** Natural numbers semi-rings with natural order. *)

Section NOrdSemiRingT.

  Definition gtN := Peano.gt.
  Definition geN := Peano.ge.

  Lemma eq_ge_compatp : forall x y, x = y -> x >= y.

  Proof.
    intros. subst. apply le_refl.
  Qed.

  Lemma ge_reflN : reflexive geN.

  Proof.
    intro m. unfold geN. auto with arith.
  Qed.

  Lemma ge_transN : transitive geN.

  Proof.
    intros m n p. unfold geN, Peano.ge. eauto with arith.
  Qed.

  Lemma ge_antisymN : antisymmetric geN.

  Proof.
    intros m n. unfold geN, Peano.ge. auto with arith.
  Qed.

  Definition gt_irrefl := Gt.gt_irrefl.

  Definition gt_transN := Gt.gt_trans.

  Definition ge_decN := ge_dec.

  Definition gt_decN := gt_dec.

  Lemma gt_WF : WF gtN.

  Proof.
    apply wf_transp_WF. 
    apply well_founded_lt_compat with (fun x:nat => x). auto.
  Qed.

  Lemma ge_gt_compatN : forall x y z, x >= y -> y > z -> x > z.

  Proof.
    intros. apply le_gt_trans with y; hyp.
  Qed.

  Lemma ge_gt_compat2N : forall x y z, x > y -> y >= z -> x > z.

  Proof.
    intros. apply gt_le_trans with y; hyp.
  Qed.

  Lemma plus_gt_compatN : forall m n m' n',
    m > m' -> n > n' -> m + n > m' + n'.

  Proof.
    intros. omega.
  Qed.

  Lemma plus_gt_compat_lN : forall m n m' n',
    m > m' -> n >= n' -> m + n > m' + n'.

  Proof.
    intros. omega.
  Qed.

  Lemma plus_gt_compat_rN : forall m n m' n',
    m >= m' -> n > n' -> m + n > m' + n'.

  Proof.
    intros. omega.
  Qed.

  Lemma plus_ge_compatN : forall m n m' n',
    m >= m' -> n >= n' -> m + n >= m' + n'.

  Proof.
    intros. unfold Peano.ge.
    apply plus_le_compat; hyp.
  Qed.

  Lemma mult_ge_compatN : forall m n m' n',
    m >= m' -> n >= n' -> m * n >= m' * n'.

  Proof.
    intros. unfold Peano.ge.
    apply mult_le_compat; hyp.
  Qed.

End NOrdSemiRingT.

(***********************************************************************)
(** ** BigN natural numbers semi-rings with natural order. *)

Section BigNOrdSemiRingT.

  Open Local Scope bigN_scope.

  Require Import BigNUtil.

  Definition gtbn x y := BigN.lt y x.

  Definition gebn x y := BigN.le y x.

  Definition eqAbn := BigN.eq.

  Lemma eq_ge_compatbn : forall x y, eqAbn x y -> x >= y.

  Proof.
    intros x y. unfold eqAbn, gebn, BigN.eq, BigN.le. omega.
  Qed.

  Definition ge_reflbn := BigN.le_refl.

  Lemma ge_transbn : transitive gebn.

  Proof.
    intros m n p. unfold gebn, BigN.le. omega.
  Qed.

  Lemma gt_transbn : transitive gtbn.

  Proof.
    intros m n p. unfold gtbn, BigN.lt. omega.
  Qed.

  Lemma ge_decbn : forall x y, {gebn x y}+{~gebn x y}.

  Proof.
    intros x y. unfold gebn, BigN.le. destruct (Z_le_dec [y] [x]).
    left. omega. right. omega.
  Qed.

  Lemma gt_decbn : forall x y, {gtbn x y}+{~gtbn x y}.

  Proof.
    intros. unfold gtbn, BigN.lt. destruct (Z_lt_dec [y] [x]).
    left. omega. right. omega.
  Qed.

  Definition gt_WFbn := wf_transp_WF BigN.lt_wf_0.

  Lemma ge_gt_compatbn : forall x y z, gebn x y -> gtbn y z -> gtbn x z.

  Proof.
    intros x y z. unfold gebn, gtbn, BigN.le, BigN.lt. omega.
  Qed.

  Lemma ge_gt_compat2bn : forall x y z, gtbn x y -> gebn y z -> gtbn x z.

  Proof.
    intros x y z. unfold gtbn, BigN.lt, gebn, BigN.le. omega.
  Qed.

  Lemma plus_gt_compatbn :
    forall m n m' n', gtbn m m' -> gtbn n n' -> gtbn (m + n) (m' + n').

  Proof.
    intros m n m' n'. apply BigN.add_lt_mono; hyp.
  Qed.

  Lemma plus_gt_compat_lbn :
    forall m n m' n', gtbn m m' -> gebn n n' -> gtbn (m + n) (m' + n').

  Proof.
    intros. apply BigN.add_lt_le_mono; hyp.
  Qed.

  Lemma plus_gt_compat_rbn :
    forall m n m' n', gebn m m' -> gtbn n n' -> gtbn (m + n) (m' + n').

  Proof.
    intros. apply BigN.add_le_lt_mono; hyp.
  Qed.

  Lemma plus_ge_compatbn :
    forall m n m' n', gebn m m' -> gebn n n' -> gebn (m + n) (m' + n').

  Proof.
    intros. apply BigN.add_le_mono; hyp.
  Qed.

  Lemma mult_ge_compatbn :
    forall m n m' n', gebn m m' -> gebn n n' -> gebn (m * n) (m' * n').

  Proof.
    intros. apply BigN.mul_le_mono; hyp.
  Qed.

  Lemma mult_lt_compat_lrbn : forall i j k l,
    i <= j -> j > 0 -> k < l -> i * k < j * l.

  Proof.
    intros. case (bigN_le_gt_dec j i); intro.
    assert (i==j). apply BigN.le_antisymm; hyp. rewrite H2.
    rewrite <- (BigN.mul_lt_mono_pos_l _ _ _ H0). hyp.
    apply BigN.mul_lt_mono; hyp.
  Qed.

  Close Scope bigN_scope.

End BigNOrdSemiRingT.

(***********************************************************************)
(** ** Arctic ordered semi-ring. *)

Section ArticOrdSemiRingT.

  Open Scope nat_scope.

  Definition gtr m n :=
    match m, n with
    | MinusInf, _ => False
    | Pos _, MinusInf => True
    | Pos m, Pos n => m > n
    end.

  Definition ger m n := gtr m n \/ m = n.

  Lemma eq_ge_compatr : forall x y, x = y -> ger x y.

  Proof.
    unfold ger. intuition.
  Qed.

  Lemma gt_irreflr : irreflexive gtr.

  Proof.
    intros x xx. destruct x.
    unfold gtr in xx. omega.
    auto.
  Qed.

  Lemma gt_transr : transitive gtr.

  Proof.
    intros x y z xy yz. 
    destruct x; destruct y; destruct z; try solve [ auto | contr ].
    simpl in *.
    omega.
  Qed.

  Lemma gt_asymr : forall x y, gtr x y -> ~gtr y x.

  Proof.
    intros x y xy. 
    destruct x; destruct y; simpl in *; try solve [auto | omega].
  Qed.

  Lemma gt_decr : rel_dec gtr.

  Proof.
    unfold rel_dec. intros.
    unfold gtr.
    destruct x; destruct y; simpl; auto.
    destruct (NatUtil.gt_dec n n0) ; auto.
  Defined.

  Lemma gt_WFr : WF gtr.

  Proof.
    apply wf_transp_WF. 
    apply well_founded_lt_compat with 
      (fun x => 
        match x with
        | Pos x => x + 1
        | MinusInf => 0
        end).
    intros. destruct x; destruct y; 
      solve [auto with arith | elimtype False; auto].
  Qed.

  Lemma ge_reflr : reflexive ger.

  Proof.
    intro m. right. trivial.
  Qed.

  Lemma ge_transr : transitive ger.

  Proof.
    intros x y z xy yz. destruct xy. destruct yz.
    left. apply (gt_transr x y z); hyp.
    subst y. left. hyp.
    subst x. hyp.
  Qed.

  Lemma ge_antisymr : antisymmetric ger.

  Proof.
    intros x y xy yx. destruct xy. destruct yx.
    absurd (gtr y x). apply gt_asymr. hyp. hyp.
    auto. hyp.
  Qed.

  Lemma ge_decr : rel_dec ger.

  Proof.
    intros x y. destruct (gt_decr x y).
    left. left. hyp.
    destruct (eqA_decr x y).
    left. right. hyp.
    right. intro xy. destruct xy; auto.
  Defined.

  Notation "x >>= y" := (ger x y) (at level 70).
  Notation "x >> y" := (gtr x y) (at level 70).

  Lemma ge_gt_eqr : forall x y, x >>= y -> x >> y \/ x = y.

  Proof.
    destruct 1; auto.
  Qed.

  Lemma ge_gt_compatr : forall x y z, x >>= y -> y >> z -> x >> z.

  Proof.
    intros. destruct y. destruct x. destruct z.
    unfold gtr, ger in *. destruct H. 
    simpl in H. omega.
    injection H. intro. subst n0. hyp.
    auto.
    elimtype False. destruct H. auto. discr.
    elimtype False. destruct H. auto. subst x.  auto.
  Qed.

  Lemma ge_gt_compat2r : forall x y z, x >> y -> y >>= z -> x >> z.

  Proof.
    unfold ger, gtr. destruct x; destruct y; destruct z; simpl; intuition.
    inversion H1. subst. hyp. discr.
  Qed.

  Lemma pos_ordr : forall m n,
    Pos m >>= Pos n -> Peano.ge m n.

  Proof.
    intros. inversion H; simpl in H0. omega.
    injection H0. omega.
  Qed.

  Notation "x + y" := (Aplusr x y).
  Notation "x * y" := (Amultr x y).

  Lemma plus_inf_decr : forall m n,
    { exists p, (m = Pos p \/ n = Pos p) /\ m + n = Pos p} +
    { m + n = MinusInf /\ m = MinusInf /\ n = MinusInf }.

  Proof.
    intros. destruct m. 
    left. destruct n.
    exists (max n0 n). split.
    apply max_case; auto. trivial.
    exists n0. auto.
    destruct n.
    left. exists n. auto.
    right. auto.
  Qed.

  Lemma mult_inf_decr : forall m n,
    { exists mi, exists ni,
      m = Pos mi /\ n = Pos ni /\ m * n = Pos (mi + ni) } +
    { m * n = MinusInf /\ (m = MinusInf \/ n = MinusInf) }.

  Proof.
    intros. destruct m. destruct n.
    left. exists n0. exists n. repeat split. 
    right. auto.
    right. auto.
  Qed.

  Lemma ge_impl_pos_ger : forall m n, (m >= n)%nat -> Pos m >>= Pos n.

  Proof.
    intros. destruct (lt_eq_lt_dec m n) as [[m_n | m_n] | m_n].
    elimtype False. omega.
    subst m. right. refl.
    left. trivial.
  Qed.

  Lemma pos_ge_impl_ger : forall m n, Pos m >>= Pos n -> (m >= n)%nat.

  Proof.
    intros. destruct H. auto with arith. 
    injection H. intro. subst m. auto with arith.
  Qed.

  Ltac arctic_ord :=
    match goal with
    | H: MinusInf >> Pos _ |- _ =>
        contr
    | H: MinusInf >>= Pos _ |- _ =>
        destruct H; [ contr | discr ]
    | H: Pos ?m >>= Pos ?n |- _ =>
        assert ((m >= n)%nat); 
          [ apply pos_ge_impl_ger; hyp 
          | clear H; arctic_ord
          ]
    | |- Pos _ >>= MinusInf => left; simpl; trivial
    | |- Pos ?m >>= Pos ?n => apply ge_impl_pos_ger
    | _ => try solve [contr | discr]
    end.

  Lemma plus_gt_compatr : forall m n m' n',
    m >> m' -> n >> n' -> m + n >> m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    apply max_gt_compat; hyp.
    unfold Peano.gt. apply lt_max_intro_l. hyp.
    unfold Peano.gt. apply lt_max_intro_r. hyp.
  Qed.

  Lemma plus_ge_compatr : forall m n m' n',
    m >>= m' -> n >>= n' -> m + n >>= m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    apply max_ge_compat; hyp.
    unfold Peano.ge. apply le_max_intro_l. hyp.
    unfold Peano.ge. apply le_max_intro_r. hyp.
  Qed.

  Lemma mult_ge_compatr : forall m n m' n',
    m >>= m' -> n >>= n' -> m * n >>= m' * n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    omega.
  Qed.

  Lemma not_minusInf_ge_A1 : forall a, a <> MinusInf -> a >>= A1r.

  Proof.
    intros. destruct a. destruct n.
    right. refl.
    left. simpl. omega.
    tauto.
  Qed.

  Lemma ge_A1_not_minusInf : forall a, a >>= A1r -> a <> MinusInf.

  Proof.
    intros. destruct a. 
    discr.
    destruct H. contr. discr.
  Qed.

Close Scope nat_scope.

End ArticOrdSemiRingT.

(***********************************************************************)
(** ** Arctic below-zero ordered semi-ring. *)

Section ArticBZOrdSemiRingT.

  Local Open Scope Z_scope.

  Definition gtrbz m n :=
    match m, n with
    | MinusInfBZ, _ => False
    | Fin _, MinusInfBZ => True
    | Fin m, Fin n => m > n
    end.

  Definition gerbz m n := gtrbz m n \/ m = n.

  Definition is_above_zero v :=
    match v with
      | MinusInfBZ => false
      | Fin z => is_not_neg z
    end.

  Lemma is_above_zero_ok :
    forall v, is_above_zero v = true <-> gerbz v (Fin 0).

  Proof.
    intro. destruct v; simpl; intuition.
    destruct z. right. refl. left. simpl. auto with zarith. discr.
    rewrite is_not_neg_ok. destruct H. simpl in H. auto with zarith.
    inversion H. auto with zarith.
    destruct H. simpl in H. contr. discr.
  Qed.

  Lemma eq_ge_compatrbz : forall x y, x = y -> gerbz x y.

  Proof.
    unfold gerbz. intuition.
  Qed.

  Lemma ge_reflrbz : reflexive gerbz.

  Proof.
    intro m. right. trivial.
  Qed.

  Lemma gt_transrbz : transitive gtrbz.

  Proof.
    intros m n p mn np.
    destruct m; auto. 
    destruct n. 
    destruct p; auto.
    simpl in *. omega.
    simpl in *. tauto.
  Qed.

  Lemma gt_irreflrbz : irreflexive gtrbz.

  Proof.
    intros x xx. destruct x.
    unfold gtrbz in xx. omega.
    auto.
  Qed.

  Lemma gt_asymrbz : forall m n, gtrbz m n -> ~gtrbz n m.

  Proof.
    intros. destruct m; destruct n; try tauto.
    simpl in *. omega.
  Qed.

  Lemma ge_transrbz : transitive gerbz.

  Proof.
    intros m n p mn np. 
    destruct mn. 
    destruct np.
    left. apply (gt_transrbz m n p); hyp.
    rewrite <- H0. left. trivial.
    rewrite H. trivial.
  Qed.

  Lemma ge_antisymrbz : antisymmetric gerbz.

  Proof.
    intros m n mn nm. destruct mn; auto. destruct nm; auto.
    absurd (gtrbz n m). apply gt_asymrbz. hyp. hyp.
  Qed.

  Lemma gt_decrbz : rel_dec gtrbz.

  Proof.
    intros x y.
    destruct x; destruct y; simpl; auto.
    destruct (Z_lt_dec z0 z); [left | right]; omega.
  Defined.

  Lemma ge_decrbz : rel_dec gerbz.

  Proof.
    intros x y.
    destruct (gt_decrbz x y).
    left. left. trivial.
    destruct (eqA_decrbz x y).
    left. right. trivial.
    right. intro xy. destruct xy; auto.
  Defined.

  Notation "x + y" := (Aplusrbz x y).
  Notation "x * y" := (Amultrbz x y).
  Notation "x >> y" := (gtrbz x y) (at level 70).
  Notation "x >>= y" := (gerbz x y) (at level 70).

  Lemma ge_gt_eqrbz : forall x y, x >>= y -> x >> y \/ x = y.

  Proof.
    destruct 1; auto.
  Qed.

  Lemma ge_gt_compatrbz : forall x y z, x >>= y -> y >> z -> x >> z.

  Proof.
    intros. destruct y. destruct x. destruct z.
    unfold gtrbz, gerbz in *. destruct H. 
    simpl in H. omega.
    injection H. intro. subst z0. hyp.
    auto.
    elimtype False. destruct H. auto. discr.
    elimtype False. destruct H. auto. subst x.  auto.
  Qed.

  Lemma ge_gt_compat2rbz : forall x y z, x >> y -> y >>= z -> x >> z.

  Proof.
    unfold gerbz, gtrbz. destruct x as [x|]; destruct y as [y|];
      try destruct z as [z|]; simpl; intuition.
    inversion H1. subst. hyp. discr.
  Qed.

  Lemma fin_ge_Zgerbz : forall m n,
    Fin m >>= Fin n -> (m >= n)%Z.
 
  Proof.
    intros. inversion H; simpl in H0. omega.
    injection H0. omega.
  Qed.

  Lemma plus_inf_dec : forall m n,
    { exists p, (m = Fin p \/ n = Fin p) /\ m + n = Fin p} +
    { m + n = MinusInfBZ /\ m = MinusInfBZ /\ n = MinusInfBZ }.

  Proof.
    intros. destruct m. 
    left. destruct n.
    exists (Zmax z z0). split.
    apply Zmax_case; auto. trivial.
    exists z. auto.
    destruct n.
    left. exists z. auto.
    right. auto.
  Qed.

  Lemma mult_inf_dec : forall m n,
    {exists mi, exists ni, m = Fin mi /\ n = Fin ni /\ m * n = Fin (mi + ni)}
    + {m * n = MinusInfBZ /\ (m = MinusInfBZ \/ n = MinusInfBZ)}.

  Proof.
    intros. destruct m. destruct n.
    left. exists z. exists z0. repeat split.
    right. auto.
    right. auto.
  Qed.

  Lemma minusInf_ge_min : forall a, a >>= MinusInfBZ.

  Proof.
    intros. destruct a. left. simpl. trivial.
    right. refl.
  Qed.

  Lemma ge_impl_fin_ge : forall m n, (m >= n)%Z -> Fin m >>= Fin n.

  Proof.
    intros. destruct (Z_le_lt_eq_dec n m). omega.
    left. simpl. omega.
    subst n. right. refl.
  Qed.

  Lemma fin_ge_impl_ge : forall m n, Fin m >>= Fin n -> (m >= n)%Z.

  Proof.
    intros. destruct H. 
    simpl in H. omega.
    injection H. intro. subst m. omega.
  Qed.

  Ltac arctic_ord :=
    match goal with
    | H: MinusInfBZ >> Fin _ |- _ =>
        contr
    | H: MinusInfBZ >>= Fin _ |- _ =>
        destruct H; [ contr | discr ]
    | H: Fin ?m >>= Fin ?n |- _ =>
        assert ((m >= n)%Z); 
          [ apply fin_ge_impl_ge; hyp 
          | clear H; arctic_ord
          ]
    | |- Fin _ >>= MinusInfBZ => left; simpl; trivial
    | |- Fin ?m >>= Fin ?n => apply ge_impl_fin_ge
    | _ => try solve [contr | discr]
    end.

  Lemma plus_gt_compatrbz : forall m n m' n',
    m >> m' -> n >> n' -> m + n >> m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord; simpl in *.
    apply Zmax_gt_compat; hyp.
    apply Zlt_gt. apply elim_lt_Zmax_l. omega.
    apply Zlt_gt. apply elim_lt_Zmax_r. omega.
  Qed.

  Lemma plus_ge_compatrbz : forall m n m' n',
    m >>= m' -> n >>= n' -> m + n >>= m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    apply Zmax_ge_compat; hyp.
    apply Zle_ge. apply elim_Zmax_l. omega.
    apply Zle_ge. apply elim_Zmax_r. omega.
  Qed.

  Lemma mult_ge_compatrbz : forall m n m' n',
    m >>= m' -> n >>= n' -> m * n >>= m' * n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    omega.
  Qed.

  Lemma arctic_plus_ge_monotone : forall (a b c : Arbz),
    a >>= c -> Aplusrbz a b >>= c.

  Proof.
    intros. destruct c.
    destruct a. destruct b. simpl. arctic_ord. 
    apply Zle_ge. apply elim_Zmax_l. omega.
    trivial.
    arctic_ord.
    apply minusInf_ge_min.
  Qed.

  Lemma ge_A1_not_minusInfrbz : forall a, a >>= A1rbz -> a <> MinusInfBZ.

  Proof.
    intros. destruct a. 
    discr.
    destruct H. contr. discr.
  Qed.

End ArticBZOrdSemiRingT.

(***********************************************************************)
(** ** Tropical ordered semi-ring. *)

Section TropicalOrdSemiRingT.

  Local Open Scope nat_scope.

  Definition gtt m n :=
    match m, n with
    | PlusInf, PlusInf => False
    | PlusInf, _ => True
    | TPos _, PlusInf => False
    | TPos m, TPos n => m > n
    end.

  Definition get m n := gtt m n \/ m = n.

  Lemma eq_ge_compatt : forall x y, x = y -> get x y.

  Proof.
    unfold get. intuition.
  Qed.

  Lemma gt_irreflt : irreflexive gtt.

  Proof.
    intros x xx. destruct x.
    unfold gtt in xx. omega.
    auto.
  Qed.

  Lemma gt_transt : transitive gtt.

  Proof.
    intros x y z xy yz. 
    destruct x; destruct y; destruct z; try solve [ auto | contr ].
    apply Arith.Gt.gt_trans with n0; auto.
  Qed.

  Lemma gt_asymt : forall x y, gtt x y -> ~gtt y x.

  Proof.
    intros x y xy. 
    destruct x; destruct y; simpl in *; try solve [auto | omega].
  Qed.

  Lemma gt_dect : rel_dec gtt.

  Proof.
    unfold rel_dec. intros.
    destruct x; destruct y; simpl; auto.
    destruct (NatUtil.gt_dec n n0); auto.
  Defined.

  Lemma gt_Fin_WF x : Acc (transp gtt) (TPos x).
  Proof.
    induction x using lt_wf_ind; apply Acc_intro; destruct y;
      auto || contr.
  Qed.

  Hint Resolve gt_Fin_WF.

  Lemma gt_WFt : WF gtt.

  Proof with auto; try contr.
    apply wf_transp_WF. intro x.
    destruct x...
    apply Acc_intro. intros. destruct y...
  Qed.

  Lemma ge_reflt : reflexive get.

  Proof.
    intro m. right. trivial.
  Qed.

  Lemma ge_transt : transitive get.

  Proof.
    intros x y z xy yz. destruct xy. destruct yz.
    left. apply (gt_transt x y z); hyp.
    subst y. left. hyp.
    subst x. hyp.
  Qed.

  Lemma ge_antisym : antisymmetric get.

  Proof.
    intros x y xy yx. destruct xy. destruct yx.
    absurd (gtt y x). apply gt_asymt. hyp. hyp.
    auto. hyp.
  Qed.

  Lemma ge_dect : rel_dec get.

  Proof.
    intros x y. destruct (gt_dect x y).
    left. left. hyp.
    destruct (eqA_dect x y).
    left. right. hyp.
    right. intro xy. destruct xy; auto.
  Defined.

  Notation "x + y" := (Aplust x y).
  Notation "x * y" := (Amultt x y).
  Notation "x >>= y" := (get x y) (at level 70).
  Notation "x >> y" := (gtt x y) (at level 70).

  Lemma ge_gt_eq : forall x y, x >>= y -> x >> y \/ x = y.

  Proof.
    destruct 1; auto.
  Qed.

  Lemma ge_gt_compatt : forall x y z, x >>= y -> y >> z -> x >> z.

  Proof with simpl; intuition.
    intros. 
    destruct y; destruct x; destruct z; auto...
    destruct H. simpl in *. omega. injection H. intros. subst...
    destruct H. contr. discr.
  Qed.

  Lemma ge_gt_compat2t : forall x y z, x >> y -> y >>= z -> x >> z.

  Proof.
    unfold get, gtt. destruct x; destruct y; destruct z; simpl; intuition;
    try discr.
    inversion H1. subst. hyp.
  Qed.

  Lemma pos_ord : forall m n,
    TPos m >>= TPos n -> Peano.ge m n.

  Proof.
    intros. inversion H; simpl in H0. omega.
    injection H0. omega.
  Qed.

  Lemma plus_inf_dect : forall m n,
    { exists p, (m = TPos p \/ n = TPos p) /\ m + n = TPos p} +
    { m + n = PlusInf /\ m = PlusInf /\ n = PlusInf }.

  Proof.
    intros. destruct m. 
    left. destruct n.
    exists (min n0 n). split.
    apply min_case; auto. trivial.
    exists n0. auto.
    destruct n.
    left. exists n. auto.
    right. auto.
  Qed.

  Lemma mult_inf_dect : forall m n,
    { exists mi, exists ni,
      m = TPos mi /\ n = TPos ni /\ m * n = TPos (mi + ni) } +
    { m * n = PlusInf /\ (m = PlusInf \/ n = PlusInf) }.

  Proof.
    intros. destruct m. destruct n.
    left. exists n0. exists n. repeat split. 
    right. auto.
    right. auto.
  Qed.

  Lemma ge_impl_pos_ge : forall m n, (m >= n)%nat -> TPos m >>= TPos n.

  Proof.
    intros. destruct (lt_eq_lt_dec m n) as [[m_n | m_n] | m_n].
    elimtype False. omega.
    subst m. right. refl.
    left. trivial.
  Qed.

  Lemma pos_ge_impl_ge : forall m n, TPos m >>= TPos n -> (m >= n)%nat.

  Proof.
    intros. destruct H. auto with arith. 
    injection H. intro. subst m. auto with arith.
  Qed.

  Ltac tropical_ord :=
    match goal with
    | H: _ >> PlusInf |- _ => contr
    | H: TPos _ >>= PlusInf |- _ =>
        destruct H; [ contr | discr ]
    | H: TPos ?m >>= TPos ?n |- _ =>
        assert ((m >= n)%nat); 
          [ apply pos_ge_impl_ge; hyp 
          | clear H; tropical_ord
          ]
    | |- PlusInf >>= TPos _ => left; simpl; trivial
    | |- TPos ?m >>= TPos ?n => apply ge_impl_pos_ge
    | _ => try solve [contr | discr]
    end.

  Lemma plus_gt_compatt : forall m n m' n',
    m >> m' -> n >> n' -> m + n >> m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; tropical_ord.
    apply min_gt_compat; hyp.
    unfold Peano.gt. apply lt_min_intro_l. hyp.
    unfold Peano.gt. apply lt_min_intro_r. hyp.
  Qed.

  Lemma plus_ge_compatt : forall m n m' n',
    m >>= m' -> n >>= n' -> m + n >>= m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; tropical_ord.
    apply min_ge_compat; hyp.
    unfold Peano.ge. apply le_min_intro_l. hyp.
    unfold Peano.ge. apply le_min_intro_r. hyp.
  Qed.

  Lemma mult_ge_compatt : forall m n m' n',
    m >>= m' -> n >>= n' -> m * n >>= m' * n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; tropical_ord.
    omega.
  Qed.

  Lemma not_minusInf_ge_A1t : forall a, a <> PlusInf -> a >>= A1t.

  Proof.
    intros. destruct a. destruct n.
    right. refl.
    left. simpl. omega.
    tauto.
  Qed.

  Lemma tropical_plus_inf_max : forall x, x <> PlusInf -> PlusInf >> x.
  Proof.
    intros. destruct x. simpl. auto.
    elimtype False. apply H. trivial.
  Qed.

End TropicalOrdSemiRingT.

(***********************************************************************)
(** ** Semi-ring of booleans with order True > False. *)

Section BOrdSemiRingT.

  Local Open Scope bool.

  Definition gtb x y := 
    match x, y with
    | true, false => True
    | _, _ => False
    end.

  Definition geb x y :=
    match x, y with
    | false, true => False
    | _, _ => True
    end.

  Lemma eq_ge_compatb : forall x y, x = y -> geb x y.

  Proof.
    unfold geb. destruct x; destruct y; auto. discr.
  Qed.

  Notation "x + y" := (Aplusb x y).
  Notation "x * y" := (Amultb x y).
  Notation "x >> y" := (gtb x y) (at level 70).
  Notation "x >>= y" := (geb x y) (at level 70).

  Lemma ge_reflb : reflexive geb.

  Proof.
    intro m. unfold geb. destruct m; auto.
  Qed.

  Lemma ge_transb : transitive geb.

  Proof.
    intros m n p. unfold geb. 
    destruct m; destruct n; destruct p; auto.
  Qed.

  Lemma ge_antisymb : antisymmetric geb.

  Proof.
    intros m n. unfold geb. 
    destruct m; destruct n; tauto.
  Qed.

  Lemma gt_irreflb : irreflexive gtb.

  Proof.
    intros x. unfold gtb. destruct x; tauto.
  Qed.

  Lemma gt_transb : transitive gtb.

  Proof.
    intros x y z. 
    destruct x; destruct y; destruct z; tauto.
  Qed.

  Lemma ge_decb : rel_dec geb.

  Proof.
    intros x y. destruct x; destruct y; simpl; tauto.
  Qed.

  Lemma gt_decb : rel_dec gtb.

  Proof.
    intros x y. destruct x; destruct y; simpl; tauto.
  Qed.

  (* open nat_scope to be able to use [well_founded_lt_compat] *)
  Local Open Scope nat_scope.

  Lemma gt_WFb : WF gtb.

  Proof.
    apply wf_transp_WF.  
    apply well_founded_lt_compat with 
      (fun x => 
        match x with
        | false => 0
        | true => 1
        end).
    destruct x; destruct y; unfold transp, gtb; 
      solve [tauto | auto with arith].
  Qed.

  Close Scope nat_scope.

  Lemma ge_gt_compatb : forall x y z, x >>= y -> y >> z -> x >> z.

  Proof.
    destruct x; destruct y; destruct z; simpl; tauto.
  Qed.

  Lemma ge_gt_compat2b : forall x y z, x >> y -> y >>= z -> x >> z.

  Proof.
    destruct x; destruct y; destruct z; simpl; tauto.
  Qed.

  Lemma plus_gt_compatb : forall m n m' n',
    m >> m' -> n >> n' -> m + n >> m' + n'.

  Proof.
    destruct m; destruct m'; destruct n; destruct n'; simpl; tauto.
  Qed.

  Lemma plus_ge_compatb : forall m n m' n',
    m >>= m' -> n >>= n' -> m + n >>= m' + n'.

  Proof.
    destruct m; destruct m'; destruct n; destruct n'; simpl; tauto.
  Qed.

  Lemma mult_ge_compatb : forall m n m' n',
    m >>= m' -> n >>= n' -> m * n >>= m' * n'.

  Proof.
    destruct m; destruct m'; destruct n; destruct n'; simpl; tauto.
  Qed.

End BOrdSemiRingT.