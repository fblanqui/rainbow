(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-05-20
- Frederic Blanqui, 2005-02-25

polynomials with non-negative integers as coefficients
*)

Set Implicit Arguments.

Require Import Polynom2 OrdSemiRing2 NaryFunction ListForall VecUtil List
  LogicUtil Relations BoolUtil Morphisms.

Section S.

  Context {OR: OrderedRing}.

  Import OR_Notations.

  Notation "x >>= y" := (@or_ge _ x y) (at  level 70).
  Notation not_neg   := (fun z => z >>= 0).
  Notation D         := (sig not_neg).
  Notation val       := (@proj1_sig s_typ not_neg).
  Notation vec       := (vector D). 
  Notation vals      := (@Vmap D s_typ val _).
  
  Lemma not_neg_meval : forall n (m: monom n) (v: vec n),
    meval m (vals v) >>= 0.

  Proof.
    induction n; intros; simpl. unfold or_ge. left.
    apply or_one_gt_zero. 
    VSntac m. VSntac v. simpl. apply or_mul_ge_0. 
    apply or_power_ge_0. destruct (Vhead v).
    simpl. hyp.
    apply IHn.
  Qed.

  Lemma preserv_not_neg_meval :
    forall n (m : monom n), preserv not_neg (meval m).

  Proof.
  intros n m v Hv. rewrite (Vmap_proj1_sig Hv). apply not_neg_meval.
  Qed.

  Definition meval_D n (m : monom n) := restrict (preserv_not_neg_meval m).

  (***********************************************************************)
  (** predicate saying that all pseudo-coefficients are non-negative *)

  Definition coef_not_neg (n: nat) (p: poly n) :=
    lforall (fun x => fst x >>= 0) p.

  Definition bcoef_not_neg n (p: poly n) :=
    forallb (fun x => bnot_neg (fst x)) p.

  Lemma bcoef_not_neg_ok : forall n (p: poly n),
    bcoef_not_neg p = true <-> coef_not_neg p.

  Proof.
  intros n p. apply forallb_lforall. intros [z m]. apply bnot_neg_ok. 
  Qed.

  (***********************************************************************)
  (** the predicate coef_not_neg is preserved by operations on polynomials *)

  Lemma coef_not_neg_coef : forall n p (m: monom n), 
    coef_not_neg p -> coef m p >>= 0.

  Proof.
    induction p; intros; simpl. apply or_ge_refl.   
    destruct a. simpl in H. destruct H.
    case (monom_eq_dec m t); intro. assert (coef m p >>= 0). apply IHp. hyp.
    apply or_add_ge_0; hyp. apply IHp. hyp.
  Qed.

  Lemma coef_not_neg_cons : forall n c (m : monom n) (p : poly n),
    coef_not_neg ((c,m)::p) -> c >>= 0 /\ coef_not_neg p.

  Proof.
  unfold coef_not_neg. intros n c m p. simpl. auto.
  Qed.

  Lemma coef_not_neg_app : forall (n: nat) p1 p2,
    @coef_not_neg n (p1 ++ p2) -> coef_not_neg p1 /\ coef_not_neg p2.

  Proof.
    unfold coef_not_neg. intros n p1 p2. simpl.
    rewrite lforall_app. intuition.
  Qed.

  Implicit Arguments coef_not_neg_app [n p1 p2].

  Lemma coef_not_neg_mpmult : forall n c (m : monom n) (p: poly n),
    c >>= 0 -> coef_not_neg p -> coef_not_neg (mpmult c m p).

  Proof.
    induction p; intros; simpl. exact I. 
    destruct a. simpl.
    simpl in H0. destruct H0. split. 
    apply or_mul_ge_0; hyp.
    apply IHp; hyp.
  Qed.

  Lemma not_neg_peval : forall n (p: poly n) v, 
    coef_not_neg p -> peval p (vals v) >>= 0.

  Proof.
    induction p; intros; simpl. apply or_ge_refl. 
    destruct a. simpl in H. destruct H.
    apply or_add_ge_0. apply or_mul_ge_0. hyp.
    apply not_neg_meval. apply IHp. hyp.
  Qed.

  Lemma preserv_not_neg_peval : forall n (p: poly n),
    coef_not_neg p -> preserv not_neg (peval p).

  Proof.
    intros. unfold preserv. intros v Hv.
    rewrite (Vmap_proj1_sig Hv). apply not_neg_peval. hyp.
  Qed.

  Definition peval_D n (p: poly n) (H : coef_not_neg p) :=
    restrict (preserv_not_neg_peval p H).

  Implicit Arguments peval_D [n p].

  Lemma val_peval_D : forall n (p : poly n) (H : coef_not_neg p) (v : vec n),
    val (peval_D H v) == peval p (vals v).

  Proof.
    intros. simpl in *.
    intuition.
  Qed.

  Lemma coef_not_neg_mpadd : forall n c (m : monom n) p,
    c >>= 0 -> coef_not_neg p -> coef_not_neg (mpadd c m p).

  Proof.
    induction p; intros; simpl. auto. destruct a.
    simpl in H0. destruct H0.
    case (monom_eq_dec m t); simpl; intuition.
    apply or_add_ge_0. hyp. hyp.
  Qed.

  Lemma coef_not_neg_add : forall n (p1 p2 : poly n),
    coef_not_neg p1 -> coef_not_neg p2 -> coef_not_neg (padd p1 p2).

  Proof.
    induction p1; intros; simpl. hyp. destruct a. simpl in H. destruct H.
    apply coef_not_neg_mpadd. hyp. apply IHp1; hyp.
  Qed.

  Lemma coef_not_neg_mult : forall n (p1 p2 : poly n),
    coef_not_neg p1 -> coef_not_neg p2 -> coef_not_neg (pmult p1 p2).

  Proof.
    induction p1; intros; simpl. exact I. destruct a. simpl in H. destruct H.
    apply coef_not_neg_add. apply coef_not_neg_mpmult; hyp. apply IHp1; hyp.
  Qed.

  Lemma coef_not_neg_power : forall k n (p : poly n),
    coef_not_neg p -> coef_not_neg (ppower p k).

  Proof.
    induction k; intros; simpl. intuition. unfold osr_ge. left.
    apply or_one_gt_zero.  
    apply coef_not_neg_mult. hyp.
    apply IHk. hyp.
  Qed.

  Lemma coef_not_neg_mcomp : forall k n (m : monom n) (ps : vector (poly k) n),
    Vforall (@coef_not_neg k) ps -> coef_not_neg (mcomp m ps).

  Proof.
    induction n; intros; simpl. intuition. unfold osr_ge. left.
    apply or_one_gt_zero.
    VSntac ps. simpl. rewrite H0 in H.
    simpl in H. destruct H. apply coef_not_neg_mult. apply coef_not_neg_power.
    hyp. apply IHn. hyp.
  Qed.

  Lemma coef_not_neg_cpmult : forall n c (p : poly n),
    c >>= 0 -> coef_not_neg p -> coef_not_neg (cpmult c p).

  Proof.
    induction p; intros; simpl. exact I. 
    destruct a. simpl. simpl in H0. intuition.
    apply or_mul_ge_0. hyp. hyp.
  Qed.

  Lemma coef_not_neg_pcomp : forall n k (p : poly n) (ps : vector (poly k) n),
    coef_not_neg p -> Vforall (@coef_not_neg k) ps -> coef_not_neg (pcomp p ps).

  Proof.
    induction p; intros; simpl. exact I. 
    destruct a. simpl. simpl in H. destruct H.
    apply coef_not_neg_add. apply coef_not_neg_cpmult. hyp. 
    apply coef_not_neg_mcomp. hyp. apply IHp; hyp.
  Qed.

  (***********************************************************************)
  (* MOVE *)
  
  Add Ring R: r_th.

  Lemma add_minus : forall x y, x == x + y - y.
  Proof.
    intros. ring.
  Qed.

   Lemma add_op_ge_intro_r : forall x y z, x + z >>= y + z -> x >>= y.

  Proof.
    intros x y z. unfold or_ge.
    intuition. left. rewrite (add_minus x z). rewrite (add_minus y z).
    unfold r_sub. apply or_add_gt_mono_r. hyp.
    right. rewrite (add_minus x z). rewrite (add_minus y z).
    rewrite H0. refl.
  Qed.

  (* replace r_opp_def by Ropp_def *)
  Lemma r_opp_def : forall x, x + (-x) == 0.
  Proof.
    intros. ring.
  Qed.

  Lemma r_opp_def2 : forall x, (-x) + x == 0.
  Proof.
    intros. ring.
  Qed.

  Lemma add_permute : forall n m p, n + (m + p) == m + (n + p).
  
  Proof.
    intros. ring.
  Qed.

 Lemma or_ge_minus_iff : forall r s, r >>= s <-> r + - s >>= 0.

  Proof.
  intros. intuition. rewrite <- (r_opp_def s).
  apply or_add_ge_mono_r. hyp.
  rewrite <- (Aplus_0_r _ r).
  rewrite <- (@r_opp_def s).
  rewrite add_permute.
  set (a := s + (r + -s)).
  rewrite <- (Aplus_0_r _ s).  
  rewrite (Radd_comm r_th).
  unfold a. set (b := r + -s). 
  rewrite (Radd_comm r_th).
  apply or_add_ge_mono_r.
  unfold b. hyp.
  Qed.

  (***********************************************************************)

  Lemma coef_not_In_coef : forall n (p : poly n) (m : monom n) c,
    coef_not_neg p -> In (c, m) p -> coef m p >>= c.
    
  Proof.
    induction p. simpl. tauto.
    destruct a. simpl. intros. destruct H. destruct H0.
    inversion H0. subst. case (monom_eq_dec m m); intro.
    apply or_ge_minus_iff.
    rewrite (Radd_comm r_th).
    rewrite (Radd_assoc r_th).
    rewrite (@r_opp_def2 c).
    rewrite Aplus_0_l. 
    apply coef_not_neg_coef. hyp. apply IHp. hyp. irrefl.
    case (monom_eq_dec m t); intro. subst.
    apply or_ge_trans with (y:=s+c).
    apply or_add_ge_mono_l. apply IHp; hyp.
    apply or_ge_minus_iff. rewrite (Radd_comm r_th).
    rewrite (Radd_assoc r_th). rewrite (Radd_comm r_th).
    rewrite (Radd_assoc r_th). rewrite (@r_opp_def c).
    rewrite Aplus_0_l. hyp.
    apply IHp; hyp.
  Qed.

End S.