(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-05-20
- Frederic Blanqui, 2005-02-25

polynomials with non-negative integers as coefficients

- Kim Quyen Ly, 2013-08-23

Polynomials with non-negative rational numbers as coefficients.
*)

Set Implicit Arguments.

Require Import NewPolynom2 RingType2 NaryFunction ListForall VecUtil List
  LogicUtil Relations QArith OrdRingType2.

(* REMARK: Add Section to be able to control some arguments. *)

Section PosQPoly.

  Notation "x >=A y" := (QgeA x y) (at level 70).
  Notation "0" := QA0.
  Notation pos := (fun z => z >=A 0).
  Notation D := (sig pos).
  Notation vec := (vector D).
  Notation val := (@proj1_sig Q pos).
  Notation vals := (@Vmap D Q val _).

  (* meval of type Q. *)
  
  Lemma not_neg_meval : forall n (m : monom n) (v : vec n),
    meval m (vals v) >=A 0.
    
  Proof.
    induction n; intros; simpl. unfold QgeA.
    left. apply one_QgtA_zero. 
    VSntac m. VSntac v. simpl. apply Qmul_geA_0_compat. 
    apply Qpower_geA_0. destruct (Vhead v).
    simpl. hyp.
    apply IHn.
  Qed.
  
  Notation not_neg := (fun z => z >=A 0).

  Lemma preserv_not_neg_meval :  forall n (m : monom n), preserv not_neg (meval m).
    
  Proof.
    intros n m v Hv. rewrite (Vmap_proj1 Hv). apply not_neg_meval.
  Qed.

  Definition meval_D n (m : monom n) := restrict (preserv_not_neg_meval m).

  (***********************************************************************)
  (** Predicate saying that all pseudo-coefficients are non-negative. *)

  Definition coef_not_neg n (p : Qpoly n) :=
    lforall (fun x => fst x >=A 0) p.

  Definition bcoef_not_neg n (p : Qpoly n) :=
    forallb (fun x => Qbnot_neg (fst x)) p.

  Lemma bcoef_not_neg_ok : forall n (p : Qpoly n),
    bcoef_not_neg p = true <-> coef_not_neg p.
    
  Proof.
    intros n p. apply forallb_lforall. intros [z m]. apply Qbnot_neg_ok. 
  Qed.

  (***********************************************************************)
  (** The predicate coef_not_neg is preserved by operations on
  Qpolynomials. *)

  Lemma coef_not_neg_coef : forall n (p : Qpoly n) m, 
    coef_not_neg p -> Qcoef m p >=A 0.
    
  Proof.
    induction p; intros; simpl. apply QgeA_refl.   
    destruct a. simpl in H. destruct H.
    case (monom_eq_dec m t); intro. assert (Qcoef m p >=A 0). apply IHp. hyp.
    apply Qadd_geA_0_compat; hyp. apply IHp. hyp.
  Qed.

  Lemma coef_not_neg_cons : forall n c (m : monom n) (p : Qpoly n),
    coef_not_neg ((c,m)::p) -> c >=A 0 /\ coef_not_neg p.
    
  Proof.
    unfold coef_not_neg. intros n c m p. simpl. auto.
  Qed.

  Lemma coef_not_neg_app : forall n (p1 p2 : Qpoly n),
    coef_not_neg (p1 ++ p2) -> coef_not_neg p1 /\ coef_not_neg p2.

  Proof.
    unfold coef_not_neg. intros n p1 p2. simpl. rewrite lforall_app.
    intuition.
  Qed.

  Implicit Arguments coef_not_neg_app [n p1 p2].

  Lemma coef_not_neg_mpmult : forall n c (m : monom n) (p : Qpoly n),
    c >=A 0 -> coef_not_neg p -> coef_not_neg (mpmult c m p).
    
  Proof.
    induction p; intros; simpl. exact I. 
    destruct a. simpl.
    simpl in H0. destruct H0. split. 
    apply Qmul_geA_0_compat; hyp.
    apply IHp; hyp.
  Qed.

  Lemma not_neg_peval : forall n (p : Qpoly n) v, 
    coef_not_neg p -> peval p (vals v) >=A 0.
    
  Proof.
    induction p; intros; simpl. apply QgeA_refl. 
    destruct a. simpl in H. destruct H.
    apply Qadd_geA_0_compat. apply Qmul_geA_0_compat. hyp.
    apply not_neg_meval. apply IHp. hyp.
  Qed.

  Lemma preserv_not_neg_peval : forall n (p : Qpoly n),
    coef_not_neg p -> preserv not_neg (peval p).
    
  Proof.
    intros. unfold preserv. intros v Hv.
    rewrite (Vmap_proj1 Hv). apply not_neg_peval. hyp.
  Qed.

  Definition peval_D n (p : Qpoly n) (H : coef_not_neg p) : naryFunction D D n :=
    restrict (preserv_not_neg_peval p H).

  Implicit Arguments peval_D [n p].

  Lemma val_peval_D : forall n (p : Qpoly n) (H : coef_not_neg p) (v : vec n),
    val (peval_D H v) =A= peval p (vals v).

  Proof.
    intros. unfold QeqA.
    refl.
  Qed.

  Lemma coef_not_neg_mpadd : forall n c (m : monom n) (p : Qpoly n),
    c >=A 0 -> coef_not_neg p -> coef_not_neg (mpadd c m p).
    
  Proof.
    induction p; intros; simpl. auto. destruct a. simpl in H0. destruct H0.
    case (monom_eq_dec m t); simpl; intuition.
    apply Qadd_geA_0_compat. hyp. hyp.
  Qed.

  Lemma coef_not_neg_add : forall n (p1 p2 : Qpoly n),
    coef_not_neg p1 -> coef_not_neg p2 -> coef_not_neg (p1 + p2).
    
  Proof.
    induction p1; intros; simpl. hyp. destruct a. simpl in H. destruct H.
    apply coef_not_neg_mpadd. hyp. apply IHp1; hyp.
  Qed.

  Lemma coef_not_neg_mult : forall n (p1 p2 : Qpoly n),
    coef_not_neg p1 -> coef_not_neg p2 -> coef_not_neg (p1 * p2).
    
  Proof.
    induction p1; intros; simpl. exact I. destruct a. simpl in H. destruct H.
    apply coef_not_neg_add. apply coef_not_neg_mpmult; hyp. apply IHp1; hyp.
  Qed.

  Lemma coef_not_neg_power : forall k n (p : Qpoly n),
    coef_not_neg p -> coef_not_neg (ppower p k).
    
  Proof.
    induction k; intros; simpl. intuition. unfold QgeA.
    left. apply one_QgtA_zero.  
    apply coef_not_neg_mult. hyp.
    apply IHk. hyp.
  Qed.

  Lemma coef_not_neg_mcomp : forall k n (m : monom n) (ps : vector (Qpoly k) n),
    Vforall (@coef_not_neg k) ps -> coef_not_neg (mcomp m ps).
    
  Proof.
    induction n; intros; simpl. intuition. unfold QgeA.
    left. apply one_QgtA_zero.
    VSntac ps. simpl. rewrite H0 in H.
    simpl in H. destruct H. apply coef_not_neg_mult. apply coef_not_neg_power.
    hyp. apply IHn. hyp.
  Qed.

  Lemma coef_not_neg_cpmult : forall n c (p : Qpoly n),
    c >=A 0 -> coef_not_neg p -> coef_not_neg (cpmult c p).
    
  Proof.
    induction p; intros; simpl. exact I. 
    destruct a. simpl. simpl in H0. intuition.
    apply Qmul_geA_0_compat. hyp. hyp.
  Qed.

  Lemma coef_not_neg_pcomp : forall n k (p : Qpoly n) (ps : vector (Qpoly k) n),
    coef_not_neg p -> Vforall (@coef_not_neg k) ps -> coef_not_neg (pcomp p ps).
    
  Proof.
    induction p; intros; simpl. exact I. 
    destruct a. simpl. simpl in H. destruct H.
    apply coef_not_neg_add. apply coef_not_neg_cpmult. hyp. 
    apply coef_not_neg_mcomp. hyp. apply IHp; hyp.
  Qed.

  (* Declare the relation geA is transitive relation. Require the
     Setoid library. *)
  
  Add Relation Q QgeA
  reflexivity proved by QgeA_refl
  transitivity proved by QgeA_trans
    as QgeA_rel.

  Lemma coefPos_ge0 : forall n (p : Qpoly n) (m : monom n),
    coef_not_neg p -> Qcoef m p >=A 0.

  Proof with auto with zarith.
    induction p. simpl...
    intros. unfold QgeA. intuition.
    destruct a. simpl. intros m.
    destruct (monom_eq_dec m t).
    subst m. intros. apply QgeA_trans with (Qcoef t p).
    destruct H.
    Focus 2. apply IHp.
    destruct H. hyp.
    Focus 2. intros.
    apply IHp. destruct H.
    hyp.
    set (a := Qcoef t p). apply Qnot_neg_geA.
    apply Qplus_sub_ge0.
  Qed.

  Lemma coef_not_In_coef : forall n (p : Qpoly n) (m : monom n) c,
    coef_not_neg p -> In (c, m) p -> Qcoef m p >=A c.
    
  Proof with auto with qarith.
    induction p. simpl. tauto.
    destruct a. simpl. intros. destruct H. destruct H0.
    inversion H0. subst. case (monom_eq_dec m m); intro.   
    Focus 2. apply IHp. hyp. irrefl.
    apply QgeA_minus_iff. 
    Focus 2.
    case (monom_eq_dec m t); intro. subst.
    transitivity (q + c).
    apply Qadd_geA_mono_l. apply IHp; hyp.
    apply Qadd_geA_intro_r with (-c). ring_simplify.
    unfold QgeA in H. 
    Focus 2.
    apply IHp; hyp.
    set (a:= c + - c).
    apply QgeA_minus_iff.
    unfold a.
    apply Qadd_geA_0_compat.
    rewrite <- QgeA_minus_iff. apply Qnot_neg_geA.
    apply Qplus_sub_ge0.
    apply Qsub_sub_ge. rewrite Qplus_geA0. 
    apply Qplus_sub_ge0.
  Qed.

End PosQPoly.