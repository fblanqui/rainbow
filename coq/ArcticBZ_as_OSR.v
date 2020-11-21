(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frédéric Blanqui, 2014-02-18

Some structures on arctic below zero numbers. *)

Set Implicit Arguments.

Require Import Arith OrdSemiRing2 Omega LogicUtil RelUtil Morphisms
SemiRing EqUtil Max.

Instance ArcticBZ_as_Setoid : Setoid := LeibnizSetoid ArcticBZDom.

Instance ArcticBZ_as_DS : DecidableSetoid.

Proof.
  apply Build_DecidableSetoid with (ds_setoid := ArcticBZ_as_Setoid).
  simpl. intros.
  apply dec_beq with (beq := beq_ArcticBZDom).
  apply beq_ArcticBZDom_ok.
Defined.

Local Open Scope Z_scope.

Definition gt m n :=
    match m, n with
    | MinusInfBZ, _ => False
    | Fin _, MinusInfBZ => True
    | Fin m, Fin n => m > n
    end.

Definition ge m n := gt m n \/ m = n.

(***********************************************************************)
(* Define [is_above_zero] used in AArcticBZInt.v *)

Require Import ZUtil.

Definition is_above_zero v :=
  match v with
    | MinusInfBZ => false
    | Fin z => is_not_neg z
  end.

Lemma is_above_zero_ok :
  forall v, is_above_zero v = true <-> ge v (Fin 0).
Proof.
  intro. destruct v; simpl; intuition.
  destruct z. right. refl. left. simpl.
  auto with zarith. discr.
  rewrite is_not_neg_ok. destruct H. simpl in H.
  auto with zarith.
  inversion H. auto with zarith.
  destruct H. simpl in H. contr. discr.
Qed.

(***********************************************************************)
(** Arctic below zero ordered setoid *)

Instance ArcticBZ_as_OS : OrderedSetoid.

Proof.
  apply Build_OrderedSetoid with
  (os_setoid := ArcticBZ_as_Setoid)
  (os_gt := gt).
  simpl. intros x x' xx' y y' yy' xy. rewrite <- xx'.
  rewrite <- yy'. apply xy.
Defined.

(***********************************************************************)
(** Arctic below zero semi-ring *)

Definition A0 := MinusInfBZ.
Definition A1 := Fin 0.

(* max is a <+> operation in the semi-ring *)
Definition Aplus m n :=
  match m, n with
    | MinusInfBZ, n => n
    | m, MinusInfBZ => m
    | Fin m, Fin n => Fin (Zmax m n)
  end.

(* plus is a <*> operation in the semi-ring *)
Definition Amult m n := 
  match m, n with
    | MinusInfBZ, _ => MinusInfBZ
    | _, MinusInfBZ => MinusInfBZ
    | Fin m, Fin n => Fin (m + n)
  end.

Lemma A_plus_comm : forall m n, Aplus m n = Aplus n m.

Proof.
  intros. unfold Aplus. destruct m; destruct n; trivial. 
  rewrite Zmax_comm. refl.
Qed.

Lemma A_plus_assoc : forall m n p,
  Aplus m (Aplus n p) = Aplus (Aplus m n) p.

Proof.
  intros. unfold Aplus.
  destruct m; destruct n; destruct p; trivial.
  rewrite Zmax_assoc. refl.
Qed.

Lemma A_mult_comm : forall m n, Amult m n = Amult n m.

Proof.
  intros. unfold Amult. destruct m; destruct n; trivial.
  rewrite Zplus_comm. refl.
Qed.

Lemma A_mult_assoc : forall m n p,
  Amult m (Amult n p) = Amult (Amult m n) p.

Proof.
  intros. unfold Amult.
  destruct m; destruct n; destruct p; trivial.
  rewrite Zplus_assoc. refl.
Qed.

Lemma A_mult_plus_distr : forall m n p,
  Amult (Aplus m n) p = Aplus (Amult m p) (Amult n p).

Proof.
  intros. unfold Amult, Aplus. 
  destruct m; destruct n; destruct p; trivial.
  rewrite Zplus_max_distr_r.
  destruct (Zmax_irreducible_inf z z0); rewrite e; refl.
Qed.

Instance ArcticBZ_as_SR : SemiRing.

Proof.
apply Build_SemiRing with
(sr_ds  := ArcticBZ_as_DS)
(sr_0   := MinusInfBZ)
(sr_1   := Fin 0)
(sr_add := Aplus)
(sr_mul := Amult).
(* Aplus eq as proper. *)
intros x y z xx yy H. rewrite H. rewrite z. refl.
(* Amult eq as proper. *)
intros x y z xx yy H. rewrite H. rewrite z. refl.
(* semi-ring-theory. *)
constructor; intros.
compute; trivial.
apply A_plus_comm.
apply A_plus_assoc.
destruct n; compute; trivial.
compute; trivial.
apply A_mult_comm.
apply A_mult_assoc.
apply A_mult_plus_distr.
Defined.

(***********************************************************************)
(** Arctic below zero ordered semi-ring. *)

Notation "x + y"    := (Aplus x y).
Notation "x * y"    := (Amult x y).
Notation "x >_b y"  := (gt x y) (at level 70).
Notation "x >=_b y" := (ge x y) (at level 70).

Lemma gt_trans : transitive gt.

Proof.
  intros m n p mn np.
  destruct m; auto. 
  destruct n. 
  destruct p; auto.
  simpl in *. omega.
  simpl in *. tauto.
Qed.

Lemma ge_trans : transitive ge.

Proof.
  intros m n p mn np. 
  destruct mn. 
  destruct np.
  left. apply (gt_trans m n p); hyp.
  rewrite <- H0. left. trivial.
  rewrite H. trivial.
Qed.

Lemma gt_dec : rel_dec gt.

Proof.
  intros x y.
  destruct x; destruct y; simpl; auto.
  destruct (Z_lt_dec z0 z); [left | right]; omega.
Defined.

Lemma ge_dec : rel_dec ge.

Proof.
  intros x y.
  destruct (gt_dec x y).
  left. left. trivial.
  destruct (@ds_eq_dec ArcticBZ_as_DS x y).
  left. right. trivial.
  right. intro xy. destruct xy; auto.
Defined.

(* ge @ gt << gt : ge_gt_compat *)

Lemma ge_gt_compat: forall x y z, x >=_b y -> y >_b z -> x >_b z. 

Proof.
  intros. destruct y. destruct x. destruct z.
  unfold gt, ge in *. destruct H. 
  simpl in H. omega.
  injection H. intro. subst z0. hyp.
  auto.
  elimtype False. destruct H. auto. discr.
  elimtype False. destruct H. auto. subst x. auto.
Qed.

(* gt @ ge << gt : gt_ge_compat *)

Lemma gt_ge_compat: forall x y z, x >_b y -> y >=_b z -> x >_b z. 

Proof.
  unfold ge, gt. destruct x as [x|]; destruct y as [y|];
                 try destruct z as [z|]; simpl; intuition.
  inversion H1. subst. hyp. discr.
Qed.

Lemma ge_impl_fin_ge : forall m n, (m >= n)%Z -> Fin m >=_b Fin n.

Proof.
  intros. destruct (Z_le_lt_eq_dec n m). omega.
  left. simpl. omega.
  subst n. right. refl.
Qed.

Lemma fin_ge_impl_ge : forall m n, Fin m >=_b Fin n -> (m >= n)%Z.

Proof.
  intros. destruct H. 
  simpl in H. omega.
  injection H. intro. subst m. omega.
Qed.

Ltac arctic_ord :=
  match goal with
    | H: MinusInfBZ >_b Fin _ |- _ =>
      contr
    | H: MinusInfBZ >=_b Fin _ |- _ =>
      destruct H; [ contr | discr ]
    | H: Fin ?m >=_b Fin ?n |- _ =>
      assert ((m >= n)%Z); 
        [ apply fin_ge_impl_ge; hyp 
        | clear H; arctic_ord
        ]
    | |- Fin _ >=_b MinusInfBZ => left; simpl; trivial
    | |- Fin ?m >=_b Fin ?n => apply ge_impl_fin_ge
    | _ => try solve [contr | discr]
  end.

Lemma plus_gt_compat: Proper (gt ==> gt ==> gt) Aplus.

Proof.
intros m m' H n n' H0.
 destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord; simpl in *.
 apply ZUtil.Zmax_gt_compat; hyp.
 apply Zlt_gt. apply ZUtil.elim_lt_Zmax_l. omega.
 apply Zlt_gt. apply ZUtil.elim_lt_Zmax_r. omega.
Qed.

Lemma plus_ge_compat: Proper (ge ==> ge ==> ge) Aplus.
Proof.
intros m m' H n n' H0.
destruct m; destruct n; destruct m'; destruct n'; 
simpl; trivial; arctic_ord.
apply ZUtil.Zmax_ge_compat; hyp.
apply Zle_ge. apply ZUtil.elim_Zmax_l. omega.
apply Zle_ge. apply ZUtil.elim_Zmax_r. omega.
Qed.

Lemma mult_ge_compat: Proper (ge ==> ge ==> ge) Amult.

Proof.
intros m m' H n n' H0.
destruct m; destruct n; destruct m'; destruct n'; 
simpl; trivial; arctic_ord.
omega.
Qed.

Instance ArcticBZ_as_OSR : OrderedSemiRing.

Proof.
apply Build_OrderedSemiRing with
(osr_sr := ArcticBZ_as_SR)
(osr_gt := gt)
(osr_ge := ge); simpl.
fo. fo.
(* Transitive ge *)
apply ge_trans.
(* Transitive gt *)
apply gt_trans.
(* rel_dec ge *)
apply ge_dec.
(* rel_dec gt *)
apply gt_dec.
(* ge @ gt << gt *)
apply ge_gt_compat.
(* gt @ ge << gt *)
apply gt_ge_compat.
(* Aplus gt proper: plus_gt_compat *)
apply plus_gt_compat.
(* Aplus ge proper: plus_ge_compat *)
apply plus_ge_compat.
(* Mult ge proper: mult_ge_compat *)
apply mult_ge_compat.
Defined.

(** Properties of arctic below zero. *)

Lemma ge_gt_eq : forall x y, x >=_b y -> x >_b y \/ x = y.

Proof.
  destruct 1; auto.
Qed.

Lemma minusInf_ge_min : forall a, a >=_b MinusInfBZ.

Proof.
  intros. destruct a. left. simpl. trivial.
  right. refl.
Qed.

Lemma arctic_plus_ge_monotone :
  forall (a b c : s_typ),
    a >=_b c -> Aplus a b >=_b c.

Proof.
  intros. destruct c.
  destruct a. destruct b. simpl. arctic_ord. 
  apply Zle_ge. apply elim_Zmax_l. omega.
  trivial.
  arctic_ord.
  apply minusInf_ge_min.
Qed.

Lemma A_plus_0_r : forall n, Aplus n MinusInfBZ = n.

Proof.
  intros. unfold Aplus. destruct n; auto.
Qed.

Lemma A_plus_0_l : forall n, Aplus MinusInfBZ n = n.

Proof.
  intros. rewrite A_plus_comm. apply A_plus_0_r.
Qed.