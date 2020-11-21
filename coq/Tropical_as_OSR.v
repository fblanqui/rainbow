(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frédéric Blanqui, 2014-02-18

Some structures on tropical numbers. *)

Set Implicit Arguments.

Require Import Arith OrdSemiRing2 Omega LogicUtil RelUtil Morphisms
SemiRing EqUtil Max.

Instance Tropical_as_Setoid : Setoid := LeibnizSetoid TropicalDom.

Instance Tropical_as_DS : DecidableSetoid.

Proof.
  apply Build_DecidableSetoid with (ds_setoid := Tropical_as_Setoid).
  simpl. intros.
  apply dec_beq with (beq := beq_TropicalDom). apply beq_TropicalDom_ok.
Defined.

(***********************************************************************)
(** Tropical ordered setoid *)

Definition gt m n :=
  match m, n with
    | PlusInf, PlusInf => False
    | PlusInf, _ => True
    | TPos _, PlusInf => False
    | TPos m, TPos n => m > n
  end.

Definition ge m n := gt m n \/ m = n.

Instance Tropical_as_OS : OrderedSetoid.

Proof.
  apply Build_OrderedSetoid with
  (os_setoid := Tropical_as_Setoid)
  (os_gt     := gt).
  simpl. intros x x' xx' y y' yy' xy. rewrite <- xx'.
  rewrite <- yy'. apply xy.
Defined.

(***********************************************************************)
(** Tropical semi-ring *)

Definition A0 := PlusInf.
Definition A1 := TPos 0.

Definition Aplus m n :=
  match m, n with
    | PlusInf, n     => n
    | m, PlusInf     => m
    | TPos m, TPos n => TPos (min m n)
  end.

Definition Amult m n := 
  match m, n with
    | PlusInf, _     => PlusInf
    | _, PlusInf     => PlusInf
    | TPos m, TPos n => TPos (m + n)
  end.

Require Import Min.

Lemma A_plus_comm : forall m n, Aplus m n = Aplus n m.

Proof.
  intros. unfold Aplus. destruct m; destruct n; trivial.
  rewrite min_comm. trivial.
Qed.

Lemma A_plus_assoc : forall m n p,
  Aplus m (Aplus n p) = Aplus (Aplus m n) p.

Proof.
  intros. unfold Aplus.
  destruct m; destruct n; destruct p; trivial.
  rewrite min_assoc. trivial.
Qed.

Lemma A_mult_comm : forall m n, Amult m n = Amult n m.

Proof.
  intros. unfold Amult. destruct m; destruct n; trivial.
  rewrite plus_comm. trivial.
Qed.

Lemma A_mult_assoc : forall m n p,
  Amult m (Amult n p) = Amult (Amult m n) p.

Proof.
  intros. unfold Amult.
  destruct m; destruct n; destruct p; trivial.
  rewrite plus_assoc. trivial.
Qed.

Import Compare. Import Min.

Lemma A_mult_plus_distr : forall m n p,
  Amult (Aplus m n) p = Aplus (Amult m p) (Amult n p).

Proof.
  intros. unfold Amult, Aplus.
  destruct m; destruct n; destruct p; trivial.
  destruct (le_dec n0 n).
  rewrite min_l. rewrite min_l. trivial.
  auto with arith. trivial.
  rewrite min_r. rewrite min_r. trivial.
  auto with arith. trivial.
Qed.

Instance Tropical_as_SR : SemiRing.

Proof.
  apply Build_SemiRing with
  (sr_ds  := Tropical_as_DS)
  (sr_0   := PlusInf)
  (sr_1   := TPos 0)
  (sr_add := Aplus)
  (sr_mul := Amult).
  (* Aplus s_eq as proper. *)
  intros x y z xx yy H. rewrite H. rewrite z. refl.
  (* Amult s_eq as proper. *)
  intros x y z xx yy H. rewrite H. rewrite z. refl.
  (* Semi-ring-theory. *)
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
(** Tropical ordered semi-ring *)

Notation "x + y"    := (Aplus x y).
Notation "x * y"    := (Amult x y).
Notation "x >=_t y" := (ge x y) (at level 70).
Notation "x >_t y"  := (gt x y) (at level 70).

Lemma gt_trans : transitive gt.

Proof.
  intros x y z xy yz. 
  destruct x; destruct y; destruct z; try solve [ auto | contr ].
  apply gt_trans with n0; auto.
Qed.

Lemma ge_trans : transitive ge.

Proof.
  intros x y z xy yz. destruct xy. destruct yz.
  left. apply (gt_trans x y z); hyp.
  subst y. left. hyp.
  subst x. hyp.
Qed.

Lemma gt_dec : rel_dec gt.

Proof.
  unfold rel_dec. intros.
  destruct x; destruct y; simpl; auto.
  destruct (gt_dec n n0); auto.
Defined.

Lemma ge_dec : rel_dec ge.

Proof.
  intros x y. destruct (gt_dec x y).
  left. left. hyp.
  destruct (@ds_eq_dec Tropical_as_DS x y).
  left. right. hyp.
  right. intro xy. destruct xy; auto.
Defined.

(* ge @ gt << gt : ge_gt_compat *)

Lemma ge_gt_compat: forall x y z, x >=_t y -> y >_t z -> x >_t z.

Proof with simpl; intuition.
    intros. 
    destruct y; destruct x; destruct z; auto...
    destruct H. simpl in *. omega. injection H. intros. subst...
    destruct H. contr. discr.
Qed.

(* gt @ ge << gt : gt_ge_compat *)

Lemma gt_ge_compat: forall x y z, x >_t y -> y >=_t z -> x >_t z.

Proof.
  unfold ge, gt. destruct x; destruct y; destruct z; simpl; intuition;
  try discr.
  inversion H1. subst. hyp.
Qed.

Lemma ge_impl_pos_ge : forall m n, (m >= n)%nat -> TPos m >=_t TPos n.

Proof.
  intros. destruct (lt_eq_lt_dec m n) as [[m_n | m_n] | m_n].
  elimtype False. omega.
  subst m. right. refl.
  left. trivial.
Qed.

Lemma pos_ge_impl_ge : forall m n, TPos m >=_t TPos n -> (m >= n)%nat.

Proof.
  intros. destruct H. auto with arith. 
  injection H. intro. subst m. auto with arith.
Qed.

Ltac tropical_ord :=
  match goal with
    | H: _ >_t PlusInf |- _ => contr
    | H: TPos _ >=_t PlusInf |- _ =>
      destruct H; [ contr | discr ]
    | H: TPos ?m >=_t TPos ?n |- _ =>
      assert ((m >= n)%nat); 
        [ apply pos_ge_impl_ge; hyp 
        | clear H; tropical_ord
        ]
    | |- PlusInf >=_t TPos _ => left; simpl; trivial
    | |- TPos ?m >=_t TPos ?n => apply ge_impl_pos_ge
    | _ => try solve [contr | discr]
  end.

Lemma plus_gt_compat: Proper (gt ==> gt ==> gt) Aplus.

Proof.
intros m m' H n n' H0.
destruct m; destruct n; destruct m'; destruct n'; 
simpl; trivial; tropical_ord.
apply NatUtil.min_gt_compat; hyp.
unfold Peano.gt. apply NatUtil.lt_min_intro_l. hyp.
unfold Peano.gt. apply NatUtil.lt_min_intro_r. hyp.
Qed.

Lemma plus_ge_compat: Proper (ge ==> ge ==> ge) Aplus.

Proof.
intros m m' H n n' H0.
destruct m; destruct n; destruct m'; destruct n'; 
simpl; trivial; tropical_ord.
apply NatUtil.min_ge_compat; hyp.
unfold Peano.ge. apply NatUtil.le_min_intro_l. hyp.
unfold Peano.ge. apply NatUtil.le_min_intro_r. hyp.
Qed.

Lemma mult_ge_compat: Proper (ge ==> ge ==> ge) Amult.

Proof.
intros m m' H n n' H0.
 destruct m; destruct n; destruct m'; destruct n'; 
 simpl; trivial; tropical_ord.
 omega.
Qed.

Instance Tropical_as_OSR : OrderedSemiRing.

Proof.
apply Build_OrderedSemiRing with
(osr_sr := Tropical_as_SR)
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

Lemma tropical_plus_notInf_left :forall a b,
  a <> PlusInf -> Aplus a b <> PlusInf.

Proof.
  intros. destruct a. 
  destruct b; simpl; discr.
  auto. 
Qed.

Lemma tropical_mult_notInf : forall a b,
  a <> PlusInf -> b <> PlusInf -> Amult a b <> PlusInf.

Proof.
  intros. 
  destruct a; auto. 
  destruct b; auto. 
  simpl. discr.
Qed.

Lemma tropical_plus_inf_max : forall x, x <> PlusInf -> PlusInf >_t x.

Proof.
  intros. destruct x. simpl. auto.
  elimtype False. apply H. trivial.
Qed.

Lemma A_plus_0_r : forall n, Aplus n PlusInf = n.

Proof.
  intros. unfold Aplus. destruct n; auto.
Qed.

Lemma A_plus_0_l : forall n, Aplus PlusInf n = n.

Proof.
  intros. rewrite A_plus_comm. apply A_plus_0_r.
Qed.

Lemma gt_irrefl : irreflexive gt.

Proof.
  intros x xx. destruct x.
  unfold gt in xx. omega.
  auto.
Qed.

Require Import SN.

Lemma gt_Fin_WF x : Acc (transp gt) (TPos x).

Proof.
  induction x using lt_wf_ind; apply Acc_intro; destruct y;
  auto || contr.
Qed.

Hint Resolve gt_Fin_WF.

Lemma gt_WF : WF gt.

Proof with auto; try contr.
  apply wf_transp_WF. intro x.
  destruct x...
  apply Acc_intro. intros. destruct y...
Qed.

Lemma ge_gt_eq : forall x y, x >=_t y -> x >_t y \/ x = y.

Proof.
  destruct 1; auto.
Qed.