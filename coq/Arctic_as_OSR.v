(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frédéric Blanqui, 2014-02-18

Some structures on artic numbers. *)

Set Implicit Arguments.

Require Import Arith OrdSemiRing2 Omega LogicUtil RelUtil Morphisms
        EqUtil Max SemiRing.

Instance Arctic_as_Setoid : Setoid := LeibnizSetoid ArcticDom.

Instance Arctic_as_DS : DecidableSetoid.

Proof.
  apply Build_DecidableSetoid with (ds_setoid := Arctic_as_Setoid).
  simpl. intros.
  apply dec_beq with (beq := beq_ArcticDom).
  apply beq_ArcticDom_ok.
Defined.

Definition gt m n :=
    match m, n with
    | MinusInf, _ => False
    | Pos _, MinusInf => True
    | Pos m, Pos n => m > n
    end.

Definition ge m n := gt m n \/ m = n.

(***********************************************************************)
(** Arctic ordered setoid *)

Instance Arctic_as_OS : OrderedSetoid.

Proof.
  apply Build_OrderedSetoid with
  (os_setoid := Arctic_as_Setoid)
  (os_gt := gt).
  simpl. intros x x' xx' y y' yy' xy. rewrite <- xx'.
  rewrite <- yy'. apply xy.
Defined.

(* max is a <+> operation in the semi-ring *)

Definition Aplus m n :=
  match m, n with
    | MinusInf, n => n
    | m, MinusInf => m
    | Pos m, Pos n => Pos (max m n)
  end.

(* plus is a <*> operation in the semi-ring *)

Definition Amult m n := 
  match m, n with
    | MinusInf, _ => MinusInf
    | _, MinusInf => MinusInf
    | Pos m, Pos n => Pos (m + n)
  end.

Lemma A_plus_comm : forall m n, Aplus m n = Aplus n m.

Proof.
  intros. unfold Aplus. destruct m; destruct n; trivial.
  rewrite max_comm. trivial.
Qed.

Lemma A_plus_0_r : forall n, Aplus n MinusInf = n.

Proof.
  intros. unfold Aplus. destruct n; auto.
Qed.

Lemma A_plus_0_l : forall n, Aplus MinusInf n = n.

Proof.
  intros. rewrite A_plus_comm. apply A_plus_0_r.
Qed.

Lemma A_plus_assoc : forall m n p,
  Aplus m (Aplus n p) = Aplus (Aplus m n) p.

Proof.
  intros. unfold Aplus.
  destruct m; destruct n; destruct p; trivial.
  rewrite max_assoc. trivial.
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

Import Compare. Import Max.

Lemma A_mult_plus_distr : forall m n p,
  Amult (Aplus m n) p = Aplus (Amult m p) (Amult n p).

Proof.
  intros. unfold Amult, Aplus.
  destruct m; destruct n; destruct p; trivial.
  destruct (le_dec n n0).
  rewrite max_l. rewrite max_l. trivial. auto with arith. trivial.
  rewrite max_r. rewrite max_r. trivial. auto with arith. trivial.
Qed.

(***********************************************************************)
(** Arctic semi-ring *)

Definition A0 := MinusInf.
Definition A1 := Pos 0.

Instance Arctic_as_SR : SemiRing.

Proof.
apply Build_SemiRing with
  (sr_ds  := Arctic_as_DS)
  (sr_0   := A0)
  (sr_1   := A1)
  (sr_add := Aplus)
  (sr_mul := Amult).
(* Aplus s_eq as a proper *)
intros x y z xx yy H. rewrite H. rewrite z. refl.
(* Amult s_eq as a proper *)
intros x y z xx yy H. rewrite H. rewrite z. refl.
(* semi-ring-theory *)
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
(** Arctic ordered semi-ring *)

Notation "x + y" := (Aplus x y).
Notation "x * y" := (Amult x y).
Notation "x >=_a y" := (ge x y) (at level 70).
Notation "x >_a y" := (gt x y) (at level 70).

Lemma gt_trans : transitive gt.

Proof.
  intros x y z xy yz. 
  destruct x; destruct y; destruct z; try solve [ auto | contr ].
  apply gt_trans with n0; auto.
Qed.

Lemma ge_trans : Transitive ge.

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
  destruct (@ds_eq_dec Arctic_as_DS x y).
  left. right. hyp.
  right. intro xy. destruct xy; auto.
Defined.

(* ge @ gt << gt : ge_gt_compat *)

Lemma ge_gt_compat:  forall x y z:
  ArcticDom, x >=_a y -> y >_a z -> x >_a z.

Proof.
  intros. destruct y. destruct x. destruct z.
  unfold gt, ge in *. destruct H. 
  simpl in H. omega.
  injection H. intro. subst n0. hyp.
  auto.
  elimtype False. destruct H. auto. discr.
  elimtype False. destruct H. auto. subst x.
  auto.
Qed.

(* gt @ ge << gt : ge_gt_compat2 *)

Lemma gt_ge_compat : forall x y z,
  x >_a y -> y >=_a z -> x >_a z.

Proof.
unfold ge, gt.
destruct x; destruct y; destruct z; simpl; intuition.
inversion H1. subst. hyp. discr.
Qed.

Lemma ge_impl_pos_ge : forall m n, (m >= n)%nat -> Pos m >=_a Pos n.

Proof.
  intros. destruct (lt_eq_lt_dec m n) as [[m_n | m_n] | m_n].
  elimtype False. omega.
  subst m. right. refl.
  left. trivial.
Qed.

Lemma pos_ge_impl_ge : forall m n, Pos m >=_a Pos n -> (m >= n)%nat.

Proof.
  intros. destruct H. auto with arith. 
  injection H. intro. subst m. auto with arith.
Qed.

Ltac arctic_ord :=
  match goal with
    | H: MinusInf >_a Pos _ |- _ =>
      contr
    | H: MinusInf >=_a Pos _ |- _ =>
      destruct H; [ contr | discr ]
    | H: Pos ?m >=_a Pos ?n |- _ =>
      assert ((m >= n)%nat); 
        [ apply pos_ge_impl_ge; hyp 
        | clear H; arctic_ord
        ]
    | |- Pos _ >=_a MinusInf => left; simpl; trivial
    | |- Pos ?m >=_a Pos ?n => apply ge_impl_pos_ge
    | _ => try solve [contr | discr]
  end.

(* plus gt compat. *)
Lemma plus_gt_compat : Proper (gt ==> gt ==> gt) Aplus.

Proof.
intros m m' H n n' H0.
destruct m; destruct n; destruct m'; destruct n';
simpl; trivial; arctic_ord.
apply NatUtil.max_gt_compat; hyp.
 unfold Peano.gt. apply NatUtil.lt_max_intro_l. hyp.
 unfold Peano.gt. apply NatUtil.lt_max_intro_r. hyp.
Qed.

(* Aplus ge proper: plus_ge_compat *)
Lemma plus_ge_compat : Proper (ge ==> ge ==> ge) Aplus.
Proof.
  intros m m' H n n' H0.
  destruct m; destruct n; destruct m'; destruct n'; 
  simpl; trivial; arctic_ord.
  apply NatUtil.max_ge_compat; hyp.
  unfold Peano.ge. apply NatUtil.le_max_intro_l. hyp.
  unfold Peano.ge. apply NatUtil.le_max_intro_r. hyp.
Qed.

(* Aplus proper: mult_ge_compat *)
Lemma mult_ge_compat : Proper (ge ==> ge ==> ge) Amult.
Proof.
intros m m' H n n' H0.
destruct m; destruct n; destruct m'; destruct n'; 
simpl; trivial; arctic_ord.
omega.
Qed.

Instance Arctic_as_OSR : OrderedSemiRing.

Proof.
apply Build_OrderedSemiRing with
(osr_sr := Arctic_as_SR)
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
(* Aplus proper: mult_ge_compat *)
apply mult_ge_compat.
(* Remark: if I end by [Qed] I cannot use it in another file. It must
end with [Defined]. *)
Defined.

(** Properties of OrderSemiRing. *)

Lemma ge_refl : reflexive ge.

Proof.
  intro m. right. trivial.
Qed.

Lemma arctic_plus_notInf_left : forall a b,
  a <> MinusInf -> Aplus a b <> MinusInf.

Proof.
  intros. destruct a. 
  destruct b; simpl; discr.
  auto. 
Qed.

Lemma arctic_mult_notInf: forall a b,
  a <> MinusInf -> b <> MinusInf -> Amult a b <> MinusInf.

Proof.
  intros. 
  destruct a; auto. 
  destruct b; auto. 
  simpl. discr.
Qed.

Lemma not_minusInf_ge_A1 : forall a, a <> MinusInf -> a >=_a A1.

Proof.
  intros. destruct a. destruct n.
  right. refl.
  left. simpl. omega.
  tauto.
Qed.

Lemma ge_A1_not_minusInf : forall a, a >=_a A1 -> a <> MinusInf.

Proof.
  intros. destruct a. 
  discr.
  destruct H. contr. discr.
Qed.

Lemma ge_gt_eq : forall x y, x >=_a y -> x >_a y \/ x = y.

Proof.
  destruct 1; auto.
Qed.

Require Import SN.

Lemma gt_WF : WF gt.

Proof.
  apply wf_transp_WF. 
  apply well_founded_lt_compat with 
  (fun x => 
     match x with
       | Pos x => (x + 1)%nat
       | MinusInf => 0
     end). intros.
  destruct x; destruct y;
          solve [auto with arith | elimtype False; auto].
Qed.