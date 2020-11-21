(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frédéric Blanqui, 2014-02-18

Some structures on natural numbers. *)

Set Implicit Arguments.

Require Import Arith OrdSemiRing2 Omega LogicUtil RelUtil Morphisms.

Global Instance Nat_as_Setoid : Setoid := LeibnizSetoid nat.

Global Instance Nat_as_DS : DecidableSetoid.

Proof.
  apply Build_DecidableSetoid with (ds_setoid := Nat_as_Setoid).
  apply eq_nat_dec.
Defined.

Global Instance Nat_as_OS : OrderedSetoid.

Proof.
  apply Build_OrderedSetoid with
  (os_setoid := Nat_as_Setoid)
  (os_gt     := gt).
  simpl. intros x x' xx' y y' yy' xy. omega.
Defined.

Global Instance Nat_as_SR : SemiRing.

Proof.
apply Build_SemiRing with
(sr_ds  := Nat_as_DS)
(sr_0   := 0)
(sr_1   := 1)
(sr_add := plus)
(sr_mul := mult).
class. class. constructor; intros; simpl; try ring. refl.
Defined.

Global Instance Nat_as_OSR : OrderedSemiRing.

Proof.
apply Build_OrderedSemiRing with
(osr_sr := Nat_as_SR)
(osr_gt := gt)
(osr_ge := ge); simpl.
fo. fo.
intros x y z xy yz. omega.
intros x y z xy yz. omega.
unfold rel_dec. apply ge_dec.
unfold rel_dec. apply gt_dec.
intros x y z. omega.
intros x y z. omega.
intros x x' xx' y y' yy'. omega.
intros x x' xx' y y' yy'. omega.
intros x x' xx' y y' yy'.
apply mult_le_compat; hyp.
Defined.

(* Properties of Natural numbers on OrderedSemiRing. *)

Require Import SN.

Lemma gt_WF : WF gt.

Proof.
   apply wf_transp_WF.
   apply well_founded_lt_compat with (fun x:nat => x). auto.
Qed.

Lemma eq_ge_compat : forall x y, x = y -> x >= y.

Proof.
  intros. subst. apply le_refl.
Qed.

Lemma ge_gt_compat : forall x y z, x >= y -> y > z -> x > z.

Proof.
  intros. apply le_gt_trans with y; hyp.
Qed.

Lemma plus_gt_compat_l : forall m n m' n',
  m > m' -> n >= n' -> m + n > m' + n'.

Proof.
  intros. omega.
Qed.

Lemma plus_gt_compat_r : forall m n m' n',
  m >= m' -> n > n' -> m + n > m' + n'.

Proof.
  intros. omega.
Qed.

Lemma mult_ge_compat : forall m n m' n',
    m >= m' -> n >= n' -> m * n >= m' * n'.

Proof.
  intros. unfold Peano.ge.
  apply mult_le_compat; hyp.
Qed.