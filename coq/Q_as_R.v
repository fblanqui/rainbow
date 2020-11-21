(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frédéric Blanqui, 2014-02-18

Some structures on integer numbers. *)

Set Implicit Arguments.

Require Import EqUtil QArith OrdSemiRing2 Omega LogicUtil RelUtil
Morphisms ZUtil.

Global Instance Q_as_Setoid : Setoid.
Proof.
  apply Build_Setoid with (s_typ :=Q)(s_eq:=Qeq).
  constructor. fo. fo. unfold Transitive. apply Qeq_trans.
Defined.

Global Instance Q_as_DS : DecidableSetoid.

Proof.
  apply Build_DecidableSetoid with (ds_setoid := Q_as_Setoid).
  intros. simpl in *.
  apply Qeq_dec.
Defined.

Instance Q_as_SR : SemiRing.

Proof.
  apply Build_SemiRing with
  (sr_ds  := Q_as_DS)
  (sr_0   := 0%Q)
  (sr_1   := 1%Q)
  (sr_add := Qplus)
  (sr_mul := Qmult).
  intros x y H z r H1. rewrite H. rewrite H1. refl.
  intros x y H z r H1. rewrite H. rewrite H1. refl.
  constructor. 
  exact Qplus_0_l.
  exact Qplus_comm.
  exact Qplus_assoc.
  exact Qmult_1_l. fo.
  exact Qmult_comm.
  exact Qmult_assoc.
  exact Qmult_plus_distr_l.
Defined.

(* Rational numbers as Ring *)

Instance Q_as_R : Ring.

Proof.
  apply Build_Ring with (sr:= Q_as_SR)(r_opp := Qopp).
  intros x y H. rewrite H. refl.
  intros x y H z r H1. rewrite H. rewrite H1. refl.
  apply Qsrt.
Defined.

(* Rational as OrderedRing. *)

Definition Qgt x y := Qlt y x.

Definition Qgt_dec x y : {x > y} + {~ x > y}.

Proof.
  unfold Qlt in |- *. intros.
  exact (Z_lt_dec (Qnum y * QDen x) (Qnum x * QDen y)).
Defined.

Definition Q_bgt x y :=
  match Qgt_dec x y with
    | left _ => true
    | right _ => false
  end.

Lemma Q_bgt_ok : forall x y, Q_bgt x y = true <-> x > y.

Proof.
  intros. unfold Q_bgt. case_eq (Qgt_dec x y); intuition.
Qed.

Lemma one_Qgt_zero : 1 > 0.

Proof.
  apply Zlt_0_1.
Qed.

Lemma add_gt_mono_r : forall x y z, x > y -> x + z > y + z.

Proof.
  unfold Qplus, Qlt; intros (x1, x2) (y1, y2) (z1, z2); simpl;
  simpl_mult.
  Open Scope Z_scope.
  intros.  match goal with |- ?a < ?b => ring_simplify a b end.
  apply Zplus_lt_compat_r. rewrite <- Zmult_assoc, Zmult_comm.
  rewrite <- !Zmult_assoc. apply Zmult_lt_compat_l.
  apply Zmult_lt_0_compat; apply Zgt_lt; apply Zgt_pos_0.
  set (a := 'x2 * y1). rewrite Zmult_comm. 
  unfold a. rewrite Zmult_comm. hyp. 
  Close Scope Z_scope.
Qed.

Lemma mul_Qgt_mono_r : forall x y z, z > 0 -> x > y -> x * z > y * z. 

Proof.
  intros. apply Qmult_lt_compat_r with (x := y). hyp. hyp. 
Qed.

Instance Q_as_OR : OrderedRing.

Proof.
  apply Build_OrderedRing with
  (or     := Q_as_R)
  (or_gt  := Qgt)
  (or_bgt := Q_bgt).
  (* Transitivity *)
  intros m n p.
  unfold Qgt; intros; apply Qlt_trans with n; hyp.
  (* Irreflexive *)
  unfold Irreflexive, complement, Reflexive, Qgt.
  intros. apply Zlt_irrefl in H. hyp.
  (* Correctness of [bgt] *)
  apply Q_bgt_ok.
  (* rel_dec gt *)
  apply Qgt_dec.
  (* 1 > 0 *)
  apply one_Qgt_zero.
  (* x > y -> x + z > y + z *)
  fo. unfold Qgt in H.
  apply add_gt_mono_r. hyp.
  (* z > 0 -> x > y -> x * z > y * z *)
  apply mul_Qgt_mono_r.
  (* gt Proper *)
  intros x y H z r H1.
  unfold Qgt. intuition. rewrite <- H. rewrite <- H1. hyp.
  rewrite H1. rewrite H. hyp.
Defined. (* REMARK: not Qed. *)