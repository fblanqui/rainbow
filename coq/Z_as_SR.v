(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frédéric Blanqui, 2014-02-18

Some structures on integer numbers. *)

Set Implicit Arguments.

Require Import ZArith OrdSemiRing2 Omega LogicUtil RelUtil Morphisms
ZUtil.

Instance Z_as_Setoid : Setoid := LeibnizSetoid Z.

Instance Z_as_DS : DecidableSetoid.

Proof.
  apply Build_DecidableSetoid with (ds_setoid := Z_as_Setoid).
  intros. simpl in *. apply Z.eq_dec. 
Defined.

(* Integer as SemiRing *)

Instance Z_as_SR : SemiRing.

Proof.
apply Build_SemiRing with
(sr_ds  := Z_as_DS)
(sr_0   := 0%Z)
(sr_1   := 1%Z)
(sr_add := Zplus)
(sr_mul := Zmult).
(* Aplus s_eq as proper. *)
intros x y z xx yy H. rewrite H. rewrite z. refl.
(* Amult s_eq as proper. *)
intros x y z xx yy H. rewrite H. rewrite z. refl.
(* Semi-ring-theory. *)
constructor.
exact Zplus_0_l.
exact Zplus_comm.
exact Zplus_assoc.
exact Zmult_1_l.
exact Zmult_0_l.
exact Zmult_comm.
exact Zmult_assoc.
exact Zmult_plus_distr_l.
Defined.

(* Integer as a Ring *)

Instance Z_as_R : Ring.

Proof.
  apply Build_Ring with
  (sr    := Z_as_SR)
  (r_opp := Zopp).
  intros x y H. rewrite H. refl.
  intros x y H z r H1.
  rewrite H. rewrite H1. refl.
  (* Ring theory *)
  constructor.
  exact Zplus_0_l.
  exact Zplus_comm.
  exact Zplus_assoc.
  exact Zmult_1_l.
  exact Zmult_comm.
  exact Zmult_assoc.
  exact Zmult_plus_distr_l.
  refl.
  intro. simpl. omega.
Defined.

(* Integer as an OrderedRing. *)

Open Scope Z_scope.

Definition bgt x y :=
  match Z_gt_dec x y with
    | left _ => true
    | right _ => false
  end.

Lemma bgt_ok : forall x y, bgt x y = true <-> x > y.

Proof.
  intros x y. unfold bgt. case_eq (Z_gt_dec x y); intuition.
Qed.

Lemma one_gt_zero : 1 > 0.

Proof. omega. Qed.

Lemma mul_gt_mono_r : forall x y z, z > 0 -> x > y -> x * z > y * z.
Proof.
  intros x y z H H0. destruct z. omega.
  rewrite (Zmult_comm x); rewrite (Zmult_comm y).
  unfold Zgt in |-*; rewrite Zcompare_mult_compat; hyp.
  discr.
Qed.

Instance Z_as_OR : OrderedRing.

Proof.
  apply Build_OrderedRing with
  (or     := Z_as_R)
  (or_gt  := Zgt)
  (or_bgt := bgt).
  (* transitivity and irreflexive *)
  fo. fo. 
  (* Correctness of function [bgt]. *)
  apply bgt_ok. 
  (* rel_dec gt *)
  apply Z_gt_dec.
  (* 1 > 0 *)
  apply one_gt_zero.
  (* x > y -> x + z > y + z *)
  fo. 
  (* z > 0 -> x > y -> x * z > y * z *)
  fo. apply mul_gt_mono_r. hyp. hyp.
  (* gt proper *)
  unfold Z.gt. intuition.
Defined. (* REMARK: not Qed. *)