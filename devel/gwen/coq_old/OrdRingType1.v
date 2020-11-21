
(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-05-20
- Frederic Blanqui, 2005-02-25

Ring equipped with a decidable strict ordering.
*)

Require Import Ring RingType1 RelUtil LogicUtil VecUtil Setoid BoolUtil
  Wellfounded Morphisms RelExtras1.

(***********************************************************************)
(** Module type for building the theory module of an ordered ring *)

Class OrdRing := {
  (*o_ring :> Ring;*)
  o_ring :> Ring;
  o_gt : s_typ -> s_typ -> Prop;
  o_gt_trans : transitive o_gt;
  o_gt_irrefl : irreflexive o_gt;
  o_bgt : s_typ -> s_typ -> bool;
  o_bgt_ok : forall x y, o_bgt x y = true <-> o_gt x y;
  o_one_gt_zero : o_gt ring_A1 ring_A0;
  o_add_gt_mono_r : forall x y z, o_gt x y -> o_gt (ring_Aplus x z) (ring_Aplus y z);
  o_mul_gt_mono_r : forall x y z, o_gt z ring_A0 -> o_gt x y -> o_gt (ring_Amult x z) (ring_Amult y z)                               
}.

(***********************************************************************)
(* Integers as an order ring *)

Require Import ZArith.

Definition gtA_dec := Z_gt_dec. 
 
Definition bgtA x y := 
  match gtA_dec x y with 
    |left _ => true 
    |right _ => false
  end.

Instance Z_as_OrdRing : OrdRing.

Proof.
  apply Build_OrdRing with
  (o_ring := Int_as_Ring)
  (o_gt := Zgt)(o_bgt:= bgtA).
  exact Zcompare_Gt_trans.
  intros n H. apply (Zgt_asym n n H H).
  intros. unfold bgtA. case (gtA_dec x y); intuition.
  simpl. omega. simpl. intros. omega.
  simpl.  intros x y z H H0. destruct z. contradiction (Zgt_irrefl 0). 
  rewrite (Zmult_comm x); rewrite (Zmult_comm y). 
  unfold Zgt in |- *; rewrite Zcompare_mult_compat; hyp. 
  discr.
Defined.

(***********************************************************************)
(**Rational numbers as an order ring *)

Require Import QArith.

Definition Qgt x y := Qlt y x. 

Definition Q_gt_dec x y : {x > y} + {~ x > y}.
Proof.
  unfold Qlt in |- *. intros. 
  exact (Z_lt_dec (Qnum y * QDen x) (Qnum x * QDen y)).
Defined.

Definition Qgt_dec := Q_gt_dec.

Definition Qbgt x y :=
  match Qgt_dec x y with
    |left _ => true
    |right _ => false
  end.

Instance Q_as_OrdRing : OrdRing.

Proof.
  apply Build_OrdRing with
  (o_ring := Q_as_Ring)(o_gt:=Qgt)
  (o_bgt:= Qbgt). (* FIXME *)
  