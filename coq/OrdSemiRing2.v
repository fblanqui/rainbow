(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frédéric Blanqui, 2014-02-18

Class of ordered semi-rings.
*)

Set Implicit Arguments.

Require Import Relations Structures.Equalities LogicUtil Morphisms Basics
  Ring_theory.

(** Setoids. *)

Class Setoid := {
  s_typ      :> Type;
  s_eq       : relation s_typ;
  s_eq_Equiv : Equivalence s_eq }.

Existing Instance s_eq_Equiv.

Module Import Setoid_Notations.
  Infix "==" := s_eq (at level 70).
End Setoid_Notations.

Global Instance LeibnizSetoid (A : Type) : Setoid.

Proof.
  apply Build_Setoid with (s_eq := @eq A).
  constructor. fo. fo.
  unfold Transitive. apply eq_trans.
Defined.

(** Setoids with decidable equivalence. *)

Class DecidableSetoid := {
  ds_setoid :> Setoid;
  ds_eq_dec : forall x y, {s_eq x y} + {~s_eq x y} }.

(** Ordered setoids. *)

Class OrderedSetoid := {
  os_setoid    :> Setoid;
  os_gt        : relation s_typ;
  os_gt_compat : Proper (s_eq ==> s_eq ==> impl) os_gt }.

(***********************************************************************)
(** Dedicable semi-rings. *)

Class SemiRing := {
  sr_ds     :> DecidableSetoid;
  sr_0      : s_typ;
  sr_1      : s_typ;
  sr_add    : s_typ -> s_typ -> s_typ;
  sr_add_eq : Proper (s_eq ==> s_eq ==> s_eq) sr_add;
  sr_mul    : s_typ -> s_typ -> s_typ;
  sr_mul_eq : Proper (s_eq ==> s_eq ==> s_eq) sr_mul;
  sr_th     : semi_ring_theory sr_0 sr_1 sr_add sr_mul s_eq }.

Existing Instance sr_add_eq.
Existing Instance sr_mul_eq.

(*******************************************************************)
(* Ring class *)

Class Ring := {
  sr       :> SemiRing;
  r_opp    : s_typ -> s_typ;
  r_sub    : s_typ -> s_typ -> s_typ := fun x y => sr_add x (r_opp y);
  r_opp_eq : Proper (s_eq ==> s_eq) r_opp;
  r_sub_eq : Proper (s_eq ==> s_eq ==> s_eq) r_sub;
  r_th     : ring_theory sr_0 sr_1 sr_add sr_mul r_sub r_opp s_eq }.

Existing Instance r_opp_eq.
Existing Instance r_sub_eq.

Module Import SR_Notations.
  Include Setoid_Notations.
  Notation "0"     := sr_0.
  Notation "1"     := sr_1.
  Infix "+"        := sr_add.
  Infix "*"        := sr_mul.
  Notation "- x"   := (r_opp x).
  Notation "x - y" := (r_sub x y).
End SR_Notations.

Section SR_Theory.

  Variable SR : SemiRing.

  Definition Aplus_comm          := SRadd_comm sr_th.
  Definition Aplus_assoc         := SRadd_assoc sr_th.
  Definition Aplus_0_l           := SRadd_0_l sr_th.
  Definition Amult_comm          := SRmul_comm sr_th.
  Definition Amult_assoc         := SRmul_assoc sr_th.
  Definition Amult_0_l           := SRmul_0_l sr_th.
  Definition Amult_1_l           := SRmul_1_l sr_th.
  Definition A_plus_mult_distr_l := SRdistr_l sr_th.

  (* Addition *)

  Lemma Aplus_0_r n : n + 0 == n.

  Proof. rewrite Aplus_comm. apply Aplus_0_l. Qed.

  (* Multiplication *)

  Lemma Amult_0_r n : n * 0 == 0.

  Proof. rewrite Amult_comm. apply Amult_0_l. Qed.

  Lemma Amult_1_r n : n * 1 == n.

  Proof. rewrite Amult_comm. apply Amult_1_l. Qed.

  Lemma A_plus_mult_distr_r m n p : m * (n + p) == m * n + m * p.

  Proof.
    rewrite Amult_comm, (Amult_comm m n), (Amult_comm m p).
    apply A_plus_mult_distr_l.
  Qed.

  (* Power *)

  Fixpoint power x n {struct n} :=
    match n with
      | 0 => 1
      | S n' => x * power x n'
    end.

  Notation "x ^ n" := (power x n).

  Lemma power_add : forall x n1 n2, x ^ (n1 + n2) == x ^ n1 * x ^ n2.

  Proof.
  induction n1; simpl; intros. rewrite Amult_1_l. refl. rewrite IHn1.
  rewrite Amult_assoc. refl.
  Qed.

End SR_Theory.

Hint Rewrite Aplus_0_l Aplus_0_r Amult_0_l Amult_0_r Amult_1_l Amult_1_r
  : arith.

(***********************************************************************)
(** Dedicable ordered semi-rings. *)

Class OrderedSemiRing := {
  osr_sr :> SemiRing;
  osr_gt : relation s_typ;
  osr_ge : relation s_typ;
  osr_eq_incl_ge : forall x y, s_eq x y -> osr_ge x y;
  osr_ge_refl  : Reflexive osr_ge;
  osr_ge_trans : Transitive osr_ge;
  osr_gt_trans : Transitive osr_gt;
  osr_ge_dec : forall x y, {osr_ge x y} + {~osr_ge x y};
  osr_gt_dec : forall x y, {osr_gt x y} + {~osr_gt x y};
  osr_ge_gt  : forall x y z, osr_ge x y -> osr_gt y z -> osr_gt x z;
  osr_gt_ge  : forall x y z, osr_gt x y -> osr_ge y z -> osr_gt x z;
  osr_add_gt : Proper (osr_gt ==> osr_gt ==> osr_gt) sr_add;
  osr_add_ge : Proper (osr_ge ==> osr_ge ==> osr_ge) sr_add;
  osr_mul_ge : Proper (osr_ge ==> osr_ge ==> osr_ge) sr_mul
 }.

Existing Instance osr_ge_refl.
Existing Instance osr_ge_trans.
Existing Instance osr_gt_trans.
Existing Instance osr_add_gt.
Existing Instance osr_add_ge.
Existing Instance osr_mul_ge.

Module Import OSR_Notations.
  Include SR_Notations.
  Infix ">>" := osr_gt (at level 70).
  Infix ">>=" := osr_ge (at level 70).
End OSR_Notations.

Section OSR_Theory.

  Variable OSR : OrderedSemiRing.

  Global Instance ge_eq : Proper (s_eq ==> s_eq ==> iff) osr_ge.

  Proof.
    intros x y H x0 y0 H0. intuition.
    trans x. apply osr_eq_incl_ge. sym. hyp.
    trans x0. hyp. apply osr_eq_incl_ge. hyp.
    trans y. apply osr_eq_incl_ge. hyp.
    trans y0. hyp. apply osr_eq_incl_ge. sym. hyp.
  Qed.

  Global Instance gt_eq : Proper (s_eq ==> s_eq ==> iff) osr_gt.

  Proof.
    intros x y H x0 y0 H0.
    intuition. apply osr_gt_ge with x0. 2: apply osr_eq_incl_ge; hyp.
    apply osr_ge_gt with x. apply osr_eq_incl_ge. sym. hyp. hyp.
    apply osr_gt_ge with y0. 2: apply osr_eq_incl_ge; sym; hyp.
    apply osr_ge_gt with y. apply osr_eq_incl_ge. hyp. hyp.
  Qed.

  (* Define boolean function for [eq]. *)
  
  Definition beq x y :=
    match ds_eq_dec x y with
      | left _  => true
      | right _ => false
    end.
  
  Lemma beq_ok : forall x y, beq x y = true <-> s_eq x y.
  Proof.
    intros. unfold beq. case_eq (ds_eq_dec x y); intuition; discr.
  Qed.

  (* Define boolean function for [ge]. *)

  Definition bge x y :=
    match osr_ge_dec x y with
      | left _  => true
      | right _ => false
    end.

  Lemma bge_ok : forall x y, bge x y = true <-> x >>= y.
  Proof.
    intros. unfold bge. case_eq (osr_ge_dec x y); intuition; discr.
  Qed.

  (* Define boolean function for [gt]. *)

  Definition bgt x y :=
    match osr_gt_dec x y with
      | left _  => true
      | right _ => false
    end.
  
  Lemma bgt_ok : forall x y, bgt x y = true <-> x >> y.
  Proof.
    intros. unfold bgt. case_eq (osr_gt_dec x y); intuition; discr.
  Qed.

End OSR_Theory.

(* TEST: It is simpler to define the relation [ge] than define it as a
field like the definition above. *)
(*******************************************************************************)
(* Class Order Ring *)

Class OrderedRing := {
  or           :> Ring;
  or_gt        : relation s_typ;
  or_gt_trans  : Transitive or_gt;
  or_gt_irrefl : Irreflexive or_gt;
  or_bgt       : s_typ -> s_typ -> bool;
  (* x > y = true -> x > y *)
  or_bgt_ok : forall x y, or_bgt x y = true <-> or_gt x y;
  (* x > y - ~ x > y *)
  or_gt_dec : forall x y, {or_gt x y} + {~or_gt x y};
  (* 1 > 0 *)
  or_one_gt_zero  : or_gt sr_1 sr_0;
  (*or_one_ge_zero: forall x, or_gt x sr_0 \/ s_eq x sr_0 -> or_gt x sr_0;*)
  (* FIXME: this lemma needed in the Polynomial. *)
  (*  or_gt_0 : forall x, or_gt x 0 -> x <> 0;*)
  (* x > y -> x + z > y + z *)
  or_add_gt_mono_r : forall x y z, or_gt x y -> or_gt (sr_add x z) (sr_add y z);
  (* z > 0 -> x > y -> x * z > y * z *)
  or_mul_gt_mono_r : forall x y z, or_gt z sr_0 -> or_gt x y ->
                                   or_gt (sr_mul x z) (sr_mul y z);
  ogt_eq           : Proper (s_eq ==> s_eq ==> iff) or_gt }.

Existing Instance or_gt_trans.
Existing Instance or_gt_irrefl.
Existing Instance ogt_eq.

Module Import OR_Notations.
  Include SR_Notations.
  Infix ">>" := or_gt (at level 70).

End OR_Notations.

(***********************************************************************)
(* Define not_neg of type [s_typ] in OrderedRing. *)

Section OR_Theory.

  Context {OR: OrderedRing}.

  Definition or_ge x y := x >> y \/ x == y.
  
  Notation "x >>= y" := (or_ge x y) (at level 70).

  (* TODO *)
  Lemma or_gt_0 : forall x, x >> 0 -> x <> 0.
  Proof.
    intros.
  Admitted.

  (* TODO *)
  Lemma or_gt_eq_ge_dec : forall x y, x >>= y -> {x >> y} + {x == y}.
  Proof.
    intuition. unfold or_ge in H. 
  Admitted.
    
  Lemma or_ge_refl : forall x, x >>= x.
  
  Proof.
    right. refl.
  Qed.

  Lemma or_ge_trans : forall x y z, x >>= y -> y >>= z -> x >>= z.
  
  Proof.
    unfold transitive, or_ge. intuition.
    left. transitivity y; hyp. left.
    rewrite <- H. auto.
    rewrite H1. auto.
    rewrite H1. rewrite H. right. refl.
  Qed.

   Add Relation s_typ or_ge
    reflexivity proved by or_ge_refl
    transitivity proved by or_ge_trans
      as or_ge_rel.
   
   Global Instance or_ge_mor : Proper (s_eq ==> s_eq ==> iff) or_ge.
   
   Proof.
     intros x y H x0 y0 H0.
     unfold or_ge. intuition.
     rewrite <- H. rewrite <- H0. auto.
     rewrite <- H. rewrite H2. auto.
     rewrite H. rewrite H0. auto.
     rewrite H. rewrite H2. rewrite H0. right. refl.
   Qed.    

  Definition bool_or_gt x y := 
    match or_gt_dec x y with
      | left _  => true
      | right _ => false
    end.

  Definition bool_s_eq x y :=
    match ds_eq_dec x y with
      | left _  => true
      | right _ => false
    end.
  
  (* FIXME: bge = bgt || beq? *)

  Require Import BoolUtil.

  (*  x > y || x = y *)

  Definition bool_or_ge x y := bool_or_gt x y || bool_s_eq x y.

  Lemma bool_s_eq_ok : forall x y, bool_s_eq x y = true <-> x == y.

  Proof.
    intros. unfold bool_s_eq. case_eq (ds_eq_dec x y); intuition; discr.
  Qed.

  Lemma bool_or_gt_ok : forall x y, bool_or_gt x y = true <-> x >> y.

  Proof.
    intros. unfold bool_or_gt. case_eq (or_gt_dec x y); intuition; discr.
  Qed.

  Lemma bool_or_ge_ok : forall x y, bool_or_ge x y = true <-> x >>= y.

  Proof.
    intros x y. unfold bool_or_ge. rewrite orb_eq. rewrite bool_or_gt_ok.
    rewrite bool_s_eq_ok. unfold or_ge; intuition.
  Qed.

  (* z > 0 || z = 0 *)

  Definition bnot_neg z := bool_or_gt z 0 || bool_s_eq z 0.

  Lemma bnot_neg_ok : forall z, bnot_neg z = true <-> z >>= 0.
  Proof.
    intros. unfold bnot_neg. rewrite orb_eq.
    rewrite bool_or_gt_ok. rewrite bool_s_eq_ok.
    unfold or_ge; intuition. 
  Qed.

  (* Addition *)

  Lemma or_add_ge_mono_r : forall x y z, x >>= y -> x + z >>= y + z.

  Proof.
    unfold or_ge. intuition. left. apply or_add_gt_mono_r. hyp. 
    right. rewrite H0. refl.
  Qed.

  Lemma or_add_ge_0 : forall n m, n >>= 0 -> m >>= 0 -> n + m >>= 0.

  Proof.
    intros. apply or_ge_trans with (x := n + m)(y := m).
    rewrite <- (SRadd_0_l sr_th m). rewrite (SRadd_assoc sr_th), Aplus_0_r.
    apply or_add_ge_mono_r. hyp. hyp. 
  Qed.

  Lemma or_add_gt_mono_l : forall x y z, x >> y -> z + x >> z + y.

  Proof.
    intros. set (a := z + x). rewrite (SRadd_comm sr_th). unfold a.
    rewrite (SRadd_comm sr_th). apply or_add_gt_mono_r. hyp.
  Qed.

  Lemma or_add_ge_mono_l : forall x y z, x >>= y -> z + x >>= z + y.

  Proof.
    intros x y z. unfold or_ge.
    intuition. left. apply or_add_gt_mono_l. hyp.
    right. rewrite H0. refl.
  Qed.

  (*
  Lemma or_add_ge_mono_r : forall x y z, x >>= y -> x + z >>= y + z.

  Proof.
    intros x y z. unfold or_ge.
    intuition. left. apply or_add_gt_mono_r. hyp. 
    right. rewrite H0. refl.
  Qed.*)

  Lemma or_add_ge_compat: forall x y z w, x >>= y -> z >>= w -> x + z >>= y + w.

  Proof.
    intros. eapply or_ge_trans. apply or_add_ge_mono_r. apply H.
    apply or_add_ge_mono_l. hyp.
  Qed.

  Lemma ge_gt_trans : forall x y z, x >>= y -> y >> z  -> x >> z.

  Proof.
    unfold or_ge. intuition. transitivity y; hyp. rewrite H1. hyp.
  Qed.

  Lemma gt_ge_trans : forall x y z, x >> y -> y >>= z -> x >> z.
  Proof.
    intros. apply ge_gt_trans with (y:=x). apply or_ge_refl.
    destruct H0. transitivity y; hyp. rewrite <- H0. hyp.
  Qed.

  Lemma or_add_ge_gt_mono : forall x y p q, 
    x >>= y -> p >> q -> x + p >> y + q.

  Proof.
    intros. apply ge_gt_trans with (y:=y+p). apply or_add_ge_mono_r.
    hyp. apply or_add_gt_mono_l. hyp.
  Qed.

  Lemma or_add_gt_ge_mono : forall x y p q,
    x >> y -> p >>= q -> x + p >> y + q.

  Proof.
    intros. apply gt_ge_trans with (y:=y+p). apply or_add_gt_mono_r.
    hyp. apply or_add_ge_mono_l. hyp.
  Qed.

  (* Multiplication *)

  Lemma or_mul_gt_mono_l : forall x y z, z >> 0 -> x >> y -> z * x >> z * y. 
    
  Proof.
  intros. set (a := z * x). rewrite (SRmul_comm sr_th). unfold a.
  rewrite (SRmul_comm sr_th). apply or_mul_gt_mono_r. hyp. hyp.
  Qed.

  Lemma or_mul_ge_mono_l : forall x y z, z >>= 0 -> x >>= y -> z * x >>= z * y.

  Proof.
  intros x y z. unfold or_ge. intros. elim H. 
  intros. elim H0. intros. left. apply or_mul_gt_mono_l. hyp. 
  hyp. right. rewrite H2. refl. intros. right. rewrite H1.
  do 2 rewrite Amult_0_l. refl.
  Qed.

  Lemma or_mul_ge_mono_r : forall x y z,  z >>= 0 -> x >>= y -> x * z >>= y * z.
  
  Proof.
  intros. set (a := x * z). rewrite (SRmul_comm sr_th). unfold a.
  rewrite (SRmul_comm sr_th). apply or_mul_ge_mono_l. hyp. hyp. 
  Qed.
  
  Lemma or_mul_ge_0 : forall n m, n >>= 0 -> m >>= 0 -> n * m >>= 0.

  Proof.
    intros. rewrite <- (Amult_0_l _ m). apply or_mul_ge_mono_r.
    hyp. hyp.
  Qed.

  Lemma or_mul_ge_compat : forall x y z w, y >>= 0 -> w >>= 0 -> x >>= y ->
    z >>= w -> x * z >>= y * w.
 
  Proof.
    intros. eapply or_ge_trans. apply or_mul_ge_mono_r. 
    eapply or_ge_trans. apply H2. hyp. apply H1.
    apply or_mul_ge_mono_l. hyp. hyp. 
  Qed.
  
  (* Power *)

  Notation "x ^ n" := (power _ x n).

  Lemma or_power_ge_0 : forall x n, x >>= 0 ->  x ^ n >>= 0.
  
  Proof.  
  induction n. 
  intros. simpl. unfold or_ge. left. apply or_one_gt_zero. 
  simpl. intros. apply or_mul_ge_0. hyp.
  apply IHn. hyp.
  Qed.

  Lemma or_power_ge_compat : forall x y (n : nat),
    x >>= 0 -> y >>= x -> y ^ n >>= x ^ n.
  
  Proof.
  induction n. simpl. intros. apply or_ge_refl.
  intros. simpl. apply or_mul_ge_compat. hyp.
  apply or_power_ge_0. hyp. hyp. apply IHn. hyp. hyp.
  Qed.

End OR_Theory.