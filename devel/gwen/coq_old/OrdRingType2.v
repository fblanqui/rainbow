
(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-05-20
- Frederic Blanqui, 2005-02-25

Ring equipped with a decidable strict ordering.

- Kim Quyen Ly, 2013-08-22

Replace Module Type by Section for Ring.

*)

Require Export Ring.
Require Import RingType2 RelUtil LogicUtil VecUtil Setoid BoolUtil
  Wellfounded Morphisms RelExtras2 QArith.

(***********************************************************************)
(** ** Building the theory module of an ordered ring. *)

Section OrdRing.

  Variable e : Eqset.

  Variable r : (Ring e).

  Notation "1" := (A1 r).
  Notation "0" := (A0 r).
  
  Notation Aadd := (Aadd r).
  Notation "x + y" := (Aadd x y).

  Notation Amul := (Amul r).
  Notation "x * y" := (Amul x y).

  Record OrdRing := mkOrdRing {
    gtA : A -> A -> Prop;

    gtA_trans : transitive gtA;

    gtA_irrefl : irreflexive gtA;

    bgtA : A -> A -> bool;

    bgtA_ok : forall x y, bgtA x y = true <-> gtA x y;
    
    one_gtA_zero: gtA 1 0;

    add_gtA_mono_r : forall x y z, gtA x y -> gtA (x + z) (y + z);

    mul_gtA_mono_r : forall x y z, gtA z 0 -> gtA x y -> gtA (x * z) (y * z)

  }.
  
  Notation eqA := (eqA e).

  Variable ord : OrdRing.

  Parameter gtA_morph : Proper (eqA ==> eqA ==> iff) (gtA ord).

End OrdRing.

(***********************************************************************)
(** Theory of ordered rings *)

Section OrdRingTheory.

  Variable e : Eqset.

  Variable r : Ring e.

  Variable ord: OrdRing e r.

  Notation gtA := (gtA e r ord).
  
  Notation gtA_trans := (gtA_trans e r ord).

  Add Relation A gtA
  transitivity proved by gtA_trans
    as gtA_rel.

  (***********************************************************************)
  (** Setoid-reflexive closure of the ordering *)
  
  Notation eqA := (eqA e).

  Notation "x =A= y" := (eqA x y) (at level 70).

  Notation "x >A y" := (gtA x y) (at level 70).

  Definition geA x y := x >A y \/ x =A= y.

  Notation "x >=A y" := (geA x y) (at  level 70).
  
  (* Declare the relation eqA is reflexive relation. Require the Setoid library. *)

  Notation sid_theoryA := (sid_theoryA e).

  Add Setoid A eqA sid_theoryA as A_Setoid.

  Lemma geA_refl : reflexive geA.

  Proof.
    right. reflexivity.
  Qed.

  Lemma geA_trans : transitive geA.

  Proof.
    unfold transitive, geA. intuition.
    left. transitivity y; hyp.
    rewrite <- H. auto.
    rewrite H1. auto.
    rewrite H1. rewrite H. right. refl.
  Qed.

  Add Relation A geA
  reflexivity proved by geA_refl
  transitivity proved by geA_trans
    as geA_rel.

  Add Morphism geA
    with signature eqA ==> eqA ==> iff
      as geA_morph.

  Proof.
    unfold geA. intuition.
    rewrite <- H. rewrite <- H0. auto.
    rewrite <- H. rewrite H2. auto.
    rewrite H. rewrite H0. auto.
    rewrite H. rewrite H2. rewrite H0. right. refl.
  Qed.

  (***********************************************************************)
  (** Boolean ordering *)
  
  Notation bgtA := (bgtA e r ord).

  Notation beqA := (beqA e).

  Definition bgeA x y := bgtA x y || beqA x y.

  Lemma bgeA_ok : forall x y, bgeA x y = true <-> x >=A y.

  Proof.
    intros x y. unfold bgeA, geA. rewrite orb_eq. rewrite bgtA_ok.
    rewrite beqA_ok. tauto.
  Qed.

  (***********************************************************************)
  (** Non-negative numbers *)
  
  Notation "0" := (A0 r).

  Notation not_neg := (fun z => z >=A 0).

  Definition bnot_neg z := bgtA z 0 || beqA z 0.

  Lemma bnot_neg_ok : forall z, bnot_neg z = true <-> z >=A 0.

  Proof.
    intro. unfold bnot_neg, geA. rewrite orb_eq. rewrite bgtA_ok.
    rewrite beqA_ok. tauto.
  Qed.

  Notation D := (sig not_neg).

  Notation inj := (@exist A not_neg _).

  Notation val := (@proj1_sig A not_neg).

  Definition Dgt x y := val x >A val y. Notation Dlt := (transp Dgt).

  Definition Dge x y := val x >=A val y. Notation Dle := (transp Dge).

  (***********************************************************************)
  (** Properties of the ordering *)

  Lemma geA_gtA_trans : forall x y z, x >=A y -> y >A z -> x >A z.

  Proof.
    unfold geA. intuition. transitivity y; hyp. rewrite H1. hyp.
  Qed. 

  Lemma gtA_geA_trans : forall x y z, x >A y -> y >=A z -> x >A z.

  Proof.
    intros. apply geA_gtA_trans with (y := x). apply geA_refl. 
    destruct H0. transitivity y; hyp. rewrite <- H0. hyp. 
  Qed.

  (***********************************************************************)
  (** Addition *)

  Notation "x + y" := (Aadd r x y).

  Notation "x * y" := (Amul r x y).

  Notation "- x" := (Aopp r x).

  Definition Asub := (Asub r).

  Notation "x - y" := (Asub x y).

  Notation Aring := (Aring r).

  Lemma add_gtA_mono_l : forall x y z, x >A y -> z + x >A z + y.

  Proof.
    intros. set (a := z + x). rewrite (Radd_comm Aring). unfold a.
    rewrite (Radd_comm Aring). apply add_gtA_mono_r. hyp.
  Qed.

  Lemma add_geA_mono_l : forall x y z, x >=A y -> z + x >=A z + y.

  Proof.
    unfold geA. intuition. left. apply add_gtA_mono_l. hyp.
    right. rewrite H0. refl.
  Qed.

  Lemma add_geA_mono_r : forall x y z, x >=A y -> x + z >=A y + z.

  Proof.
    unfold geA. intuition. left. apply add_gtA_mono_r. hyp.
    right. rewrite H0. refl.
  Qed.

  Notation add_minus := (add_minus r).

  Notation add_gtA_mono_r := (add_gtA_mono_r e r ord).

  (* TODO *)
  Lemma add_geA_intro_r : forall x y z, x + z >=A y + z -> x >=A y.

  Proof.
    unfold geA. intuition.
    left. rewrite (add_minus x z). rewrite (add_minus y z).
    (*apply add_gtA_mono_r. hyp. *)
    Focus 2.
    right. rewrite (add_minus x z). rewrite (add_minus y z). rewrite H0. refl.

  Admitted.

  Lemma add_geA_0_compat : forall n m, n >=A 0 -> m >=A 0 -> n + m >=A 0.

  Proof.
    intros. apply geA_trans with (x := n + m)(y := m).
    rewrite <- (Radd_0_l Aring m). rewrite (Radd_assoc Aring), Aadd_0_r.
    apply add_geA_mono_r. hyp. hyp. 
  Qed.

  Lemma add_geA_compat: forall x y z w, x >=A y -> z >=A w -> x + z >=A y + w.

  Proof.
    intros. apply geA_trans with (y := y + z). apply add_geA_mono_r. hyp.
    apply add_geA_mono_l. hyp.
  Qed.

  Lemma add_geA_gtA_compat : forall x y z w, x >=A y -> z >A w -> x + z >A y + w.
    
  Proof.
    intros. apply geA_gtA_trans with (y := y + z). apply add_geA_mono_r. hyp.
    apply add_gtA_mono_l. hyp.
  Qed.

  Lemma add_gtA_geA_compat : forall x y z w, x >A y -> z >=A w -> x + z >A y + w.
    
  Proof.
    intros. apply gtA_geA_trans with (y := y + z). apply add_gtA_mono_r. hyp. 
    apply add_geA_mono_l. hyp. 
  Qed.

  Lemma geA_minus_iff : forall r s, r >=A s <-> r + - s >=A 0.

  Proof.
    intros. intuition. rewrite <- (Aopp_def r s).
    apply  add_geA_mono_r. hyp.
    rewrite <- (Aadd_0_r r).
    rewrite <- (@Aopp_def e r s).
    rewrite add_permute.
    set (a := s + (r0 + -s)).
    rewrite <- (Aadd_0_r r s).  
    rewrite (Radd_comm Aring).
    unfold a. set (b := r0 + -s). 
    rewrite (Radd_comm Aring).
    apply add_geA_mono_r.
    unfold b. hyp.
  Qed.

  Lemma not_neg_geA : forall x y, y - x >=A 0 -> y >=A x. 

  Proof.
    intros. apply geA_minus_iff. rewrite <- (Asub_def r) at 1.
    hyp.
  Qed.  

  Notation "1" := (A1 r).

  Lemma not_neg_gt : forall x y : A, y - x - 1 >=A 0 -> y >A x.

  Proof.
    intros. apply gtA_geA_trans with (y := x).
    repeat rewrite (Asub_def r) in H.
    rewrite (Radd_comm Aring) in H. rewrite (Radd_assoc Aring) in H. 
    rewrite <- geA_minus_iff in H.    
    rewrite (Radd_comm Aring) in H. 
    rewrite <- (Aadd_0_r r x) in H.
    rewrite <- (Aopp_def r 1) in H.
    rewrite (Radd_assoc Aring) in H. 
    apply add_geA_intro_r in H. 
    Focus 2. 
    apply geA_refl. apply geA_gtA_trans with (z := x) in H. 
    hyp. set (a := x + 1).  rewrite <- (@Aadd_0_r e r x).
    unfold a. apply add_gtA_mono_l. apply one_gtA_zero.
  Qed.

  (***********************************************************************)
  (** Multiplication *)

  Lemma mul_gtA_0_compat : forall n m, n >A 0 -> m >A 0 -> n * m >A 0.

  Proof.
    intros. rewrite <- (@Amul_0_l e r n). rewrite (Rmul_comm Aring). apply mul_gtA_mono_r. 
    hyp. hyp.
  Qed.

  Lemma mul_gtA_mono_l : forall x y z, z >A 0 -> x >A y -> z * x >A z * y. 
    
  Proof.
    intros. set (a := z * x). rewrite (Rmul_comm Aring). unfold a.
    rewrite (Rmul_comm Aring). apply mul_gtA_mono_r. hyp. hyp.
  Qed.
  
  Lemma mul_geA_mono_l : forall x y z, z >=A 0 -> x >=A y -> z * x >=A z * y.

  Proof.
    intros x y z. unfold geA. intros. elim H. 
    intros. elim H0. intros. left. apply mul_gtA_mono_l. hyp. 
    hyp. right. rewrite H2. refl. intros. right. rewrite H1. do 2 rewrite Amul_0_l. refl.
  Qed.

  Lemma mul_geA_mono_r : forall x y z,  z >=A 0 -> x >=A y -> x * z >=A y * z.
    
  Proof.
    intros. set (a := x * z). rewrite (Rmul_comm Aring). unfold a.
    rewrite (Rmul_comm Aring). apply mul_geA_mono_l. hyp. hyp. 
  Qed.

  Lemma mul_geA_0_compat : forall n m, n >=A 0 -> m >=A 0 -> n * m >=A 0.

  Proof. 
    intros. rewrite <- (Amul_0_l r m). apply mul_geA_mono_r. hyp. hyp. 
  Qed.

  Lemma mul_geA_compat : forall x y z w, y >=A 0 -> w >=A 0 -> x >=A y ->
    z >=A w -> x * z >=A y * w.
    
  Proof.
    intros. apply geA_trans with (y := y * z). apply mul_geA_mono_r. 
    apply geA_trans with (y := w). hyp. hyp. hyp. 
    apply mul_geA_mono_l. hyp. hyp. 
  Qed.

  (***********************************************************************)
  (** power *)

  Notation "x ^ n" := (power r x n).

  Lemma power_geA_0 : forall x n, x >=A 0 ->  x ^ n >=A 0.
    
  Proof.  
    induction n. 
    intros. simpl. unfold geA. left. apply one_gtA_zero. 
    simpl. intros. apply mul_geA_0_compat. hyp.
    apply IHn. hyp.
  Qed.
  
  Lemma power_geA_compat : forall x y (n : nat), x >=A 0 -> y >=A x -> y ^ n >=A x ^ n.
    
  Proof.
    induction n. simpl. intros. refl.
    intros. simpl. apply mul_geA_compat. hyp.
    apply power_geA_0. hyp. hyp. apply IHn. hyp. hyp.
  Qed.

End OrdRingTheory.

(***********************************************************************)
(* Integers as an order ring *)

Section IntOrdRing.

  Require Import BinInt.

  (* ZgtA is an instantiation of gtA of type Z corresponding to the
  abstract type A. *)

  Definition ZgtA := Zgt.

  Definition ZeqA := Z.eq.

  Add Morphism ZgtA
    with signature ZeqA ==> ZeqA ==> iff
      as ZgtA_morph.

  Proof. 
    unfold ZgtA. intuition. rewrite <- H. 
    rewrite <- H0. auto. rewrite H0. rewrite H. auto.
  Qed.

  (* An instantiation of gtA_trans. *)

  Lemma ZgtA_trans : transitive ZgtA.
    
  Proof.
    exact Zcompare_Gt_trans.
  Qed.
  
  (* gtA_irrefl. *)

  Lemma ZgtA_irrefl : irreflexive ZgtA. 
    
  Proof.
    intros n H. apply (Zgt_asym n n H H). 
  Qed.

  Definition gtA_dec := Z_gt_dec. 

  (* bgtA of type Z. *)

  Definition ZbgtA x y := 
    match gtA_dec x y with 
      |left _ => true 
      |right _ => false
    end.

  (* A correctness proof of bgtA_ok of type Z. *)

  Lemma ZbgtA_ok : forall x y, ZbgtA x y = true <-> (x > y)%Z.

  Proof. 
    intros. unfold ZbgtA. case (gtA_dec x y); intuition.
  Qed.

  (* A proof of 1 > 0 of type Z. *)

  Lemma one_ZgtA_zero : (1 > 0)%Z. 
    
  Proof. 
    omega. 
  Qed.
  
  (* A property of add/plus of type Z. *)

  Lemma add_ZgtA_mono_r : forall x y z, (x > y)%Z -> (x + z > y + z)%Z.
    
  Proof. 
    intros. intuition. 
  Qed.

  (* A property of multiplication of type Z. *)

  Lemma mul_ZgtA_mono_r : forall x y z, (z > 0)%Z -> (x > y)%Z -> (x * z > y * z)%Z.

  Proof. 
    intros x y z H H0. destruct z. contradiction (Zgt_irrefl 0). 
    rewrite (Zmult_comm x); rewrite (Zmult_comm y). 
    unfold Zgt in |- *; rewrite Zcompare_mult_compat; hyp. 
    discr. 
  Qed.

End IntOrdRing.

(***********************************************************************)
(* Theory of ordered rings of type Z. *)

Section IntOrdRingTheory.

  Notation "x =A= y" := (ZeqA x y) (at level 70).
  Notation "x >A y" := (ZgtA x y) (at level 70).

  Definition ZgeA x y := x >A y \/ x =A= y.

  Notation "x >=A y" := (ZgeA x y) (at  level 70).

  Lemma ZgeA_refl : reflexive ZgeA.

  Proof.
    right. reflexivity.
  Qed.

End IntOrdRingTheory.

(***********************************************************************)
(** Rational numbers as an order ring *)

Section RatOrdRing.
  
  Require Import QArith QArith_base.

  Open Scope Q_scope.

  Definition QgtA x y := Qlt y x.

  Definition QeqA := Qeq.

  Add Morphism QgtA
    with signature QeqA ==> QeqA ==> iff
      as QgtA_morph.

  Proof. 
    unfold QgtA. intuition. rewrite <- H. 
    rewrite <- H0. auto. rewrite H0. rewrite H. auto.
  Qed.

  Definition Qgt_dec x y : {x > y} + {~ x > y}.
  
  Proof.
    unfold Qlt in |- *. intros. 
    exact (Z_lt_dec (Qnum y * QDen x) (Qnum x * QDen y)).
  Defined.

  Definition QgtA_dec := Qgt_dec.

  Definition QbgtA x y :=
    match QgtA_dec x y with
      |left _ => true
      |right _ => false
    end.

  Lemma QbgtA_ok : forall x y, QbgtA x y = true <-> x > y. 
    
  Proof.
    intros. unfold QbgtA. case (QgtA_dec x y); intuition. 
  Qed. 

  Lemma QgtA_trans : transitive QgtA.
    
  Proof. 
    intros m n p. unfold QgtA; intros; apply Qlt_trans with n; hyp. 
  Qed. 

  Lemma QgtA_irrefl : irreflexive QgtA. 

  Proof.
    unfold inclusion, irreflexive, QgtA. intros. apply Zlt_irrefl. 
  Qed.

  Lemma one_QgtA_zero : 1 > 0. 

  Proof.
    apply Zlt_0_1.
  Qed.

  Lemma Qadd_gtA_mono_r : forall x y z, x > y -> x + z > y + z. 
    
  Proof.
    unfold Qplus, Qlt; intros (x1, x2) (y1, y2) (z1, z2);
      simpl; simpl_mult.
    Open Scope Z_scope.
    intros.
    match goal with |- ?a < ?b => ring_simplify a b end.
    apply Zplus_lt_compat_r. rewrite <- Zmult_assoc, Zmult_comm.
    rewrite <- !Zmult_assoc. apply Zmult_lt_compat_l.
    apply Zmult_lt_0_compat; apply Zgt_lt; apply Zgt_pos_0.
    set (a := 'x2 * y1). rewrite Zmult_comm. 
    unfold a. rewrite Zmult_comm. hyp. 
    Close Scope Z_scope.
  Qed.

  Lemma Qmul_gtA_mono_r : forall x y z, z > 0 -> x > y -> x * z > y * z. 

  Proof.
    intros. apply Qmult_lt_compat_r with (x := y). hyp. hyp. 
  Qed.

End RatOrdRing.

(***********************************************************************)
(* Theory of ordered rings of type Q. *)

Section RatOrdRingTheory.

  Notation "x =A= y" := (QeqA x y) (at level 70).
  Notation "x >A y" := (QgtA x y) (at level 70).

  Definition QgeA x y := x >A y \/ x =A= y.

  Notation "x >=A y" := (QgeA x y) (at  level 70).

  Notation sid_theoryA := Qsid_theoryA.

  Add Setoid Q QeqA sid_theoryA as QA_Setoid.

  Lemma QgeA_refl : reflexive QgeA.

  Proof.
  right. reflexivity.
  Qed.

  Lemma QgeA_trans : transitive QgeA.

  Proof.
  unfold transitive, QgeA. intuition.
  left. unfold QgtA. unfold QgtA in H1.
  unfold QgtA in H. apply Qlt_trans with (y:=y). hyp.
  hyp. left. unfold QgtA.
  unfold QeqA in H. rewrite <- H.
  unfold QgtA in H1. hyp.
  left. unfold QgtA. unfold QeqA in H1.
  unfold QgtA in H. rewrite H1. hyp.
  right. rewrite H1. hyp.
  Qed.

  Add Relation Q QgeA
    reflexivity proved by QgeA_refl
    transitivity proved by QgeA_trans
      as QgeA_rel.

  Add Morphism QgeA
    with signature QeqA ==> QeqA ==> iff
      as QgeA_morph.

  Proof.
  Admitted.

  (***********************************************************************)
  (** Boolean ordering *)

  Definition QbgeA x y := QbgtA x y || QbeqA x y.

  Lemma QbgeA_ok : forall x y, QbgeA x y = true <-> x >=A y.

  Proof.
  intros x y. unfold QbgeA, QgeA. rewrite orb_eq. rewrite QbgtA_ok.
  rewrite QbeqA_ok. tauto.
  Qed.

  (***********************************************************************)
  (** Non-negative numbers *)
 
  Notation "0" := QA0.
  Notation not_neg := (fun z => z >=A 0).

  Definition Qbnot_neg z := QbgtA z 0 || QbeqA z 0.

  Lemma Qbnot_neg_ok : forall z, Qbnot_neg z = true <-> z >=A 0.

  Proof.
    intro. unfold Qbnot_neg, QgeA. rewrite orb_eq. rewrite QbgtA_ok.
    rewrite QbeqA_ok. tauto.
  Qed.

  Notation D := (sig not_neg).
  Notation inj := (@exist Q not_neg _).
  Notation val := (@proj1_sig Q not_neg).

  Definition QDgt (x y: D) := val x >A val y.

  Notation QDlt := (transp QDgt).

  Definition QDge (x y :D) : Prop := val x >=A val y.

  Notation QDle := (transp QDge).

  (***********************************************************************)
  (** Properties of the ordering *)

  Lemma QgeA_gtA_trans : forall x y z, x >=A y -> y >A z -> x >A z.

  Proof.
    unfold QgeA. intuition. unfold QgtA. unfold QgtA in H1. unfold QgtA in H0.
    apply Qlt_trans with (y:=y). hyp. hyp.
    unfold QgtA. unfold QeqA in H1. unfold QgtA in H0. rewrite H1. hyp.
  Qed. 

  Lemma QgtA_geA_trans : forall x y z, x >A y -> y >=A z -> x >A z.

  Proof.
    intros. apply QgeA_gtA_trans with (y := x). apply QgeA_refl. 
    destruct H0. unfold QgtA. unfold QgtA in H0. unfold QgtA in H.
    apply Qlt_trans with (y:= y). hyp. hyp.
    unfold QgtA. unfold QeqA in H0. unfold QgtA in H. rewrite <- H0. hyp.
  Qed.

  (***********************************************************************)
  (** Addition *)
  
  (* REMARK: Aring define as a defintion and not as a Notation to be
  able to use tactic [set].*)

  Definition Aring := QAring.

  Lemma Qadd_gtA_mono_l : forall x y z, x >A y -> z + x >A z + y.

  Proof.
    intros. set (a := z + y). unfold QgtA. rewrite (Radd_comm Aring) at 1. unfold a.
    rewrite (Radd_comm Aring). simpl in *. 
    apply Qadd_gtA_mono_r. unfold QgtA in H. hyp.
  Qed.

  Lemma Qadd_geA_mono_l : forall x y z, x >=A y -> z + x >=A z + y.

  Proof.
    unfold QgeA. intuition. left. apply Qadd_gtA_mono_l. hyp.
    right. rewrite H0. refl.
  Qed.

  Lemma Qadd_geA_mono_r : forall x y z, x >=A y -> x + z >=A y + z.

  Proof.
    unfold QgeA. intuition. left. apply Qadd_gtA_mono_r. hyp.
    right. rewrite H0. refl.
  Qed.

  (* TO MOVE: inside RingType2 *)
  Lemma Qadd_minus : forall x y, x =A= x + y - y.
    
  Proof.
    intros. unfold QeqA. ring.
  Qed.

  Lemma Qadd_0_r : forall x, x + 0 =A= x.

  Proof.
  intros. unfold QeqA. ring. 
  Qed.

  (* Add new lemma used in NewPositivePolynom2.v *)

  Lemma Qplus_sub_ge0 : forall x y, x + y - y >=A 0.
  Proof.

  Admitted.

  (* New Lemma *)
  Lemma Qplus_geA0 : forall x y, x + y + - x >=A 0 <-> y + x + - x  >=A 0.      
  Proof.

  Admitted.
  
  (* New Lemma *)

  Lemma Qsub_sub_ge : forall x, - ( x + - x) >=A 0.
  Proof.

  Admitted.


  Lemma Qadd_geA_intro_r : forall x y z, x + z >=A y + z -> x >=A y.

  Proof.
    intuition. unfold QgeA. unfold QgeA in H.
    intuition. Focus 2. right. apply Qplus_inj_r in H0. unfold QeqA. hyp.
    left. unfold QgtA. unfold QgtA in H0.
    apply Qplus_lt_l in H0. hyp.
  Qed.
  
  Lemma Qadd_geA_0_compat : forall n m, n >=A 0 -> m >=A 0 -> n + m >=A 0.

  Proof.
    intros. apply QgeA_trans with (x := n + m)(y := m).
    rewrite <- (Radd_0_l Aring m). rewrite (Radd_assoc Aring), Qadd_0_r.
    apply Qadd_geA_mono_r. hyp. hyp. 
  Qed.

  Lemma Qadd_geA_compat: forall x y z w, x >=A y -> z >=A w -> x + z >=A y + w.

  Proof.
    intros. apply QgeA_trans with (y := y + z). apply Qadd_geA_mono_r. hyp.
    apply Qadd_geA_mono_l. hyp.
  Qed.

  Lemma Qadd_geA_gtA_compat : forall x y z w, x >=A y -> z >A w -> x + z >A y + w.
  
  Proof.
    intros. apply QgeA_gtA_trans with (y := y + z). apply Qadd_geA_mono_r. hyp.
    apply Qadd_gtA_mono_l. hyp.
  Qed.

  Lemma Qadd_gtA_geA_compat : forall x y z w, x >A y -> z >=A w -> x + z >A y + w.
  
  Proof.
    intros. apply QgtA_geA_trans with (y := y + z). apply Qadd_gtA_mono_r. hyp. 
    apply Qadd_geA_mono_l. hyp. 
  Qed.
  
  (* TO MOVE : RingType2 for Q type *)
  Lemma QAopp_def : forall x, x + (-x) =A= 0.
  
  Proof.
    intros. unfold QeqA. ring.
  Qed.

  Lemma Qadd_permute : forall n m p, n + (m + p) =A= m + (n + p).

  Proof.
    intros. unfold QeqA. ring.
  Qed.

  Lemma QgeA_minus_iff : forall r s, r >=A s <-> r + - s >=A 0.

  Proof.
    intros. intuition. 
    rewrite <- QAopp_def.
    apply Qadd_geA_mono_r. hyp.
    rewrite <- Qadd_0_r. 
    rewrite <- (@QAopp_def s).
    rewrite Qadd_permute.
    set (a := s + (r + -s)).
    rewrite <- (Qadd_0_r s).  
    rewrite (Radd_comm Aring).
    unfold a. set (b := r + -s). 
    rewrite (Radd_comm Aring).
    apply Qadd_geA_mono_r.
    unfold b. hyp.
  Qed.
  
  (* TO MOVE *)
  Lemma Qsub_def : forall x y, x - y =A= x + - y.

  Proof.
    intros. unfold QeqA. ring.
  Qed.

  Lemma Qnot_neg_geA : forall x y, y - x >=A 0 -> y >=A x. 

  Proof.
    intros. apply QgeA_minus_iff. rewrite <- (Qsub_def) at 1.
    hyp.
  Qed.  

  Notation "1" := QA1.

  Lemma Qnot_neg_gt : forall x y : Q, y - x - 1 >=A 0 -> y >A x.

  Proof.
    intros. apply QgtA_geA_trans with (y := x).
    repeat rewrite Qsub_def in H.
    rewrite (Radd_comm Aring) in H. rewrite (Radd_assoc Aring) in H. 
    rewrite <- QgeA_minus_iff in H.    
    rewrite (Radd_comm Aring) in H. 
    rewrite <- (Qadd_0_r x) in H.
    rewrite <- (QAopp_def 1) in H.
    rewrite (Radd_assoc Aring) in H. 
    apply Qadd_geA_intro_r in H. 
    Focus 2. 
    apply QgeA_refl. apply QgeA_gtA_trans with (z := x) in H. 
    hyp. set (a := x + 1). 
    (*unfold a. apply Qadd_gtA_mono_l. apply one_gtAq_zero.*)
  Admitted.

  (***********************************************************************)
  (** Multiplication *)
  
  (* TO MOVE *)
  Lemma QAmul_0_l : forall x, 0 * x =A= 0.

  Proof.
    intros. unfold QeqA. ring. 
  Qed. 

  (* TODO *)
  Lemma Qmul_gtA_0_compat : forall n m, n >A 0 -> m >A 0 -> n * m >A 0.

  Proof.
    intros.
    unfold QgtA. rewrite <- (@Qmult_0_l n). unfold QgtA in H0. 
    unfold QgtA in H.
    rewrite (Rmul_comm Aring). (* TODO *)
  Admitted.

  (* TODO *)
  Lemma Qmul_gtA_mono_l : forall x y z, z >A 0 -> x >A y -> z * x >A z * y. 
    
  Proof.
    intros.
    set (a := z * x). 
    (*rewrite (Rmul_comm Aring). unfold a.
    rewrite (Rmul_comm Aring). apply mul_gtAq_mono_r. hyp. hyp.
  Qed.*)
  Admitted.
 
  Lemma Qmul_geA_mono_l : forall x y z, z >=A 0 -> x >=A y -> z * x >=A z * y.

  Proof.
    intros x y z. unfold QgeA. intros. elim H. 
    intros. elim H0. intros. left. apply Qmul_gtA_mono_l. hyp. 
    hyp. right. rewrite H2. refl. intros. right. rewrite H1. do 2 rewrite QAmul_0_l. refl.
  Qed.

  Lemma Qmul_geA_mono_r : forall x y z,  z >=A 0 -> x >=A y -> x * z >=A y * z.
  
  Proof.
    intros.
    set (a := x * z). rewrite (Rmul_comm Aring). unfold a.
    rewrite (Rmul_comm Aring). apply Qmul_geA_mono_l. hyp. hyp. 
  Qed.

  Lemma Qmul_geA_0_compat : forall n m, n >=A 0 -> m >=A 0 -> n * m >=A 0.

  Proof. 
    intros. rewrite <- (QAmul_0_l m). apply Qmul_geA_mono_r. hyp. hyp. 
  Qed.

  Lemma Qmul_geA_compat : forall x y z w, y >=A 0 -> w >=A 0 -> x >=A y ->
                                         z >=A w -> x * z >=A y * w.
  
  Proof.
    intros. apply QgeA_trans with (y := y * z). apply Qmul_geA_mono_r. 
    apply QgeA_trans with (y := w). hyp. hyp. hyp. 
    apply Qmul_geA_mono_l. hyp. hyp. 
  Qed.

  (***********************************************************************)
  (** power *)

  Notation "x ^ n" := (Qpower x n).
  
  (* TODO *)
  Lemma Qpower_geA_0 : forall x n, x >=A 0 ->  x ^ n >=A 0.
  
  Proof.  
    induction n. 
    intros. simpl. unfold QgeA. left. apply one_QgtA_zero. 
    simpl. intros. (*apply mul_geA_0_compat. hyp.
  apply IHn. hyp.
  Qed.*)
  Admitted.
  
  (* TODO *)
  Lemma Qpower_geA_compat : forall x y (n : Z), x >=A 0 -> y >=A x
    -> y ^ n >=A x ^ n.
  
  Proof.
    induction n. simpl. intros. refl.
    intros. simpl. (*apply mul_geA_compat. hyp.
  apply power_geA_0. hyp. hyp. apply IHn. hyp. hyp.
  Qed.*)
  Admitted.

End RatOrdRingTheory.

(***********************************************************************)
(* Definitions and properites using rational number 
 *         f(x) = floor (x / delta). (delta > 0) 
 *         gtA x y = x - y >= delta 
 Remark the notation ">" and ">=" is the notations of type Q (QArith_base)*)

Section Well_found_Rational.

  Require Import QArith_base Qround QMake.

  Open Local Scope Q_scope.

  Variable delta : Q.

  Variable delta_pos : delta > 0. 
  
  Definition gtAQ (x y: Q) := x - y >= delta.

  (***********************************************************************)
  (* f(x): Q -> N *)

  Definition f_Z (x: Q): Z := Qfloor (Qdiv x delta).

  Definition f (x: Q): nat := Zabs_nat (f_Z x).

  Definition f_Q (x: Q): Q := inject_Z (f_Z x). 

(***********************************************************************)
(* x = f(x) * delta + t, 0 <= t < delta *)


  Lemma Q_floor_pos: forall z, 0 <= z -> (0 <= Qfloor z)%Z.

  Proof.
    intros. rewrite <- (Qfloor_Z (0)). 
    apply Qfloor_resp_le. intuition.
  Qed.

  (*FIXME: Change name*) 

  Lemma poly_exp:  forall x, x >= 0 -> exists t, x == f_Q x * delta + t /\ 
    0 <= t /\ t < delta.

  Proof.
    intros. exists (x - f_Q x * delta).
    split. ring. 
    split. unfold f_Q, f, f_Z. set (z := x / delta).
    rewrite Qmult_comm. unfold Qminus. 
    rewrite <- (Qplus_opp_r (delta * inject_Z (Qfloor z))).
    apply Qplus_le_compat. rewrite Qmult_comm. 
    setoid_replace (x) with (x * (delta/delta)). 
    set (t := inject_Z (Qfloor z) * delta). rewrite Qmult_comm. unfold Qdiv. 
    rewrite <- Qmult_assoc.
    rewrite Qmult_comm. unfold t. apply Qmult_le_compat_r.
    rewrite Qmult_comm. unfold z, Qdiv. apply Qfloor_le. intuition.
    unfold eqA; unfold Qdiv; rewrite Qmult_inv_r. ring. auto with *.
    apply Qle_refl. unfold f_Q, f_Z. set (z := x / delta).
    rewrite Qlt_minus_iff, Qplus_comm. unfold Qminus. 
    rewrite Qopp_plus, Qopp_opp.
    rewrite <- Qplus_assoc. rewrite Qplus_comm.
    rewrite <- Qlt_minus_iff. 
    set (t := inject_Z (Qfloor z) * delta).
    setoid_replace (delta) with (delta * (delta / delta)).
    unfold t. rewrite Qmult_comm. rewrite <- Qmult_plus_distr_r. 
    unfold Qdiv. rewrite Qmult_inv_r. rewrite Qmult_comm.
    setoid_replace (x) with (x * (delta / delta)). 
    unfold Qdiv. rewrite Qmult_comm. rewrite <- Qmult_assoc.
    rewrite Qmult_comm. apply Qmult_lt_compat_r. hyp.
    rewrite Qmult_comm. unfold z, Qdiv.
    generalize (Qlt_floor (x * / delta)).  
    cut (inject_Z (Qfloor (x * / delta) + 1)%Z = inject_Z (Qfloor (x * / delta)) + 1).
    intro. rewrite H0; auto. unfold inject_Z, Qplus. simpl.
    rewrite Zmult_1_r. auto.
    unfold eqA; unfold Qdiv; rewrite Qmult_inv_r. ring. auto with *.  
    auto with *. unfold eqA; unfold Qdiv; rewrite Qmult_inv_r. ring.
    auto with *. 
  Qed.

(***********************************************************************)
(* x - y = (f(x) - f(y)) * delta + t - u >= delta, - delta <= t - u < delta *)

  Lemma Qplus_permute : forall n m p, n + (m + p) == m + (n + p).

  Proof.
    intros. ring.  
  Qed.
  
  Lemma Qmult_minus_distr_r : forall n m p, (n + - m) * p == n * p + - (m * p).

  Proof.
    intros x y z. ring.   
  Qed.

  Lemma Qplus_lt_compat_l : forall n m p, n < m -> p + n < p + m.

  Proof.
    unfold Qplus, Qlt; intros (x1, x2) (y1, y2) (z1, z2);
      simpl; simpl_mult.
    Open Scope Z_scope.
    intros.
    match goal with |- ?a < ?b => ring_simplify a b end.
    apply Zplus_lt_compat_l. rewrite Zmult_comm.
    rewrite <- !Zmult_assoc. rewrite Zmult_assoc. 
    rewrite Zmult_comm. set (a := ' z2 ^ 2 * (' y2 * x1)). 
    rewrite Zmult_comm. rewrite <- Zmult_assoc. unfold a.
    apply Zmult_lt_compat_l. apply Zmult_lt_0_compat; apply Zgt_lt;
    apply Zgt_pos_0.
    rewrite Zmult_comm. hyp.
    Close Scope Z_scope.
  Qed.

  Lemma Qplus_lt_compat_r : forall n m p, n < m -> n + p < m + p.

  Proof.
    intros n m p H. rewrite <- Qplus_comm. set (a := p + n). rewrite Qplus_comm. 
    unfold a. apply Qplus_lt_compat_l. hyp. 
  Qed.

  Lemma Qplus_le_lt_compat : forall x y z w, x <= y -> z < w -> x + z < y + w.
    
  Proof.
    intros. apply Qle_lt_trans with (y := y + z). apply Qplus_le_compat. hyp. 
    apply Qle_refl. apply Qplus_lt_compat_l. hyp.
  Qed.

  Lemma Qplus_lt_le_compat : forall x y z w, x < y -> z <= w -> x + z < y + w.
    
  Proof.
    intros. apply Qlt_le_trans with (y := y + z). apply Qplus_lt_compat_r. hyp. 
    apply Qplus_le_compat. apply Qle_refl. hyp.
  Qed.

(*FIXME: Change name*)
  Lemma terms_cond : forall t u, 0 <= t /\ t < delta /\ 0 <= u /\ u < delta -> 
    - delta < t + - u /\ t + - u < delta.
    
  Proof.
    intros. intuition. rewrite Qplus_comm. 
    rewrite Qlt_minus_iff. rewrite Qopp_opp. rewrite <- Qplus_assoc. 
    rewrite Qplus_comm.
    rewrite <- Qlt_minus_iff. rewrite <- (Qplus_0_l (u)).
    apply Qplus_le_lt_compat. hyp. hyp.
    rewrite Qplus_comm; rewrite Qlt_minus_iff; rewrite Qopp_plus; rewrite Qopp_opp.
    rewrite Qplus_assoc. rewrite <- Qlt_minus_iff. rewrite <- (Qplus_0_r (t)).
    apply Qplus_lt_le_compat. hyp. hyp. 
  Qed.
  
  Lemma Qle_plus_swap : forall n m p, n + p <= m <-> n <= m - p.

  Proof.
    intros x y z; intros. split. intro. rewrite <- (Qplus_0_r x). 
    rewrite <- (Qplus_opp_r z).
    rewrite Qplus_assoc. apply Qplus_le_compat. hyp.
    apply Qopp_le_compat. apply Qle_refl.
    intro. rewrite <- (Qplus_0_r y). rewrite <- (Qplus_opp_r z). 
    set (a := x + z). 
    rewrite Qplus_permute. rewrite Qplus_comm. unfold a. apply Qplus_le_compat. 
    hyp. apply Qle_refl.
  Qed.

  Lemma Qlt_plus_swap : forall n m p, n < m + p <-> n - p < m.

  Proof.
    intros x y z; intros. split. intro. unfold Qminus in |- *. 
    rewrite Qplus_comm. 
    rewrite <- (Qplus_0_l y). rewrite <- (Qplus_opp_r z). set (a := -z + x). 
    rewrite Qplus_comm. rewrite Qplus_assoc. rewrite Qplus_comm. unfold a.
    apply Qplus_lt_compat_l. hyp. intro. rewrite Qplus_comm. 
    rewrite <- (Qplus_0_l x).
    rewrite <- (Qplus_opp_r z). rewrite <- Qplus_assoc. apply Qplus_lt_compat_l.
    rewrite Qplus_comm. hyp. 
  Qed.

  Lemma Qmult_gt_0_lt_reg_r : forall n m p, p > 0 -> n * p < m * p -> n < m.

  Proof.
    intros (a1,a2) (b1,b2) (c1,c2); unfold Qlt; simpl.
    Open Scope Z_scope.
    simpl_mult.
    replace (a1*c1*('b2*'c2)) with ((a1*'b2)*(c1*'c2)) by ring.
    replace (b1*c1*('a2*'c2)) with ((b1*'a2)*(c1*'c2)) by ring.
    intros; apply Zmult_lt_reg_r with (c1*'c2); auto with zarith.
    apply Zmult_lt_0_compat. omega. compute; auto. 
    Close Scope Z_scope.
  Qed.

  Lemma Qmult_lt_reg_r : forall n m p, 0 < p -> n * p < m * p -> n < m.
    
  Proof.
    intros a b c H0 H1. apply Qmult_gt_0_lt_reg_r with c; hyp.  
  Qed.

  Lemma wf_Q_N : forall x y, x >= 0 /\ y >= 0 -> gtAQ x y -> (f (y) < f (x))%nat.
    
  Proof.
    intros. assert (Hx := poly_exp x). assert (Hy := poly_exp y).
    unfold gtAQ, Qminus in H0. induction Hx; induction Hy.
    elim H1; elim H2; intros. rewrite H3 in H0; rewrite H5 in H0. clear H1; 
    clear H2.
    rewrite Qplus_comm in H0. rewrite Qopp_plus in H0. 
    rewrite <- Qplus_permute in H0.
    repeat rewrite Qplus_assoc in H0; rewrite <- Qmult_minus_distr_r in H0. 
    rewrite <- Qplus_comm in H0; rewrite Qplus_permute in H0.
    assert (Hr := terms_cond x0 x1). induction Hr.
    apply Qplus_lt_compat_l with (p := (f_Q x + - f_Q y) * delta) in H2.
    generalize (Qle_lt_trans _ _ _ H0 H2).
    intros. rewrite Qlt_plus_swap in H7. unfold Qminus in H7.
    rewrite Qplus_opp_r in H7. rewrite Qmult_minus_distr_r in H7. 
    rewrite <- Qlt_minus_iff in H7.
    apply Qmult_lt_reg_r with (p := delta) in H7. 
    unfold f_Z in H7. unfold f. 
    apply Zabs_nat_lt. intuition.
    unfold f. apply Q_floor_pos.
    apply Qle_shift_div_l. hyp. 
    rewrite Qmult_0_l. hyp. 
    unfold Qlt in H7. simpl in H7. 
    do 2 rewrite Zmult_1_r in H7. hyp.
    hyp. tauto. tauto. tauto. tauto.
  Qed.

(***********************************************************************)
(* Well-founded relations and rational numbers *)

  Definition gtA_not_neg x y := gtAQ x y /\ x >= 0 /\ y >= 0.

  Theorem well_founded_gtA_not_neg : well_founded (transp gtA_not_neg).

  Proof.
    unfold transp, gtA_not_neg. 
    apply wf_incl with (R2 := fun x y : Q => (f y > f x)%nat). 
    unfold inclusion. intros. apply wf_Q_N. tauto. tauto.
    apply (@wf_inverse_image Q nat lt f).
    apply lt_wf.
  Qed.

End Well_found_Rational.