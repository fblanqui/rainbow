(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-05-20
- Frederic Blanqui, 2005-02-25

Ring structure.

- Ly Kim Quyen, 2013-08-22

Remove Module Type structure by Section to be able to use in Rainbow.
*)

Set Implicit Arguments.

Require Export Ring Ring_theory.
Require Import LogicUtil RelExtras2 Setoid EqUtil ZUtil Morphisms.

(***********************************************************************)
(** ** Ring structure type. *)

Section Ring.

  Variable e : Eqset.

  Definition eqA := eqA e.

  Definition sid_theoryA := sid_theoryA e.

  Add Setoid A eqA sid_theoryA as A_Setoid.

  Hint Resolve (Seq_refl A eqA sid_theoryA) : sets.
  Hint Resolve (Seq_trans A eqA sid_theoryA) : sets.
  Hint Resolve (Seq_sym A eqA sid_theoryA) : sets.

  Record Ring := mkRing {
    A0 : A;
    A1 : A;
    Aadd : A -> A -> A;
    Amul : A -> A -> A;
    Aopp : A -> A;
    Asub : A -> A -> A;
    Aring : ring_theory A0 A1 Aadd Amul Asub Aopp eqA
  }.

  Variable r: Ring.
  
  (* Need to declare ring as a morphism to be able to define a [Add
  Ring] later. *)

  Parameter Aadd_mor : Proper (eqA ==> eqA ==> eqA) (Aadd r).
  Parameter Amul_mor : Proper (eqA ==> eqA ==> eqA) (Amul r).
  Parameter Aopp_mor : Proper (eqA ==> eqA) (Aopp r).
  Parameter Asub_mor : Proper (eqA ==> eqA ==> eqA) (Asub r).

End Ring.

(***********************************************************************)
(** ** Properties of rings. *)

Section RingTheory.

  Variable e : Eqset.

  Variable r: Ring e.

  Notation Aring := (Aring r).

  Notation eqA := (eqA e).

  Notation sid_theoryA := (sid_theoryA e).

  Add Setoid A eqA sid_theoryA as A_Setoid'.

  Add Ring Aring : Aring.

  (***********************************************************************)
  (** Boolean equality *)

  Notation eqA_dec := (eqA_dec e).

  Definition beqA x y :=
    match eqA_dec x y with
      | left _ => true
      | right _ => false
    end.

  Notation "x =A= y" := (eqA x y) (at level 70).

  Lemma beqA_ok : forall x y, beqA x y = true <-> x =A= y.

  Proof.
  intros. unfold beqA. case (eqA_dec x y); intuition.
  Qed.

  (***********************************************************************)
  (** Power function *)
  
  Notation A0 := (A0 r).
  Notation "0" := A0.

  Notation A1 := (A1 r).
  Notation "1" := A1.

  Notation Aadd := (Aadd r).
  Notation "x + y" := (Aadd x y).

  Notation Amul := (Amul r).
  Notation "x * y" := (Amul x y).

  Notation Aopp := (Aopp r).
  Notation "- x" := (Aopp x).

  Notation Asub := (Asub r).
  Notation "x - y" := (Asub x y).

  Fixpoint power x n {struct n} :=
    match n with
      | 0 => 1
      | S n' => x * power x n'
    end.

  Notation "x ^ n" := (power x n).

  Lemma power_add : forall x n1 n2, x ^ (n1 + n2) =A= x ^ n1 * x ^ n2.

  Proof.
  induction n1; simpl; intros. ring. rewrite IHn1. ring.
  Qed.

  Add Morphism power with signature eqA ==> @eq nat ==> eqA as power_eqA.

  Proof.
    induction y0; simpl; intros. refl. rewrite IHy0. rewrite H. refl.
  Qed.

  (***********************************************************************)
  (** Properties of ring type *)

  Lemma Aadd_0_r : forall x, x + 0 =A= x.

  Proof.
  intros. ring. 
  Qed.

  Lemma Amul_0_l : forall x, 0 * x =A= 0.

  Proof.
  intros. ring. 
  Qed. 

  Lemma Asub_def : forall x y, x - y =A= x + - y.

  Proof.
  intros. ring.
  Qed.
   
  Lemma Aopp_def : forall x, x + (-x) =A= 0.
  
  Proof.
  intros. ring.
  Qed.

  Lemma Aopp_opp : forall x, - - x =A= x.
  
   Proof.
   intros. ring.
   Qed.
 
  Lemma add_minus : forall x y, x =A= x + y - y.

  Proof.
  intros. ring.
  Qed.
  
  Lemma add_permute : forall n m p, n + (m + p) =A= m + (n + p).

  Proof.
  intros. ring.
  Qed.

End RingTheory.

(***********************************************************************)
(** ** Integers as a ring. *)

Require Import ZArith.

Section Int.
  
  Definition ZA := Z.
  Definition ZeqA := Z.eq.

  Definition Zsid_theoryA : Setoid_Theory ZA ZeqA.

  Proof.
    unfold ZeqA. constructor.
    unfold Reflexive. refl.
    unfold Symmetric. sym. hyp.
    unfold Transitive. intros. trans y; hyp.
  Qed.

End Int.

Section Int_Eqset_dec.
  
  Definition ZeqA_dec := dec_beq beq_Z_ok.
  
End Int_Eqset_dec.

Section IntRing.

  Add Setoid ZA ZeqA Zsid_theoryA as ZA_Setoid.

  Definition ZA0 := 0%Z.
  Definition ZA1 := 1%Z.
  
  Definition ZAadd := Zplus.

  Add Morphism ZAadd with signature ZeqA ==> ZeqA ==> ZeqA as ZAdd_mor.

  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition ZAmul := Zmult.

  Add Morphism ZAmul with signature ZeqA ==> ZeqA ==> ZeqA as ZAmul_mor.

  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition ZAopp := Zopp.

  Add Morphism ZAopp with signature ZeqA ==> ZeqA as ZAopp_mor.

  Proof.
    intros. rewrite H. refl.
  Qed.

  Definition ZAsub : Z -> Z -> Z := fun x y => Zplus x (Zopp y).

  Add Morphism ZAsub with signature ZeqA ==> ZeqA ==> ZeqA as ZAsub_mor.

  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Lemma ZAring : ring_theory ZA0 ZA1 ZAadd ZAmul ZAsub ZAopp ZeqA.

  Proof.
    constructor.
    exact Zplus_0_l.
    exact Zplus_comm.
    exact Zplus_assoc.
    exact Zmult_1_l.
    exact Zmult_comm.
    exact Zmult_assoc.
    exact Zmult_plus_distr_l.
    refl.
    intro. unfold ZeqA, ZA0, ZAadd, ZAopp, Z.eq. omega.
  Qed.
    
End IntRing.

(***********************************************************************)
(** ** Rational numbers as a ring .*)

Require Import QArith.

Section Rat_Eqset.

  Definition QA := Q.

  Definition QeqA := Qeq.

  Definition Qsid_theoryA : Setoid_Theory QA QeqA.

  Proof.
    unfold QeqA. constructor.
    unfold Reflexive. refl.
    unfold Symmetric. sym. hyp.
    unfold Transitive. intros. transitivity y; hyp.
  Qed.

End Rat_Eqset.

Section Rat_Eqset_dec.

  Lemma QeqA_dec : forall x y, {QeqA x y} + {~QeqA x y}.

  Proof.
    unfold QeqA. unfold Qeq. intros. apply (dec_beq beq_Z_ok).
  Defined.

  (* Define beqAq of type Q. *)

  Definition QbeqA x y :=
    match QeqA_dec x y with
      | left _ => true
      | right _ => false
    end.

  Notation "x =A= y" := (QeqA x y) (at level 70).

  Lemma QbeqA_ok : forall x y, QbeqA x y = true <-> x =A= y.

  Proof.
  intros. unfold QbeqA. case (QeqA_dec x y); intuition.
  Qed.

End Rat_Eqset_dec.

Section RatRing.
  
  Add Setoid QA QeqA Qsid_theoryA as QA_Setoid.
  
  Definition QA0 := 0#1.
  Definition QA1 := 1#1.

  Definition QAadd := Qplus.

  Add Morphism QAadd with signature QeqA ==> QeqA ==> QeqA as QAdd_mor.
    
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition QAmul := Qmult.

  Add Morphism QAmul with signature QeqA ==> QeqA ==> QeqA as QAmul_mor.

  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition QAopp := Qopp.

  Add Morphism QAopp with signature QeqA ==> QeqA as QAopp_mor.

  Proof.
    intros. rewrite H. refl.
  Qed.

  Definition QAsub : Q -> Q -> Q := fun x y => Qplus x (Qopp y).
  
  Add Morphism QAsub with signature QeqA ==> QeqA ==> QeqA as QAsub_mor.

  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition QAring := Qsrt.
  
  Notation "x ^ n" := (Qpower x n).
  Notation "x =A= y" := (QeqA x y) (at level 70).

  Lemma Qpower_add : forall x n1 n2, x ^ (n1 + n2) =A= x ^ n1 * x ^ n2.

  Proof.
    induction n1; simpl in *; intros; try discr; unfold QeqA; try ring.
    unfold Qpower. destruct n2; try ring.
    unfold Qpower_positive.  
   
  Admitted.

  Add Morphism Qpower with signature QeqA ==> @eq Z ==> QeqA as Qpower_eqA.

  Proof.
    induction y0; simpl; intros. refl. rewrite H. refl.
    unfold QeqA. rewrite H. refl.
  Qed.

End RatRing.