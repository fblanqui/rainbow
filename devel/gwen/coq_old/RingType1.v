(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-05-20
- Frederic Blanqui, 2005-02-25

Ring structure. 
*)

Set Implicit Arguments.

Require Import Ring Ring_theory LogicUtil RelExtras1 Setoid EqUtil ZUtil Morphisms.

(***********************************************************************)
(** Module type for building the theory module of some ring *)

Class Ring := {
  ring_setoid :> Setoid;
  ring_A0 : s_typ;
  ring_A1 : s_typ;
  ring_Aplus : s_typ -> s_typ -> s_typ;
  ring_Amult : s_typ -> s_typ -> s_typ;
  ring_Aopp : s_typ -> s_typ;
  ring_Asub : s_typ -> s_typ -> s_typ;
  ring_Aplus_mor : Proper (s_eq ==> s_eq ==> s_eq) ring_Aplus;
  ring_Amult_mor: Proper (s_eq ==> s_eq ==> s_eq) ring_Amult;
  ring_Aopp_mor : Proper (s_eq ==> s_eq) ring_Aopp;
  ring_Asub_mor : Proper (s_eq ==> s_eq ==> s_eq) ring_Asub;
  ring_A_semi_ring : ring_theory ring_A0 ring_A1 ring_Aplus ring_Amult ring_Asub ring_Aopp s_eq}.

(***********************************************************************)
(* Integers as a ring *)

Require Import ZArith.

Instance Int_as_Ring : Ring.

Proof.
  apply Build_Ring with (ring_setoid := Leibniz_Setoid Z)
   (ring_A0 := 0%Z) (ring_A1:= 1%Z) (ring_Aplus := Zplus) (ring_Amult:=Zmult)
   (ring_Aopp:= Zopp) (ring_Asub := fun x y => Zplus x (Zopp y)).
  simpl. intros x x' xx' y y' yy'. rewrite xx'. rewrite yy'. auto.
  simpl. intros x x' xx' y y' yy'. rewrite xx'. rewrite yy'. auto.
  simpl. intros x x' xx'. rewrite xx'. auto.
  simpl. intros x x' xx' y y' yy'. rewrite xx'. rewrite yy'. auto.
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

(***********************************************************************)
(* Rational numbers as a ring *)

Require Import QArith.

Instance Q_as_Ring : Ring.
Proof.
  apply Build_Ring with (ring_setoid := Leibniz_Setoid Q)
   (ring_A0 := 0#1) (ring_A1:= 1#1) (ring_Aplus := Qplus) (ring_Amult:=Qmult)
   (ring_Aopp:= Qopp) (ring_Asub := fun x y => Qplus x (Qopp y)).
  simpl. intros x x' xx' y y' yy'. rewrite xx'. rewrite yy'. auto.
  simpl. intros x x' xx' y y' yy'. rewrite xx'. rewrite yy'. auto.
  simpl. intros x x' xx'. rewrite xx'. auto.
  simpl. intros x x' xx' y y' yy'. rewrite xx'. rewrite yy'. auto.
  set (Qsub := fun x y : Q => x + -y).
  simpl. 
  (* FIXME *)
  (*apply Qsrt.*)
Admitted.  





Module Type Ring.
  
  Declare Module Export ES : Eqset_dec.
 
  Parameter A0 : A.
  Parameter A1 : A.

  Parameter Aadd : A -> A -> A.
  Add Morphism Aadd with signature eqA ==> eqA ==> eqA as Aadd_mor.

  Parameter Amul : A -> A -> A.
  Add Morphism Amul with signature eqA ==> eqA ==> eqA as Amul_mor.

  Parameter Aopp : A -> A.
  Add Morphism Aopp with signature eqA ==> eqA as Aopp_mor.

  Definition Asub : A -> A -> A := fun x y => Aadd x (Aopp y).
  Add Morphism Asub with signature eqA ==> eqA ==> eqA as Asub_mor.
  
  Parameter Aring : ring_theory A0 A1 Aadd Amul Asub Aopp eqA.

End Ring.

(***********************************************************************)
(** Properties of rings *)
 
Module RingTheory (Export R : Ring).

  Notation "0" := A0.
  Notation "1" := A1.
  Notation "x + y" := (Aadd x y).
  Notation "x * y" := (Amul x y).
  Notation "- x" := (Aopp x).
  Notation "x - y" := (Asub x y).

  Add Setoid A eqA sid_theoryA as A_Setoid.
  Add Ring Aring : Aring.

(***********************************************************************)
(** boolean equality *)

  Definition beqA x y :=
    match eqA_dec x y with
      | left _ => true
      | right _ => false
    end.

  Lemma beqA_ok : forall x y, beqA x y = true <-> x =A= y.

  Proof.
  intros. unfold beqA. case (eqA_dec x y); intuition. discr.
  Qed.

(***********************************************************************)
(** power function *)

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
(** properties of ring type *)

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
(* Integers as a ring *)

Require Import ZArith. 

Module Int <: SetA.
  Definition A := Z.
End Int.

Module IntEqset := Eqset_def Int.

Module IntEqset_dec <: Eqset_dec.
  Module Export Eq := IntEqset.
  Definition eqA_dec := dec_beq beq_Z_ok.
End IntEqset_dec.

Module IntRing <: Ring.

  Module Export ES := IntEqset_dec.

  Add Setoid A eqA sid_theoryA as A_Setoid.
 
  Definition A0 := 0%Z.
  Definition A1 := 1%Z.

  Definition Aadd := Zplus.
  
  Add Morphism Aadd with signature eqA ==> eqA ==> eqA as Aadd_mor.
  
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.
  
  Definition Amul := Zmult.
  
  Add Morphism Amul with signature eqA ==> eqA ==> eqA as Amul_mor.
  
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.  
 
  Definition Aopp := Zopp.
  
  Add Morphism Aopp with signature eqA ==> eqA as Aopp_mor.
  
  Proof.
    intros. rewrite H. refl.
  Qed. 

  Definition Asub : Z -> Z -> Z := fun x y => Zplus x (Zopp y).

  Add Morphism Asub with signature eqA ==> eqA ==> eqA as Asub_mor.
 
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.
 
  Lemma Aring : ring_theory A0 A1 Aadd Amul Asub Aopp eqA.
  
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
    intro. unfold eqA, A0, Aadd, Aopp, IntEqset.A, Int.A. omega. 
  Qed.

End IntRing.

Module IntRingTheory := RingTheory IntRing.

(***********************************************************************)
(* Rational numbers as a ring *)

Require Import QArith.

Module Rat_Eqset <: Eqset.
 
  Definition A := Q.
  Definition eqA := Qeq.
  Definition sid_theoryA : Setoid_Theory A eqA.
 
  Proof.
    unfold eqA. constructor. 
    unfold Reflexive. refl. 
    unfold Symmetric. symmetry. hyp. 
    unfold Transitive. intros. transitivity y; hyp. 
  Qed.

End Rat_Eqset.

Module Rat_Eqset_dec <: Eqset_dec.
  
  Module Export Eq := Rat_Eqset.
   
  Lemma eqA_dec : forall x y, {eqA x y} + {~eqA x y}.
  
  Proof.
  unfold eqA. unfold Qeq. intros. apply (dec_beq beq_Z_ok).
  Defined.

End Rat_Eqset_dec.

Module RatRing <: Ring.
  
  Module Export ES := Rat_Eqset_dec.

  Add Setoid A eqA sid_theoryA as A_Setoid.
  
  Definition A0 := 0#1.  
  Definition A1 := 1#1.  
  
  Definition Aadd := Qplus.
  
  Add Morphism Aadd with signature eqA ==> eqA ==> eqA as Aadd_mor.
 
  Proof.
    intros. rewrite H. rewrite H0. refl. 
  Qed.

  Definition Amul := Qmult.

  Add Morphism Amul with signature eqA ==> eqA ==> eqA as Amul_mor.
  
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition Aopp := Qopp.

  Add Morphism Aopp with signature eqA ==> eqA as Aopp_mor.
 
  Proof.
    intros. rewrite H. refl. 
  Qed.

  Definition Asub : Q -> Q -> Q := fun x y => Qplus x (Qopp y).

  Add Morphism Asub with signature eqA ==> eqA ==> eqA as Asub_mor.
 
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition Aring := Qsrt.

End RatRing.

Module RatRingTheory := RingTheory RatRing.

