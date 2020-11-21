(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski, 2007-04-14

* Semi-ring structure.

*)

Require Export Ring Ring_theory.
Require Import RelDec Relations Max Arith Compare LogicUtil Bool RelExtras2
  Setoid EqUtil NatUtil ZUtil Morphisms.

(***********************************************************************)
(** ** Semi-ring structure type. *)

Section SemiRingType.

  Variable e: Eqset.

  Definition eqA := eqA e.

  Definition sid_theoryA := sid_theoryA e.

  Add Setoid A eqA sid_theoryA as A_Setoid.

  Hint Resolve (Seq_refl A eqA sid_theoryA) : sets.
  Hint Resolve (Seq_trans A eqA sid_theoryA) : sets.
  Hint Resolve (Seq_sym A eqA sid_theoryA) : sets.

  Record SemiRingType := mkSemiRingType {
    A0 : A;
    A1 : A;
    Aplus : A -> A -> A;
    Amult : A -> A -> A;
    A_semi_ring : semi_ring_theory A0 A1 Aplus Amult eqA
  }.

  Variable s: SemiRingType.

  Parameter Aplus_mor : Proper (eqA ==> eqA ==> eqA) (Aplus s).
  Parameter Amult_mor : Proper (eqA ==> eqA ==> eqA) (Amult s).

End SemiRingType.

(** Some derived results about the semi-ring structure. *)

Section SemiRing.
 
  Variable e: Eqset.

  Variable s: SemiRingType e.

  Notation A_semi_ring := (A_semi_ring e s).

  Definition Aplus_comm := SRadd_comm A_semi_ring.

  Definition Aplus_assoc := SRadd_assoc A_semi_ring.

  Definition Aplus_0_l := SRadd_0_l A_semi_ring.

  Definition Amult_comm := SRmul_comm A_semi_ring.

  Definition Amult_assoc := SRmul_assoc A_semi_ring.

  Definition Amult_0_l := SRmul_0_l A_semi_ring.

  Definition Amult_1_l := SRmul_1_l A_semi_ring.

  Definition A_plus_mult_distr_l := SRdistr_l A_semi_ring.

  Notation eqA := (eqA e). 
  Notation "X =A= Y" := (eqA X Y) (at level 70).

  Notation Aplus := (Aplus e s).
  Notation "X + Y" := (Aplus X Y).

  Notation Amult := (Amult e s).
  Notation "X * Y" := (Amult X Y).

  Notation A0 := (A0 e s).
  Notation A1 := (A1 e s).

  Notation sid_theoryA := (sid_theoryA e).

  Add Setoid A eqA sid_theoryA as A_Setoid'.

  Lemma Aplus_0_r : forall n, (n + A0) =A= n.

  Proof.
    intros. rewrite Aplus_comm. apply Aplus_0_l.
  Qed.
  
  Lemma Amult_0_r : forall n, n * A0 =A= A0.

  Proof.
    intros. rewrite Amult_comm. apply Amult_0_l.
  Qed.

  Lemma Amult_1_r : forall n, n * A1 =A= n.

  Proof.
    intros. rewrite Amult_comm. apply Amult_1_l.
  Qed.

  Lemma A_plus_mult_distr_r : forall m n p,
    m * (n + p) =A= m * n + m * p.

  Proof.
    intros. rewrite Amult_comm. 
    rewrite (Amult_comm m n). rewrite (Amult_comm m p).
    apply A_plus_mult_distr_l.
  Qed.

  Hint Rewrite Aplus_0_l Aplus_0_r Amult_0_l Amult_0_r 
    Amult_1_l Amult_1_r : arith.

  Add Ring Aring : A_semi_ring.

End SemiRing.

(***********************************************************************)
(** ** Natural numbers as a semi-ring. *)

Require Import Arith.

Section Nat.

  Definition AN := nat.

  Definition eqAN := eq(A:=AN).

  Definition sid_theoryAN : Setoid_Theory AN eqAN.

  Proof.
    unfold eqAN. constructor.
    unfold Reflexive. refl.
    unfold Symmetric. sym. hyp.
    unfold Transitive. intros. trans y; hyp.
  Qed.

End Nat.

Section Nat_Eqset_dec.

  Definition eqA_decN := dec_beq beq_nat_ok.

End Nat_Eqset_dec.

Section NSemiRingT.

  Add Setoid AN eqAN sid_theoryAN as A_SetoidN.

  Definition A0N := 0.
  Definition A1N := 1.
  Definition AplusN := plus.
  
  Add Morphism AplusN with signature  eqAN ==> eqAN ==> eqAN as Aplus_morN.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition AmultN := mult.

  Add Morphism AmultN with signature eqAN ==> eqAN ==> eqAN as Amult_morN.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition A_semi_ringN := natSRth.

End NSemiRingT.

(***********************************************************************)
(** ** BigN natural numbers as a semi-ring. *)

Require Import BigN.

Section BigNat_Eqset.

  Definition AbN := bigN.
  Definition eqAbN := BigN.eq.

  Definition sid_theoryAbN : Setoid_Theory AbN eqAbN.

  Proof.
    unfold eqAbN. constructor.
    unfold Reflexive. refl.
    unfold Symmetric. sym. hyp.
    unfold Transitive. intros. trans y; hyp.
  Qed.

End BigNat_Eqset.

Section BigNat_Eqset_dec.

  Lemma eqA_decbN : forall x y, {eqAbN x y}+{~eqAbN x y}.

  Proof.
    unfold eqAbN. unfold BigN.eq. intros. apply (dec_beq beq_Z_ok).
  Defined.

End BigNat_Eqset_dec.

Section BigNSemiRingT.

  Add Setoid AbN eqAbN sid_theoryAbN as A_SetoidbN.

  Definition A0bN := BigN.zero.
  Definition A1bN := BigN.one.
  Definition AplusbN := BigN.add.

  Add Morphism AplusbN with signature eqAbN ==> eqAbN ==> eqAbN as Aplus_morbN.

  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition AmultbN := BigN.mul.

  Add Morphism AmultbN with signature eqAbN ==> eqAbN ==> eqAbN as Amult_morbN.

  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition A_semi_ringbN := BigNring.

End BigNSemiRingT.

(***********************************************************************)
(** ** Integers as a semi-ring. *)

Require Import ZArith.

Section Int.
  
  Definition Az := Z.
  Definition eqAz := Z.eq.

  Definition sid_theoryAz : Setoid_Theory Az eqAz.

  Proof.
    unfold eqAz. constructor.
    unfold Reflexive. refl.
    unfold Symmetric. sym. hyp.
    unfold Transitive. intros. trans y; hyp.
  Qed.
  
End Int.

Section Int_Eqset_dec.

  Definition eqA_decz := dec_beq beq_Z_ok.

End Int_Eqset_dec.

Section ZSemiRingT.

  Add Setoid Az eqAz sid_theoryAz as A_Setoidz.

  Definition A0z := 0%Z.
  Definition A1z := 1%Z.
  Definition Aplusz := Zplus.

  Add Morphism Aplusz with signature eqAz ==> eqAz ==> eqAz as Aplus_morz.

  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition Amultz := Zmult.

  Add Morphism Amultz with signature eqAz ==> eqAz ==> eqAz as Amult_morz.

  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Lemma A_semi_ringz : semi_ring_theory A0z A1z Aplusz Amultz eqAz.

  Proof.
    constructor.
    exact Zplus_0_l.
    exact Zplus_comm.
    exact Zplus_assoc.
    exact Zmult_1_l.
    exact Zmult_0_l.
    exact Zmult_comm.
    exact Zmult_assoc.
    exact Zmult_plus_distr_l.
  Qed.

End ZSemiRingT.

(***********************************************************************)
(** ** BigZ integers as a semi-ring. *)

Require Import BigZ.

Section BigInt_Eqset.

  Definition Abz := bigZ.
  Definition eqAbz := BigZ.eq.

  Definition sid_theoryAbz : Setoid_Theory Abz eqAbz.

  Proof.
    unfold eqAbz. constructor.
    unfold Reflexive. refl.
    unfold Symmetric. sym. hyp.
    unfold Transitive. intros. trans y; hyp.
  Qed.

End BigInt_Eqset.

Section BigInt_Eqset_dec.

  Lemma eqA_decbz : forall x y, {eqAbz x y}+{~eqAbz x y}.

  Proof.
    unfold eqAbz. unfold BigZ.eq. intros. apply (dec_beq beq_Z_ok).
  Defined.

End BigInt_Eqset_dec.

Section BigZSemiRingT.

  Add Setoid Abz eqAbz sid_theoryAbz as A_Setoidbz.

  Definition A0bz := BigZ.zero.
  Definition A1bz := BigZ.one.
  Definition Aplusbz := BigZ.add.

  Add Morphism Aplusbz with signature eqAbz ==> eqAbz ==> eqAbz as Aplus_morbz.

  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition Amultbz := BigZ.mul.

  Add Morphism Amultbz with signature eqAbz ==> eqAbz ==> eqAbz as Amult_morbz.

  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Lemma A_semi_ringbz : semi_ring_theory A0bz A1bz Aplusbz Amultbz eqAbz.

  Proof.
    constructor.
    exact (Radd_0_l BigZring).
    exact (Radd_comm BigZring).
    exact (Radd_assoc BigZring).
    exact (Rmul_1_l BigZring).
    exact BigZ.mul_0_l.
    exact (Rmul_comm BigZring).
    exact (Rmul_assoc BigZring).
    exact BigZ.mul_add_distr_r.
  Qed.

End BigZSemiRingT.

(***********************************************************************)
(** ** Arctic semi-ring over naturals with minus infinity and 
    plus-max operations. *)

Inductive ArcticDom : Type := 
| Pos (n : nat)
| MinusInf.

Definition beq_ArcticDom x y :=
  match x, y with
    | Pos x', Pos y' => beq_nat x' y'
    | MinusInf, MinusInf => true
    | _, _ => false
  end.

Lemma beq_ArcticDom_ok : forall x y, beq_ArcticDom x y = true <-> x = y.

Proof.
  unfold beq_ArcticDom. destruct x; destruct y; simpl; try (intuition; discr).
  rewrite beq_nat_ok. intuition. inversion H. refl.
Qed.

Definition is_finite v :=
  match v with
    | MinusInf => false
    | _ => true
  end.

Lemma is_finite_ok : forall v, is_finite v = true <-> v <> MinusInf.

Proof.
  intro. destruct v; simpl; intuition. discr.
Qed.

Section Artic.

  Definition Ar := ArcticDom.
  Definition eqAr := eq(A:=Ar).

  Definition sid_theoryAr : Setoid_Theory Ar eqAr.

  Proof.
    unfold eqAr. constructor.
    unfold Reflexive. refl.
    unfold Symmetric. sym. hyp.
    unfold Transitive. intros. trans y; hyp.
  Qed.

End Artic.

Section Artic_Eqset_dec.

  Definition eqA_decr := dec_beq beq_ArcticDom_ok.

End Artic_Eqset_dec.

Section ArticSemiRingT.

  Add Setoid Ar eqAr sid_theoryAr as A_Setoidr.

  Definition A0r := MinusInf.
  Definition A1r := Pos 0.

  (** Max is a <+> operation in the semi-ring. *)

  Definition Aplusr m n :=
    match m, n with
    | MinusInf, n => n
    | m, MinusInf => m
    | Pos m, Pos n => Pos (max m n)
    end.

  Add Morphism Aplusr with signature eqAr ==> eqAr ==> eqAr as Aplus_morr.

  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  (** Plus is a <*> operation in the semi-ring. *)

  Definition Amultr m n := 
    match m, n with
    | MinusInf, _ => MinusInf
    | _, MinusInf => MinusInf
    | Pos m, Pos n => Pos (m + n)
    end.

  Add Morphism Amultr with signature eqAr ==> eqAr ==> eqAr as Amult_morr.

  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Lemma A_plus_comm : forall m n, Aplusr m n = Aplusr n m.

  Proof.
    intros. unfold Aplusr. destruct m; destruct n; trivial.
    rewrite max_comm. trivial.
  Qed.

  Lemma A_plus_assoc : forall m n p, Aplusr m (Aplusr n p) = Aplusr (Aplusr m n) p.

  Proof.
    intros. unfold Aplusr.
    destruct m; destruct n; destruct p; trivial.
    rewrite max_assoc. trivial.
  Qed.

  Lemma A_mult_comm : forall m n, Amultr m n = Amultr n m.

  Proof.
    intros. unfold Amultr. destruct m; destruct n; trivial.
    rewrite plus_comm. trivial.
  Qed.

  Lemma A_mult_assoc : forall m n p, Amultr m (Amultr n p) = Amultr (Amultr m n) p.

  Proof.
    intros. unfold Amultr.
    destruct m; destruct n; destruct p; trivial.
    rewrite plus_assoc. trivial.
  Qed.

  Import Compare. Import Max.

  Lemma A_mult_plus_distr : forall m n p,
    Amultr (Aplusr m n) p = Aplusr (Amultr m p) (Amultr n p).

  Proof.
    intros. unfold Amultr, Aplusr.
    destruct m; destruct n; destruct p; trivial.
    destruct (le_dec n n0).
    rewrite max_l. rewrite max_l. trivial. auto with arith. trivial.
    rewrite max_r. rewrite max_r. trivial. auto with arith. trivial.
  Qed.

  Lemma A_semi_ringr : semi_ring_theory A0r A1r Aplusr Amultr eqAr.

  Proof.
    constructor; intros.
    compute; trivial.
    apply A_plus_comm.
    apply A_plus_assoc.
    destruct n; compute; trivial.
    compute; trivial.
    apply A_mult_comm.
    apply A_mult_assoc.
    apply A_mult_plus_distr.
  Qed.

  (* Define plus where 0 at the left hand side. *)
  
  Definition A_plus_0_l := SRadd_0_l A_semi_ringr.
  
  (* Proving the property of plus with 0 on the right. *)

  Lemma A_plus_0_r : forall n, Aplusr n A0r = n.
  Proof.
    intros. rewrite A_plus_comm. apply A_plus_0_l.
  Qed.  

  Lemma arctic_plus_notInf_left : forall a b,
    a <> MinusInf -> Aplusr a b <> MinusInf.

  Proof.
    intros. destruct a. 
    destruct b; simpl; discr.
    auto. 
  Qed.

  Lemma arctic_mult_notInf : forall a b,
    a <> MinusInf -> b <> MinusInf -> Amultr a b <> MinusInf.

  Proof.
    intros. 
    destruct a; auto. 
    destruct b; auto. 
    simpl. discr.
  Qed.

End ArticSemiRingT.

(***********************************************************************)
(** ** Arctic semi-ring over integers with minus infinity and 
    plus-max operations. *)

Require Import ZUtil.

Inductive ArcticBZDom : Type := 
| Fin (z : Z)
| MinusInfBZ.

Definition beq_ArcticBZDom x y :=
  match x, y with
    | Fin x', Fin y' => beq_Z x' y'
    | MinusInfBZ, MinusInfBZ => true
    | _, _ => false
  end.

Lemma beq_ArcticBZDom_ok : forall x y, beq_ArcticBZDom x y = true <-> x = y.

Proof.
  unfold beq_ArcticBZDom. destruct x; destruct y; simpl; try (intuition; discr).
  rewrite beq_Z_ok. intuition. subst. refl. inversion H. refl.
Qed.

Section ArticBZ.
  
  Definition Arbz := ArcticBZDom.
  Definition eqArbz := (eq(A:=Arbz)).

  Definition sid_theoryArbz : Setoid_Theory Arbz eqArbz.

  Proof.
    unfold eqArbz. constructor.
    unfold Reflexive. refl.
    unfold Symmetric. sym. hyp.
    unfold Transitive. intros. trans y; hyp.
  Qed.

End ArticBZ.

Section ArticBZ_Eqset_dec.

  Definition eqA_decrbz := dec_beq beq_ArcticBZDom_ok.

End ArticBZ_Eqset_dec.

Section ArticBZSemiRingT.

  Add Setoid Arbz eqArbz sid_theoryArbz as A_Setoidrbz.

  Definition A0rbz := MinusInfBZ.
  Definition A1rbz := Fin 0.

  (** max is a <+> operation in the semi-ring. *)

  Definition Aplusrbz m n :=
    match m, n with
    | MinusInfBZ, n => n
    | m, MinusInfBZ => m
    | Fin m, Fin n => Fin (Zmax m n)
    end.

  Add Morphism Aplusrbz with signature eqArbz ==> eqArbz ==> eqArbz as Aplus_morrbz.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  (** Plus is a <*> operation in the semi-ring. *)

  Definition Amultrbz m n := 
    match m, n with
    | MinusInfBZ, _ => MinusInfBZ
    | _, MinusInfBZ => MinusInfBZ
    | Fin m, Fin n => Fin (m + n)
    end.

  Add Morphism Amultrbz with signature eqArbz ==> eqArbz ==> eqArbz as Amult_morrbz.

  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Lemma A_plus_commrbz : forall m n, Aplusrbz m n = Aplusrbz n m.

  Proof.
    intros. unfold Aplusrbz. destruct m; destruct n; trivial. 
    rewrite Zmax_comm. refl.
  Qed.

  Lemma A_plus_assocrbz : forall m n p,
    Aplusrbz m (Aplusrbz n p) = Aplusrbz (Aplusrbz m n) p.

  Proof.
    intros. unfold Aplusrbz.
    destruct m; destruct n; destruct p; trivial.
    rewrite Zmax_assoc. refl.
  Qed.

  Lemma A_mult_commrbz : forall m n, Amultrbz m n = Amultrbz n m.

  Proof.
    intros. unfold Amultrbz. destruct m; destruct n; trivial.
    rewrite Zplus_comm. refl.
  Qed.

  Lemma A_mult_assocrbz : forall m n p,
    Amultrbz m (Amultrbz n p) = Amultrbz (Amultrbz m n) p.

  Proof.
    intros. unfold Amultrbz.
    destruct m; destruct n; destruct p; trivial.
    rewrite Zplus_assoc. refl.
  Qed.

  Lemma A_mult_plus_distrrbz : forall m n p,
    Amultrbz (Aplusrbz m n) p = Aplusrbz (Amultrbz m p) (Amultrbz n p).

  Proof.
    intros. unfold Amultrbz, Aplusrbz. 
    destruct m; destruct n; destruct p; trivial.
    rewrite Zplus_max_distr_r.
    destruct (Zmax_irreducible_inf z z0); rewrite e; refl.
  Qed.

  Lemma A_semi_ringrbz : semi_ring_theory A0rbz A1rbz Aplusrbz Amultrbz eqArbz.

  Proof.
    constructor; intros.
    compute; trivial.
    apply A_plus_commrbz.
    apply A_plus_assocrbz.
    destruct n; unfold eqArbz; refl.
    unfold eqArbz. trivial.
    apply A_mult_commrbz.
    apply A_mult_assocrbz.
    apply A_mult_plus_distrrbz.
  Qed.

  Lemma arctic_plus_notInf_leftrbz : forall (a b : Arbz),
    a <> MinusInfBZ -> Aplusrbz a b <> MinusInfBZ.

  Proof.
    intros. destruct a. 
    destruct b; simpl; discr.
    auto. 
  Qed.

  Lemma arctic_mult_notInfrbz : forall (a b : Arbz),
    a <> MinusInfBZ -> b <> MinusInfBZ -> Amultrbz a b <> MinusInfBZ.

  Proof.
    intros. 
    destruct a; auto. 
    destruct b; auto.
    simpl. discr.
  Qed.

End ArticBZSemiRingT.

(***********************************************************************)
(** ** Tropical semi-ring over naturals with plus infinity and 
    plus-min operations. *)

Inductive TropicalDom : Type := 
| TPos (n : nat)
| PlusInf.

Definition tropical_is_finite v :=
  match v with
  | PlusInf => false
  | _ => true
  end.

Lemma tropical_is_finite_ok : forall v, tropical_is_finite v = true <-> v <> PlusInf.

Proof.
  intro. destruct v; simpl; intuition. discr.
Qed.

Definition beq_TropicalDom x y :=
  match x, y with
  | TPos x', TPos y' => beq_nat x' y'
  | PlusInf, PlusInf => true
  | _, _ => false
  end.

Lemma beq_TropicalDom_ok : forall x y, beq_TropicalDom x y = true <-> x = y.

Proof.
  unfold beq_TropicalDom. destruct x; destruct y; simpl; try (intuition; discr).
  rewrite beq_nat_ok. intuition. inversion H. refl.
Qed.

Section Tropical.

  Definition At := TropicalDom.
  Definition eqAt := eq(A:=At).
 
  Definition sid_theoryAt : Setoid_Theory At eqAt.

  Proof.
    unfold eqAt. constructor.
    unfold Reflexive. refl.
    unfold Symmetric. sym. hyp.
    unfold Transitive. intros. trans y; hyp.
  Qed.

End Tropical.

Section Tropical_Eqset_dec.

  Definition eqA_dect := dec_beq beq_TropicalDom_ok.

End Tropical_Eqset_dec.

Section TropicalSemiRingT.

  Add Setoid At eqAt sid_theoryAt as A_Setoidt.

  Definition A0t := PlusInf.
  Definition A1t := TPos 0.

  (** min is a <+> operation in the semi-ring. *)

  Definition Aplust m n :=
    match m, n with
    | PlusInf, n => n
    | m, PlusInf => m
    | TPos m, TPos n => TPos (min m n)
    end.

  Add Morphism Aplust with signature eqAt ==> eqAt ==> eqAt as Aplus_mort.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  (** Plus is a <*> operation in the semi-ring. *)

  Definition Amultt m n := 
    match m, n with
    | PlusInf, _ => PlusInf
    | _, PlusInf => PlusInf
    | TPos m, TPos n => TPos (m + n)
    end.

  Add Morphism Amultt with signature eqAt ==> eqAt ==> eqAt as Amult_mort.

  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Lemma A_plus_commt : forall m n, Aplust m n = Aplust n m.

  Proof.
    intros. unfold Aplust. destruct m; destruct n; trivial.
    rewrite min_comm. trivial.
  Qed.

  Lemma A_plus_assoct : forall m n p,
    Aplust m (Aplust n p) = Aplust (Aplust m n) p.

  Proof.
    intros. unfold Aplust.
    destruct m; destruct n; destruct p; trivial.
    rewrite min_assoc. trivial.
  Qed.

  Lemma A_mult_commt : forall m n, Amultt m n = Amultt n m.

  Proof.
    intros. unfold Amultt. destruct m; destruct n; trivial.
    rewrite plus_comm. trivial.
  Qed.

  Lemma A_mult_assoct : forall m n p,
    Amultt m (Amultt n p) = Amultt (Amultt m n) p.

  Proof.
    intros. unfold Amultt.
    destruct m; destruct n; destruct p; trivial.
    rewrite plus_assoc. trivial.
  Qed.

  Import Compare. Import Min.

  Lemma A_mult_plus_distrt : forall m n p,
    Amultt (Aplust m n) p = Aplust (Amultt m p) (Amultt n p).

  Proof.
    intros. unfold Amultt, Aplust.
    destruct m; destruct n; destruct p; trivial.
    destruct (le_dec n0 n).
    rewrite min_l. rewrite min_l. trivial. auto with arith. trivial.
    rewrite min_r. rewrite min_r. trivial. auto with arith. trivial.
  Qed.

  Lemma A_semi_ringt : semi_ring_theory A0t A1t Aplust Amultt eqAt.

  Proof.
    constructor; intros.
    compute; trivial.
    apply A_plus_commt.
    apply A_plus_assoct.
    destruct n; compute; trivial.
    compute; trivial.
    apply A_mult_commt.
    apply A_mult_assoct.
    apply A_mult_plus_distrt.
  Qed.

  (* Define plus 0 on the left. *)

  Definition A_plus_0_lt := SRadd_0_l A_semi_ringt.

  (* Proving the property of plus with 0 on the right. *)

  Lemma A_plus_0_rt : forall n, Aplust n A0t = n.
  
  Proof.
    intros. rewrite A_plus_commt. apply A_plus_0_lt.
  Qed.
  
  Lemma tropical_plus_notInf_leftt : forall a b,
    a <> PlusInf -> Aplust a b <> PlusInf.

  Proof.
    intros. destruct a. 
    destruct b; simpl; discr.
    auto. 
  Qed.

  Lemma tropical_mult_notInft : forall a b,
    a <> PlusInf -> b <> PlusInf -> Amultt a b <> PlusInf.

  Proof.
    intros. 
    destruct a; auto. 
    destruct b; auto. 
    simpl. discr.
  Qed.

End TropicalSemiRingT.

(***********************************************************************)
(** ** Semi-ring of booleans with 'or' and 'and'. *)

Section Bool.

  Definition Ab := bool.
  Definition eqAb := eq (A:=Ab).

  Definition sid_theoryAb : Setoid_Theory Ab eqAb.

  Proof.
    unfold eqAb. constructor.
    unfold Reflexive. refl.
    unfold Symmetric. sym. hyp.
    unfold Transitive. intros. trans y; hyp.
 Qed.

End Bool.

Section Bool_Eqset_dec.

  Definition eqA_decb := bool_dec.

End Bool_Eqset_dec.

Section BSemiRingT.

  Add Setoid Ab eqAb sid_theoryAb as A_Setoidb.

  Definition A0b := false.
  Definition A1b := true.

  Definition Aplusb := orb.

  Add Morphism Aplusb with signature eqAb ==> eqAb ==> eqAb as Aplus_morb.

  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition Amultb := andb.

  Add Morphism Amultb with signature eqAb ==> eqAb ==> eqAb as Amult_morb.

  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Lemma A_semi_ringb : semi_ring_theory A0b A1b Aplusb Amultb eqAb.

  Proof.
    constructor; intros.
    apply orb_false_l.
    apply orb_comm.
    apply orb_assoc.
    apply andb_true_l.
    apply andb_false_l.
    apply andb_comm.
    apply andb_assoc.
    apply andb_orb_distrib_l.
  Qed.

End BSemiRingT.