(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski, 2007-04-14

Semi-ring structure.
*)

Require Export Ring Ring_theory.
Require Import RelDec Relations Max Arith Compare LogicUtil Bool RelExtras1
  Setoid EqUtil NatUtil ZUtil RelExtras Morphisms.

(* SemiRingType *)

Class SemiRingType := {
   semi_setoid :> Setoid;
   semi_A0 : s_typ;
   semi_A1 : s_typ;
   semi_Aplus : s_typ -> s_typ -> s_typ;
   semi_Amult : s_typ -> s_typ -> s_typ;
   semi_Aplus_mor : Proper (s_eq ==> s_eq ==> s_eq) semi_Aplus;
   semi_Amult_mor: Proper (s_eq ==> s_eq ==> s_eq) semi_Amult;
   semi_A_semi_ring : semi_ring_theory semi_A0 semi_A1 semi_Aplus semi_Amult
   s_eq
}.

(***********************************************************************)
(** Natural numbers as a semi-ring *)

Instance Nat_as_SemiRingType : SemiRingType.

Proof.
  apply Build_SemiRingType with
  (semi_setoid := Leibniz_Setoid nat)
  (semi_A0 := 0)(semi_A1 := 1)
  (semi_Aplus := plus) (semi_Amult := mult).
  simpl. intros x x' xx' y y' yy'. auto.
  simpl. intros x x' xx' y y' yy'. auto.
  apply natSRth.
Defined.

(***********************************************************************)
(** Integers as a semi-ring *)

Require Import ZArith.

Instance Z_as_SemiRingType : SemiRingType.

Proof.
  apply Build_SemiRingType with
  (semi_setoid := Leibniz_Setoid Z)
  (semi_A0 := 0%Z)(semi_A1 := 1%Z)
  (semi_Aplus := Zplus) (semi_Amult := Zmult).
  simpl. intros x x' xx' y y' yy'. rewrite xx'. rewrite yy'. auto.
  simpl. intros x x' xx' y y' yy'. rewrite xx'. rewrite yy'. auto.
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

(***********************************************************************)
(** Arctic semi-ring over naturals with minus infinity and 
    plus-max operations *)

Require Import SemiRing.

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

Lemma A_plus_assoc : forall m n p, Aplus m (Aplus n p) = Aplus (Aplus m n) p.

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

Lemma A_mult_assoc : forall m n p, Amult m (Amult n p) = Amult (Amult m n) p.

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

Instance Arctic_as_SemiRingType : SemiRingType.

Proof.
   apply Build_SemiRingType with
  (semi_setoid := Leibniz_Setoid ArcticDom)
  (semi_A0 := MinusInf)(semi_A1 := Pos 0)
  (semi_Aplus := Aplus) (semi_Amult := Amult).
   simpl. intros x x' xx' y y' yy'. rewrite xx'. rewrite yy'. auto.
   simpl. intros x x' xx' y y' yy'. rewrite xx'. rewrite yy'. auto.
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
(** Arctic semi-ring over integers with minus infinity and 
    plus-max operations *)

Require Import ZUtil.

(* max is a <+> operation in the semi-ring *)
Definition AplusBZ m n :=
  match m, n with
    | MinusInfBZ, n => n
    | m, MinusInfBZ => m
    | Fin m, Fin n => Fin (Zmax m n)
  end.

(* plus is a <*> operation in the semi-ring *)
Definition AmultBZ m n := 
  match m, n with
    | MinusInfBZ, _ => MinusInfBZ
    | _, MinusInfBZ => MinusInfBZ
    | Fin m, Fin n => Fin (m + n)
  end.

Lemma A_plus_commBZ : forall m n, AplusBZ m n = AplusBZ n m.

Proof.
  intros. unfold AplusBZ. destruct m; destruct n; trivial. 
  rewrite Zmax_comm. refl.
Qed.

Lemma A_plus_assocBZ : forall m n p, AplusBZ m (AplusBZ n p) = AplusBZ (AplusBZ m n) p.

Proof.
  intros. unfold AplusBZ.
  destruct m; destruct n; destruct p; trivial.
  rewrite Zmax_assoc. refl.
Qed.

Lemma A_mult_commBZ : forall m n, AmultBZ m n = AmultBZ n m.

Proof.
  intros. unfold AmultBZ. destruct m; destruct n; trivial.
  rewrite Zplus_comm. refl.
Qed.

Lemma A_mult_assocBZ : forall m n p, AmultBZ m (AmultBZ n p) = AmultBZ (AmultBZ m n) p.

Proof.
  intros. unfold AmultBZ.
  destruct m; destruct n; destruct p; trivial.
  rewrite Zplus_assoc. refl.
Qed.

Lemma A_mult_plus_distrBZ : forall m n p,
                            AmultBZ (AplusBZ m n) p = AplusBZ (AmultBZ m p) (AmultBZ n p).

Proof.
  intros. unfold AmultBZ, AplusBZ. 
  destruct m; destruct n; destruct p; trivial.
  rewrite Zplus_max_distr_r.
  destruct (Zmax_irreducible_inf z z0); rewrite e; refl.
Qed.

Instance ArcticBZ_as_SemiRingType : SemiRingType.

Proof.
  apply Build_SemiRingType with
  (semi_setoid := Leibniz_Setoid ArcticBZDom)
  (semi_A0 := MinusInfBZ)(semi_A1 := Fin 0)
  (semi_Aplus := AplusBZ) (semi_Amult := AmultBZ).
  simpl. intros x x' xx' y y' yy'. rewrite xx'. rewrite yy'. auto.
  simpl. intros x x' xx' y y' yy'. rewrite xx'. rewrite yy'. auto.
  constructor; intros.
  compute; trivial.
  apply A_plus_commBZ.
  apply A_plus_assocBZ.
  destruct n; unfold s_eq; refl.
  unfold s_eq. simpl. trivial.
  apply A_mult_commBZ.
  apply A_mult_assocBZ.
  apply A_mult_plus_distrBZ.
Defined.

(***********************************************************************)
(** Tropical semi-ring over naturals with plus infinity and 
    plus-min operations *)

(* min is a <+> operation in the semi-ring *)
Definition AplusT m n :=
  match m, n with
    | PlusInf, n => n
    | m, PlusInf => m
    | TPos m, TPos n => TPos (min m n)
  end.

(* plus is a <*> operation in the semi-ring *)
Definition AmultT m n := 
  match m, n with
    | PlusInf, _ => PlusInf
    | _, PlusInf => PlusInf
    | TPos m, TPos n => TPos (m + n)
  end.

Lemma A_plus_commT : forall m n, AplusT m n = AplusT n m.

Proof.
  intros. unfold AplusT. destruct m; destruct n; trivial.
  rewrite min_comm. trivial.
Qed.

Lemma A_plus_assocT : forall m n p, AplusT m (AplusT n p) = AplusT (AplusT m n) p.

Proof.
  intros. unfold AplusT.
  destruct m; destruct n; destruct p; trivial.
  rewrite min_assoc. trivial.
Qed.

Lemma A_mult_commT : forall m n, AmultT m n = AmultT n m.

Proof.
  intros. unfold AmultT. destruct m; destruct n; trivial.
  rewrite plus_comm. trivial.
Qed.

Lemma A_mult_assocT : forall m n p, AmultT m (AmultT n p) = AmultT (AmultT m n) p.

Proof.
  intros. unfold AmultT.
  destruct m; destruct n; destruct p; trivial.
  rewrite plus_assoc. trivial.
Qed.

Import Compare. Import Min.

Lemma A_mult_plus_distrT : forall m n p,
                            AmultT (AplusT m n) p = AplusT (AmultT m p) (AmultT n p).

Proof.
  intros. unfold AmultT, AplusT.
  destruct m; destruct n; destruct p; trivial.
  destruct (le_dec n0 n).
  rewrite min_l. rewrite min_l. trivial. auto with arith. trivial.
  rewrite min_r. rewrite min_r. trivial. auto with arith. trivial.
Qed.

Instance Tropical_as_SemiRingType : SemiRingType.

Proof.
 apply Build_SemiRingType with
  (semi_setoid := Leibniz_Setoid TropicalDom)
  (semi_A0 := PlusInf)(semi_A1 := TPos 0)
  (semi_Aplus := AplusT) (semi_Amult := AmultT).
  simpl. intros x x' xx' y y' yy'. rewrite xx'. rewrite yy'. auto.
  simpl. intros x x' xx' y y' yy'. rewrite xx'. rewrite yy'. auto.
  constructor; intros.
  compute; trivial.
  apply A_plus_commT.
  apply A_plus_assocT.
  destruct n; compute; trivial.
  compute; trivial.
  apply A_mult_commT.
  apply A_mult_assocT.
  apply A_mult_plus_distrT.
Defined.

(***********************************************************************)
(** Semi-ring of booleans with 'or' and 'and' *)

Definition AplusB := orb.
Definition AmultB := andb.

Instance Bool_as_SemiRingType : SemiRingType.

Proof.
  apply Build_SemiRingType with
  (semi_setoid := Leibniz_Setoid bool)
    (semi_A0 := false)(semi_A1 := true)
    (semi_Aplus := AplusB) (semi_Amult := AmultB).
  simpl. intros x x' xx' y y' yy'. rewrite xx'. rewrite yy'. auto.
  simpl. intros x x' xx' y y' yy'. rewrite xx'. rewrite yy'. auto.
  constructor; intros.
  apply orb_false_l.
  apply orb_comm.
  apply orb_assoc.
  apply andb_true_l.
  apply andb_false_l.
  apply andb_comm.
  apply andb_assoc.
  apply andb_orb_distrib_l.
Defined.