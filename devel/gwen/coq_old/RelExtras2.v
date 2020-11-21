(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2004-09-06
- William Delobel, 2005-10-07

* This file provides some basic results concerning relations that were
missing in the standard library.

*)

Set Implicit Arguments.

Require Import RelUtil LogicUtil Max Arith Setoid.
Require Export Relations.

(** Strict order. *)

Section StrictOrder.

  Variable A : Type.
  Variable R : relation A.

  Record strict_order : Prop := {
    sord_trans : transitive R;
    sord_irrefl : irreflexive R 
  }.

  Variable so : strict_order.

  Lemma so_not_symmetric : forall a b, R a b -> R b a -> False.

  Proof.
    unfold not; intros a b Rab Rba.
    exact (sord_irrefl so (sord_trans so Rab Rba)).
  Qed.

  Variable eq : relation A.
  Variable Req_compat : forall x x' y y',
    eq x x' -> eq y y' -> R x y -> R x' y'.
  Variable eq_setoid : Setoid_Theory A eq.

  Lemma so_strict : forall x y, eq x y -> R x y -> False.

  Proof.
    intros.
    assert (R y x).
    apply Req_compat with x y; auto.
    apply (Seq_sym A eq eq_setoid); trivial.
    absurd (R x x).
    unfold not; intro xx; exact (sord_irrefl so xx).
    exact (sord_trans so H0 H1).
  Qed.

End StrictOrder.

(** Record types for setoids with decidable equality. *)

Section SetA.

  Record SetA : Type := mkSetA {
    A' : Type}.

End SetA.

(* Record signature Eqset. *)

Section Eqset.
  
  Parameter A : Type.

  Record Eqset : Type := mkEqset {
    eqA : A -> A -> Prop
  }.
  
  Variable e: Eqset.
  
  Parameter sid_theoryA : Setoid_Theory A (eqA e).

  Hint Resolve (Seq_refl  A (eqA e) sid_theoryA) : sets.
  Hint Resolve (Seq_trans A (eqA e) sid_theoryA) : sets.
  Hint Resolve (Seq_sym   A (eqA e) sid_theoryA) : sets.

End Eqset.

(** Record signature [Eqset_dec]. *)

Section Eqset_dec.

  Variable e: Eqset.

  Notation eqA := (eqA e).
  Notation "X =A= Y" := (eqA X Y) (at level 70).

  Parameter eqA_dec : forall x y, {x =A= y} + {~x =A= y}.

End Eqset_dec.

(** Functor Eqset_def. *)

Section Eqset_def.

  Variable e : Eqset.
  
  Definition eqA' := eq(A:=A).

  Definition sid_theoryA' := Build_Setoid_Theory _ eqA'
    (refl_equal(A:=A) ) (sym_eq (A:=A)) (trans_eq(A:=A)).

  Hint Resolve (Seq_refl A eqA' sid_theoryA') : sets.
  Hint Resolve (Seq_trans A eqA' sid_theoryA') : sets.
  Hint Resolve (Seq_sym A eqA' sid_theoryA') : sets.   

End Eqset_def.

(** Record types for ordered setoids. *)

Section Eqset_def_gtA_eqA_compat.

  Variable A : Type.
  
  Variable gtA : A -> A -> Prop.

  Lemma Eqset_def_gtA_eqA_compat :
    forall x x' y y', x = x' -> y = y' -> gtA x y -> gtA x' y'.

  Proof.
    intros x x' y y' x_x' y_y' x_y.
    rewrite <- x_x'; rewrite <- y_y'; trivial.
  Qed.

End Eqset_def_gtA_eqA_compat.

(** Record signature [Ord]. *)

Section Ord.

  Variable e: Eqset.
  Notation "X =A= Y" := ((eqA e) X Y)(at level 70).

  Record Ord : Type := mkOrd {
    gtA : A -> A -> Prop;
    gtA_eqA_compat : forall x x' y y',
      x =A= x' -> y =A= y' -> gtA x y -> gtA x' y'
    }.

  Notation "X >A Y" := (gtA X Y) (at level 70).

  Hint Resolve gtA_eqA_compat : sets.

End Ord.

(** Functor OrdLemmas (P: Ord). *)

Section OrdLemmas.

  Variable e: Eqset.
  Variable P: Ord e.

  Definition ltA := transp (gtA P).
  Definition geA x y := ~ ltA x y.
  Definition leA x y := ~ (gtA P) x y.
  Definition AccA := Acc ltA.

  Notation "X =A= Y" := (eqA X Y)(at level 70).
  Notation "X <A Y" := (ltA X Y) (at level 70).
  Notation "X >=A Y" := (geA X Y) (at level 70).
  Notation "X <=A Y" := (leA X Y) (at level 70).

  Hint Unfold ltA geA leA AccA : sets.

  Add Setoid A (eqA e) (sid_theoryA e) as sidA.

  Add Morphism (gtA P)
    with signature (eqA e)  ==> (eqA e) ==> iff
      as gtA_morph.
  Proof.
   destruct P; simpl in *.
    split;
    eauto with sets. apply gtA_eqA_compat0. 
    sym. hyp.
    apply (Seq_sym _ _ (sid_theoryA e)). hyp.
  Qed.

  Add Morphism ltA
    with signature (eqA e) ==> (eqA e) ==> iff
      as ltA_morph.

  Proof.
    destruct P; simpl in *.
    split; eauto with sets.
    unfold ltA. unfold transp.
    destruct P; simpl in *. eauto with sets.
    unfold ltA. unfold transp.
    destruct P; simpl in *. eauto with sets.
    apply gtA_eqA_compat1. sym. hyp.
    sym. hyp.
  Qed.

  Add Morphism AccA
    with signature (eqA e) ==> iff
      as AccA_morph.

  Proof.
    destruct P. simpl in *.
    intros a b eq_ab. split.
    intro acc_a. inversion acc_a. constructor. intros.
    apply H. rewrite eq_ab. hyp.
    intros acc_b. inversion acc_b. constructor. intros.
    apply H. rewrite <- eq_ab. hyp.
  Qed.

End OrdLemmas.

(** Record signature Poset. *)

Section Poset.

  Variable e: Eqset.
  Variable O : Ord e.

  Parameter gtA_so : strict_order (gtA O).

  Hint Resolve (sord_trans gtA_so) : sets.
  Hint Resolve (sord_irrefl gtA_so) : sets.
  Hint Resolve (so_not_symmetric gtA_so) : sets.
  Hint Resolve (so_strict gtA_so (gtA_eqA_compat O) (sid_theoryA e)) : sets.

End Poset.

(** Functor nat_ord. *)

Section nat_ord.
   
  Section natSet.
    Definition AN := nat.
    Definition eq_decN := eq_nat_dec.
  End natSet.

  Lemma gtA_eqA_compatnat : forall x x' y y', 
    x = x' -> y = y' -> x > y -> x' > y'.

  Proof.
    intros x x' y y' xx' yy'.
    rewrite <- xx'; rewrite <- yy'; trivial.
  Qed.

End nat_ord.

(** Lemmas on transitive closure. *)

Section Transitive_Closure.

  Variable A : Type.
  Variable R : A -> A -> Prop.

  Lemma trans_clos_step_l : forall x y, 
    R! x y -> R x y \/ (exists2 z, R x z & R! z y).

  Proof.
    intros x y; compute; intro xy; induction xy.
    left; trivial.
    inversion IHxy1; inversion IHxy2; right; solve [eauto |
      inversion H; try inversion H0; exists x0; 
      [trivial | constructor 2 with y; auto]].
  Qed.

  Lemma trans_clos_step_r : forall x y, 
    R! x y -> R x y \/ (exists2 z, R! x z & R z y).

  Proof.
    intros x y; compute; intro xy; induction xy.
    left; trivial.
    inversion_clear IHxy1; inversion_clear IHxy2; right;
      solve [eauto | inversion H0; exists x0; 
      [constructor 2 with y; auto | trivial]].
  Qed.

  Variable eqA : A -> A -> Prop.

  Parameter sid_theoryAc : Setoid_Theory A eqA.
  Parameter R_eqA_comp : forall x y x' y',
    eqA x x' -> eqA y y' -> R x y -> R x' y'.
  Parameter R_so : strict_order R.

  Hint Resolve R_eqA_comp.

  Lemma trans_clos_mirror : forall x y x' y',
    eqA x x' -> eqA y y' -> R! x y -> R! x' y'.

  Proof.
    intros x y x' y' eq_xx' eq_yy' R_xy. 
    case (trans_clos_step_l R_xy).
    intro Rxy; constructor 1; eauto.
    intro R_xzy; destruct R_xzy as [w Rxw R_wy].
    case (trans_clos_step_r R_wy).
    intro Rwy; constructor 1; apply R_eqA_comp with x y;
      solve [trivial | apply (sord_trans R_so) with w; trivial].
    intro R_wpy; destruct R_wpy as [p Rwp R_py].
    constructor 2 with w.
    constructor 1; apply R_eqA_comp with x w; 
      solve [trivial | apply (Seq_refl A eqA sid_theoryAc)].
    constructor 2 with p.
    trivial.
    constructor 1; apply R_eqA_comp with p y;
      solve [trivial | apply (Seq_refl A eqA sid_theoryAc)].
  Qed.

  Lemma trans_clos_transp : forall x y, transp (R!) x y <-> (transp R)! x y.

  Proof.
    intros; split; compute.
    induction 1.
    constructor; trivial.
    constructor 2 with y; auto.
    induction 1.
    constructor; trivial.
    constructor 2 with y; auto.
  Qed.

End Transitive_Closure.

(** Specification *)

Section Specif.

  Inductive sigPS2 (A : Type) (P: A -> Prop) (Q: A -> Set) : Type :=
    existPS2: forall x:A, P x -> Q x -> sigPS2 (A:=A) P Q.

  Notation "{ x : A # P & Q }"
    := (sigPS2 (fun x:A => P) (fun x:A => Q)) : type_scope.

  Variable A : Type.
  Variables P Q : A -> Prop.

  Definition proj1_sig2 (e: sig2 P Q) :=
    match e with
    | exist2 a p q => a
    end.

End Specif.

(** Lemmas on the option type. *)

Section option.

  Variable A : Type.

  Lemma option_dec : forall (el: option A),
    el = None \/ exists w: A, el = Some w.
    
  Proof.
    intros.
    destruct el.
    right; exists a; trivial.
    left; trivial.
  Qed.

End option.

(** Tactics *)

Ltac pair_destruct t0 t1 :=
  first [destruct t0 | intros until t0; destruct t0];
  first [destruct t1 | intros until t1; destruct t1];
  try contr; simpl.

Ltac rewrite_lr term := apply (proj1 term).
Ltac rewrite_rl term := apply (proj2 term).

Ltac try_solve := 
   simpl in *; try (intros; solve 
     [ contr 
     | discr 
     | auto with terms
     | tauto
     | congruence
     ]
).
