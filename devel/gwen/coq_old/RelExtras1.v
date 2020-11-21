(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frédéric Blanqui, 2014-02-18

This file provides a translation into classes of the module types and
functors defined in RelExtras. *)

Set Implicit Arguments.

Require Import LogicUtil EqUtil Relations Setoid Structures.Equalities
  Morphisms Basics.
Require Export RelExtras.

(** Setoids. *)
(* Remark: this is a module type Eqset. *)

Class Setoid := {
  s_typ :> Type;
  s_eq : relation s_typ;
  s_eq_Equiv : Equivalence s_eq }.

(* Remake: this is a module type of Eqset_dec. The declare module export Eq is
: Setoit type.*)

Instance Leibniz_Setoid (A : Type) : Setoid.

Proof.
  apply Build_Setoid with (s_eq := @eq A). constructor. fo. fo.
  unfold Transitive. apply eq_trans.
Defined.

(** Setoids with decidable equivalence. *)
(* Remark: This is a module type Eqset_def <: Eqset is translated to
the first field Setoid. *)

Class Decidable_Setoid := {
  ds_setoid :> Setoid;
  ds_eq_dec : forall x y, {s_eq x y} + {~s_eq x y} }.

(** Ordered setoids. *)

(* Remark: all the add Setoid can be replace by Proper. This is a
module type Ord. *)

Class Ordered_Setoid := {
  os_setoid :> Setoid;
  os_gt : relation s_typ;
  os_gt_compat : Proper (s_eq ==> s_eq ==> impl) os_gt }.

(* Remark: this is a funtor nat_ord taking Ord as type. *)

Instance Nat_as_Ordered_Setoid : Ordered_Setoid.

Proof.
  apply Build_Ordered_Setoid with (os_setoid := Leibniz_Setoid nat)
                                  (os_gt := gt).
  simpl. intros x x' xx' y y' yy' xy. omega.
Defined.
