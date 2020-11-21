
(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2011-04-06

* CPF correctness checker main

*)

Set Implicit Arguments.

Require Import ATrs SN ZArith EqUtil String List ListDec ListForall
  ListUtil ZUtil LogicUtil BoolUtil VecUtil NArith NatUtil ADP
  cpf2color cpf AVarCond cpf_util RelUtil rainbow_non_termin ALoop
  AModLoop.

Section Non_Termination.

  (** [nat_of_string]: convert a variable map to natural number. *)

  Variable nat_of_string: string -> nat.

  (***********************************************************************)
  (** ** Check that non-termination proof is valid termination proof for
   [red R]. *)

  Lemma trsNonTerminationProof_variableConditionViolated_ok:
    forall a (R: arules a),
      trsNonTerminationProof_variableConditionViolated R = OK -> EIS (red R).
  
  Proof.
    intros a R H.
    unfold trsNonTerminationProof_variableConditionViolated in H.
    case_eq (brules_preserve_vars R); intros H1; rewrite H1 in H; try discr.
    apply var_cond.
    rewrite <- brules_preserve_vars_ok.
    rewrite <- false_not_true.
    apply H1.
  Qed.
  
  (***********************************************************************)
  (** ** Check that [p] is a valid non-termination proof for [red
     R]. Checking that there is a loop in a TRS. *)

  Lemma trsNonTerminationProof_loop_ok:
    forall a (R: arules a) l,
      trsNonTerminationProof_loop nat_of_string R l = OK -> EIS (red R).

  Proof.
    intros a R l Hm.
    unfold trsNonTerminationProof_loop in Hm.
    destruct l; simpl; try discr.
    destruct p; simpl; try discr.
    destruct r; simpl; try discr.
    case_eq (color_term a nat_of_string t);
      intros t1 H; rewrite H in Hm; try discr.
    case_eq (color_rewriteSequence nat_of_string a l);
      intros ds H0; rewrite H0 in Hm; try discr.
    case_eq (is_loop R t1 ds (color_position_of_context c));
      intros H1; rewrite H1 in Hm; try discr.
    set (ps:= color_position_of_context c).
    apply is_loop_correct with (t:=t1)(ds:=ds)(p:=ps).    
    apply H1.   
  Qed.
  
  (***********************************************************************)
  (** ** Check that non-termination proof is valid termination proof for
     [red_mod R D]. *)
  (* TODO *)
  
  (*Lemma relativeNonTerminationProof_variableConditionViolated_ok:
    forall a (R D: arules a),
      relativeNonTerminationProof_variableConditionViolated R D = OK
      -> EIS (red_mod R D).

  Proof.
    intros a R D Hm.
    unfold relativeNonTerminationProof_variableConditionViolated in Hm.
    case_eq (brules_preserve_vars D); intros H; rewrite H in Hm; try discr.
    apply var_cond_mod.
    rewrite <- brules_preserve_vars_ok.
    rewrite <- false_not_true.
    apply H.
  Qed.*)
  
  (***********************************************************************)
  (** ** Check that [p] is a valid non-termination proof for [red_mod
     R D]. Checking that there is a loop in a TRS. *)

  (*Lemma relativeNonTerminationProof_loop_ok:
    forall a (R D : arules a) l,
      relativeNonTerminationProof_loop nat_of_string R D l = OK -> EIS (red_mod R D).

  Proof.
    intros a R D l Hm.
    unfold relativeNonTerminationProof_loop in Hm.
    destruct l; simpl; try discr.
    destruct p; simpl; try discr.
    destruct r; simpl; try discr.
    case_eq (color_term a nat_of_string t);
      intros t1 H1; rewrite H1 in Hm; try discr.
    case_eq (color_rewriteSequence nat_of_string a l);
      intros ds H2; rewrite H2 in Hm; try discr.
    case_eq (color_list_mod_data nat_of_string a (l :: Datatypes.nil));
      intros mds H3; rewrite H3 in Hm; try discr.
    case_eq (is_mod_loop R D t1 mds ds (color_position_of_context c));
      intros H4; rewrite H4 in Hm; try discr.
    set (p := color_position_of_context c).
    apply is_mod_loop_correct with (t:=t1)(mds:=mds)(ds:=ds)(p:=p).
    apply H4.
    case_eq (color_list_mod_data nat_of_string a (l::Datatypes.nil));
      intros l0 H3; rewrite H3 in Hm; try discr.
  Qed.
*)
End Non_Termination.