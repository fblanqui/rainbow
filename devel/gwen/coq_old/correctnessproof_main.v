
(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2011-04-06

* CPF correctness checker main

*)

Set Implicit Arguments.

Require Import ATrs SN ZArith EqUtil String List ListDec ListForall
  ListUtil ZUtil LogicUtil BoolUtil VecUtil NArith NatUtil ADP
  cpf2color cpf rainbow_main_termin AVarCond cpf_util
  correctnessproof_full_termin RelUtil correctnessproof_top_termin
  rainbow_full_termin rainbow_top_termin correctnessproof_non_termin
  rainbow_non_termin.

Section S.

  (** [nat_of_string]: convert a variable map to natural number. *)

  Variable nat_of_string: string -> nat.

  (** [n: nat] is an artificial extra argument which purpose is to
     make the function [dpProof] structually recursive with respect to
     this argument. *)
  
  Variable n : nat.

  (** Assume variable [bb] in [rpo]. *)

  Variable bb : nat.

  Section Termination.
    
    (***********************************************************************)
    (** Check that [R] is a trivial proof by stating the set of rules [R] is
     empty valid termination proof for [red R]. *)
    
    Lemma trsTerminationProof_rIsEmpty_ok :
      forall a (R: arules a), trsTerminationProof_rIsEmpty R = OK -> WF (red R).
  
    Proof.
      intros a R. unfold trsTerminationProof_rIsEmpty.
      destruct R; simpl; intro. apply WF_red_empty. discr.
    Qed.
    
    (***********************************************************************)
    (** ** REMOVE Check that termination proof is valid termination proof for
     [red R]. *)
    (*
    Variables is_notvar_lhs_dp : 
      forall a R,forallb (@is_notvar_lhs (Sig a)) (dp R) = true.
    
    (** No rule right hand side is a variable in [dp R]. *)
    
    Variables is_notvar_rhs_dp :
      forall a R, forallb (@is_notvar_rhs (Sig a)) (dp R) = true. *)
    
    (***********************************************************************)
    (** Correctness proof of string reverse in trsTermination proof. *)
    (* MOVE *)
    Require Import AReverse AUnary.

    Lemma string_reverse_ok :
      forall a t (rs: arules a) trs
             (Hm : trsTerminationProof nat_of_string n bb (reverse_trs rs) t = OK)
             (H : brules_preserve_vars rs = true)
             (H0 : bis_unary (Sig a) (symbol_in_rules trs) = true),
        WF (red rs).

    Proof.
      intros a t rs trs Hm H H0.
    Admitted.

    (***********************************************************************)
    (** Correctness proof of trsTermination proof. *)

    Lemma trsTerminationProof_ok :
      forall a R t i,
        sys_of_input a nat_of_string i = Ok (Red R) ->
        trsTerminationProof nat_of_string n bb R t = OK ->
        WF (red R).
    
    Proof.
      intros a r t i H Hs. revert r H Hs. intros rs Hs.
      clear Hs i. revert t rs. 
      induction t; intros rs Hm; simpl in Hm; try discr.
      
      (** Correctness proof when termination proof is empty. *)

      apply trsTerminationProof_rIsEmpty_ok. hyp.

      (** Correctness proof of termination proof in the case of rule
          removal. *)
      
      destruct o; try discr.
      unfold trsTerminationProof_ruleRemoval in Hm. destruct o0; try discr.
      unfold orderingConstraintProof_redPair in Hm.
      destruct r; try discr.
      revert Hm. case_eq (redPair_interpretation rs t1 l);
                 intros l0 H Hm; try discr.
      eapply redPair_interpretation_ok. apply H. eapply IHt. hyp.

      (** Correctness proof of termination proof in the case of path
          ordering. *)

      revert Hm. case_eq (pathOrder bb rs l o);
      intros l0 H Hm; try discr.

      eapply pathOrdering_ok.
      apply H. eapply IHt. hyp.
      
      (** Correctness proof of dependency pair transformation method
          with and without mark symbol. *)
      
      apply trsTerminationProof_dpTrans_ok with
      (bb:=bb)(nat_of_string:=nat_of_string)(n:=n)(dps:=d)(b:=b)(p:=d0).
      hyp. (*hyp. apply Hm.*)

      (** String reversal *)
     
      case_eq (brules_preserve_vars rs && bis_unary (Sig a) (symbol_in_rules t));
        intros H; rewrite H in Hm; simpl in *; try discr.
      rewrite andb_eq in H. destruct H.
      apply string_reverse_ok with (t:=t0)(trs:=t). 
      hyp. hyp. hyp.
    Qed.

    (***********************************************************************)
    (** ** Check that termination proof is valid termination proof for
     [red_mod R D]. *)

    Require Import QArith_base NewPositivePolynom2 NewPolynom2
            NewMonotonePolynom2 APolyInt_MAQ2 NewAPolyInt2 poly_rat
            cpf2color_interpret ARedPair2 ARelation AWFMInterpretation
            OrdRingType2 PositivePolynom.
    
    (** Relative termination is empty. *)

    Lemma relProof_pIsEmpty_ok :
      forall a (R D: arules a),
        relTerminationProof_rIsEmpty D = OK -> WF (red_mod R D).
    
    Proof.
      intros a R D. unfold relTerminationProof_rIsEmpty.
      destruct D; simpl; intro. apply WF_red_mod_empty. discr.
    Qed.

    (***********************************************************************)
    (** Correctness proof of relative termination. *)

    Lemma rel_TerminationProof_ok :
      forall a R D t i, sys_of_input a nat_of_string i = Ok (Red_mod R D) ->
                        relTerminationProof R D t = OK -> WF (red_mod R D).

    Proof.
      intros a R D t i H Hs. revert R D H Hs. intros R D Hs.
      clear Hs i. revert t R D.
      induction t; intros R D Hm; simpl in Hm; try discr.

      (** Correctness proof when termination proof is empty. *)
      
      apply relProof_pIsEmpty_ok. apply Hm.  
      apply relProof_pIsEmpty_ok. apply Hm.
      
      (** Correctness proof of relative termination proof in the case of
       rule removal. *)

      destruct o; try discr.
      unfold rel_trsTerminationProof_ruleRemoval in Hm. destruct o0; try discr.
      unfold rel_orderingConstraintProof_redPair in Hm.
      destruct r; try discr.
      revert Hm. case_eq (rel_redPair_interpretation R D t2 l);
                 intros l0 H Hm; try discr.
      eapply rel_redPair_interpretation_ok. apply H.
      apply IHt. apply Hm.

      (** Correctness proof of string reverse. *)
      
      case_eq (brules_preserve_vars R && brules_preserve_vars D &&
      bis_unary (Sig a) (symbol_in_rules t)); intros H; rewrite H in Hm; try discr.
      do 2 rewrite andb_eq in H. do 2 destruct H.
      
      apply WF_red_mod_rev_eq.

      (** Proof that [is_unary] is true. *)
      
      rewrite <- bis_unary_ok. apply H0.

      (** Proof that [Fs_ok] *)

      Focus 2.

      (** Proof that rule_preserve_vars in D. *)

      rewrite <- brules_preserve_vars_ok. apply H1.

      Focus 2.
      
      (** Proof that rule_preserve_vars in R. *)
      
      rewrite <- brules_preserve_vars_ok. apply H.
      
      Focus 2.
      
    (* TODO *)
    (* Proof [red_mod (reverse_trs R) (reverse_trs D)] is well-founded *)

    Admitted.

  End Termination.

  (***********************************************************************)
  (** ** Correctness proof of certification problems. *)

  (* [main] for non-termination proof and termination proof where it
   changes [WF(rel_of_sys s)] to [EIS (rel_of_sys s)] to be able to
   proof non-termination problem.*)

  Section main.

    (* REMOVE. *)

    (*Variables is_notvar_lhs_dp : 
      forall a R, forallb (@is_notvar_lhs (Sig a)) (dp R) = true.

    (***********************************************************************)
    (** No rule right hand side is a variable in [dp R]. *)
    
    Variables is_notvar_rhs_dp :
      forall a R, forallb (@is_notvar_rhs (Sig a)) (dp R) = true.*)

    (***********************************************************************)

    Lemma main_ok : forall c, let a := arity_in_pb c in
     forall s, sys_of_pb a nat_of_string c = Ok s ->
               check nat_of_string n bb  a c = OK ->
               not_if (is_nontermin_proof c) (EIS (rel_of_sys s)).
    
    Proof.
      intros c a s Hs Hm. unfold check in Hm. rewrite Hs in Hm.
      destruct c as [[[i st] p] o]. simpl arity_in_pb in *.
      simpl sys_of_pb in *.
      simpl is_nontermin_proof.
      unfold proof in Hm. destruct s; destruct p; try discr; simpl.
      apply WF_notEIS.

      (** Correctness proof of termination problem for [red R]. *)
      
      apply trsTerminationProof_ok with (t:=t)(i:=i).
      hyp. hyp. (*hyp. hyp.*)
      
      (** Correctness proof of non-termination problem for [red R]. *)
      
      unfold trsNonTerminationProof in Hm.
      destruct t; simpl; try discr.
      apply trsNonTerminationProof_variableConditionViolated_ok.
      apply Hm.
      
      (** Correcntness proof of non-termination for [red R] using loop
       method. There is a loop in TRS. *)
      
      apply trsNonTerminationProof_loop_ok with (nat_of_string:=nat_of_string)(l:= l).
      destruct l; try discr.
      destruct p; try discr.
      destruct r; try discr.
      destruct l; try discr.
      apply Hm.
      
      (** Correctness proof of termination problem for [red_mod R D]. *)

      apply WF_notEIS.
      apply rel_TerminationProof_ok with (t:=r)(i:=i).
      hyp. apply Hm.

      (** Correctness proof of non-termination problem for [red_mod R D]. *)
      (*
      unfold relativeNonterminationProof in Hm.
      destruct r; simpl; try discr.

      (** Correctness proof of non-termination proof for [red_mod R D] in
       the case of loop. *)

      apply relativeNonTerminationProof_loop_ok in Hm. apply Hm.

      (** Correctness proof of non-termination proof for [red_mod R D] in
       the case of variable condition violated. *)
      
      apply relativeNonTerminationProof_variableConditionViolated_ok.
      apply Hm.*)
      
      (** Correctness proof of termination for top termination
       problems. [hd_red_mod R (dp R)] *)
      
      apply WF_notEIS. eapply dpProof_ok. apply Hm.
     
      (* TODO : other cases *)
    Qed.

  End main.

End S.