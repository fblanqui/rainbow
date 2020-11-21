(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-02-22, 2009-10-20 (rpo)

convert CoLoR terms into Coccinelle terms

- Ly Kim Quyen, 2013-09-16

Re-define module type into Section.

*)

Set Implicit Arguments.

Require Import LogicUtil ATerm VecUtil.

(***********************************************************************)
(** convert CoLoR terms into Coccinelle terms *)

Require Import List Relations SN ASubstitution.

Section Make_Term.

  Variable Sig: Signature.

  Notation aterm := (term Sig). Notation aterms := (vector aterm).
  Notation AVar := ATerm.Var.

  Require Import cocc_term2.

  Fixpoint term_of_aterm (t:aterm) :=
    match t with
      | AVar x => Var Sig x
      | Fun f ts =>
        let fix terms_of_aterms n (ts : aterms n) :=
          match ts with
            | Vnil => nil
            | Vcons u k us => term_of_aterm u :: terms_of_aterms k us
          end in Term f (terms_of_aterms (arity f) ts)
    end.

  Fixpoint terms_of_aterms n (ts : aterms n) :=
    match ts with
      | Vnil => nil
      | Vcons u k us => term_of_aterm u :: terms_of_aterms us
    end.

    Lemma terms_of_aterms_eq : forall n (ts : aterms n),
    (fix terms_of_aterms n (ts : aterms n) :=
      match ts with
        | Vnil => nil
        | Vcons u k us => term_of_aterm u :: terms_of_aterms k us
      end) n ts = terms_of_aterms ts.

  Proof.
    induction ts; simpl; intros. refl. rewrite IHts. refl.
  Qed.

  Lemma term_of_aterm_fun : forall f ts,
    term_of_aterm (Fun f ts) = Term f (terms_of_aterms ts).

  Proof.
    intros. simpl. rewrite terms_of_aterms_eq. refl.
  Qed.

  Require Import VecUtil.

  Lemma terms_of_aterms_cast : forall n (ts : aterms n) p (e : n=p),
    terms_of_aterms (Vcast ts e) = terms_of_aterms ts.

  Proof.
    induction ts; destruct p; simpl; intros; try discr. refl.
    inversion e. subst p. rewrite IHts. refl.
  Qed.

  Lemma terms_of_aterms_app : forall n (ts : aterms n) p (us : aterms p),
    terms_of_aterms (Vapp ts us) = terms_of_aterms ts ++ terms_of_aterms us.

  Proof.
    induction ts; simpl; intros. refl. rewrite IHts. refl.
  Qed.

  Lemma length_terms_of_aterms : forall n (ts : aterms n),
    length (terms_of_aterms ts) = n.

  Proof.
    induction ts; simpl; intros. refl. rewrite IHts. refl.
  Qed.

  Require Import Datatypes.

  Fixpoint sub_of_asub (s : ASubstitution.substitution Sig) n :=
    match n with
      | 0 => nil
      | S n' => (n', term_of_aterm (s n')) :: sub_of_asub s n'
    end.

  (********************************************************************************)

  Require Import more_list NatUtil EqUtil.
  
  Notation find := (@find _ var_eq_bool _).

  Lemma find_sub_of_asub : forall s n v, find v (sub_of_asub s n) =
    if bgt_nat n v then Some (term_of_aterm (s v)) else None.

  Proof.
    induction n; intros. refl. simpl sub_of_asub. simpl more_list.find.
    rewrite IHn. unfold var_eq_bool. case_beq_nat v n.
    assert (bgt_nat (S v) v = true). rewrite bgt_nat_ok. omega. rewrite H.
    refl.
    case_eq (bgt_nat n v); intros; case_eq (bgt_nat (S n) v); intros.
    refl. rewrite bgt_nat_ok in H0. rewrite bgt_nat_ko in H1. absurd_arith.
    rewrite bgt_nat_ok in H1. rewrite bgt_nat_ko in H0.
    rewrite (beq_ko NatUtil.beq_nat_ok) in H. absurd_arith. refl.
  Qed.
 
  Notation apply_subst := (@apply_subst Sig).

  Lemma term_of_aterm_sub : forall s k t, k > maxvar t ->
    term_of_aterm (sub s t) = apply_subst (sub_of_asub s k) (term_of_aterm t).

  Proof.
    intros s k t; pattern t; apply ATerm.term_ind
      with (Q := fun n (ts : aterms n) =>
        k > maxvars ts -> terms_of_aterms (Vmap (sub s) ts) =
        map (apply_subst (sub_of_asub s k)) (terms_of_aterms ts)); clear t.
    simpl in *. intros.
    rewrite find_sub_of_asub. case_eq (bgt_nat k x); intros.
    refl. rewrite bgt_nat_ko in H0. absurd_arith.
    intros. simpl sub. rewrite !term_of_aterm_fun. simpl.
    apply (f_equal (Term f)). apply H. hyp.
    refl. intros t n ts. simpl. rewrite maxvars_cons. rewrite gt_max.
    intros. destruct H1. rewrite H. 2: hyp. rewrite H0. 2: hyp. refl.
  Qed.

  Require Import APosition.
  Require Import AContext.

  Lemma term_of_aterm_fill : forall u t c, term_of_aterm (fill c t) =
    replace_at_pos (term_of_aterm (fill c u)) (term_of_aterm t) (pos_context c).

  Proof.
    induction c; intros. refl. simpl fill. simpl pos_context.
    rewrite !term_of_aterm_fun, replace_at_pos_unfold.
    apply (f_equal (Term f)).
    rewrite !terms_of_aterms_cast, !terms_of_aterms_app. simpl.
    rewrite replace_at_pos_list_replace_at_pos_in_subterm, <- IHc. refl.
    rewrite length_terms_of_aterms. refl.
  Qed.

  Lemma is_a_pos_context : forall u c,
    is_a_pos (term_of_aterm (fill c u)) (pos_context c) = true.

  Proof.
    induction c; intros. refl. simpl fill. rewrite term_of_aterm_fun. simpl.
    rewrite terms_of_aterms_cast. rewrite terms_of_aterms_app. simpl.
    assert (nth_error (terms_of_aterms t ++ term_of_aterm (fill c u) ::
      terms_of_aterms t0) i = nth_error (terms_of_aterms t ++ term_of_aterm
        (fill c u) :: terms_of_aterms t0) (length (terms_of_aterms t))).
    apply (f_equal (nth_error (terms_of_aterms t ++ term_of_aterm (fill c u)
      :: terms_of_aterms t0))). rewrite length_terms_of_aterms. refl.
    rewrite H. rewrite nth_error_at_pos. hyp.
  Qed.

End Make_Term.

(***********************************************************************)
(** module type for using Coccinelle's RPO *)

Require Import rpo_extension2.

Section S.

  Variable Sig: Signature.

  Section PRECEDENCE.

  Record PRECEDENCE := mkPrecedence {
    status : Sig -> status_type;
    prec_nat : Sig -> nat;
    bb: nat;
    prec_eq_status :
      forall f g, prec_eq' Sig prec_nat f g -> status f = status g
  }.

End PRECEDENCE.

(***********************************************************************)
(** convert Coccinelle RPO into a CoLoR WeakRedPair *)

Require Import ARedPair1 ARelation RelUtil BoolUtil.

Section WP_PRO.

  (* Assume bb is a variable in rpo. *)

  Variable bb: nat.
  
  (* Define [pre] is each field of PRECEDENCE. *)

  Variable P : PRECEDENCE.
  
  Definition status' := (@status P).
  Definition prec_nat' := (@prec_nat P).
  Definition prec_eq_status' := (@prec_eq_status P).

  Notation A := (A_symb Sig).

  Require Import rpo2.

  Notation rpo := (@rpo Sig status' prec_nat' prec_eq_status' bb).

  Definition succ_rpo := transp (Rof rpo (term_of_aterm (Sig:=Sig))).

  Require Import Inverse_Image.

  Lemma wf_succ_rpo : WF succ_rpo.

  Proof.
    apply wf_WF_transp. apply wf_inverse_image with (f:=@term_of_aterm Sig).
    apply wf_rpo. apply prec_wf'.
  Qed.

  Require Import Max Datatypes.

  Lemma sc_succ_rpo : substitution_closed succ_rpo.

  Proof.
    intros t u s h. unfold succ_rpo, transp, Rof. set (k:=max(maxvar t)(maxvar u)).
    rewrite term_of_aterm_sub with (k:=S k). 2: apply le_n_S; apply le_max_r.
    rewrite term_of_aterm_sub with (k:=S k). 2: apply le_n_S; apply le_max_l.
    apply rpo_subst. hyp. 
   Qed.

   Notation empty_rpo_infos := (empty_rpo_infos Sig status' prec_nat' prec_eq_status' bb).
   Notation rpo_eval := (@rpo_eval Sig status' prec_nat' prec_eq_status' empty_rpo_infos bb).
   Notation rpo_eval_is_sound := (rpo_eval_is_sound_weak empty_rpo_infos bb).

  Require Import ordered_set.

  Definition bsucc_rpo t u :=
    match rpo_eval ((term_of_aterm (Sig:=Sig))t) ((term_of_aterm (Sig:=Sig))u) with
      | Some Greater_than => true
      | _ => false
    end.

  Lemma bsucc_rpo_ok : forall t u, bsucc_rpo t u = true -> succ_rpo t u.

  Proof.
    intros t u. unfold bsucc_rpo.
    gen (rpo_eval_is_sound (term_of_aterm t) (term_of_aterm u)).
    case (rpo2.rpo_eval empty_rpo_infos bb (term_of_aterm t) (term_of_aterm u)); try discr.
    destruct c; try discr. unfold succ_rpo, transp, Rof. auto.
  Qed.

  Lemma bsucc_rpo_sub : rel_of_bool bsucc_rpo << succ_rpo.

  Proof.
    intros t u. unfold rel_of_bool. intro h. apply bsucc_rpo_ok. hyp.
  Qed.

  Definition equiv_aterm := Rof (@equiv Sig status' prec_nat' prec_eq_status')
                                (@term_of_aterm Sig).

  Definition succeq_rpo := succ_rpo U equiv_aterm.

  Lemma sc_succeq_rpo : substitution_closed succeq_rpo.

  Proof.
    intros t u s [h|h]. left. apply sc_succ_rpo. hyp. right.
    unfold equiv_aterm, Rof. set (k := max (maxvar t) (maxvar u)).
    rewrite term_of_aterm_sub with (k:=S k). 2: apply le_n_S; apply le_max_l.
    rewrite term_of_aterm_sub with (k:=S k). 2: apply le_n_S; apply le_max_r.
    apply equiv_subst. hyp.
  Qed.

  Notation AVar := ATerm.Var.

  Lemma cc_succ_rpo : context_closed succ_rpo.

  Proof.
    intros t u c h. unfold succ_rpo, transp, Rof.
    rewrite term_of_aterm_fill with (u := AVar 0) (t:=t).
    rewrite term_of_aterm_fill with (u := AVar 0) (t:=u).
    eapply rpo_add_context. hyp. apply is_a_pos_context.
  Qed.

  Lemma cc_equiv_aterm : context_closed equiv_aterm.

  Proof.
    intros t u c h. unfold equiv_aterm, Rof.
    rewrite term_of_aterm_fill with (u := AVar 0) (t:=t).
    rewrite term_of_aterm_fill with (u := AVar 0) (t:=u).
    apply equiv_add_context. hyp. apply is_a_pos_context.
  Qed.

  Lemma cc_succeq_rpo : context_closed succeq_rpo.

  Proof.
    intros t u c [h|h]. left. apply cc_succ_rpo. hyp.
    right. apply cc_equiv_aterm. hyp.
  Qed.

  Lemma refl_succeq_rpo : reflexive succeq_rpo.

  Proof.
    intro t. right.
    apply rpo2.Eq.
  Qed.

  Lemma succ_succeq_rpo_compat : absorbs_left succ_rpo succeq_rpo.

  Proof.
    intros t v [u [[h1|h1] h2]]. apply rpo_trans with (term_of_aterm u); hyp.
    unfold succ_rpo, transp, Rof. rewrite equiv_rpo_equiv_1. apply h2.
    hyp.
  Qed.

  Definition bsucceq_rpo t u :=
    match rpo_eval (@term_of_aterm Sig t) (@term_of_aterm Sig u) with
      | Some Greater_than | Some Equivalent => true
      | _ => false
    end.

  Lemma bsucceq_rpo_ok : forall t u, bsucceq_rpo t u = true -> succeq_rpo t u.

  Proof.
    intros t u. unfold bsucceq_rpo.
    gen (rpo_eval_is_sound (term_of_aterm t) (term_of_aterm u)).
    case (rpo_eval (term_of_aterm t) (term_of_aterm u)); try discr.
    destruct c; try discr; unfold succeq_rpo, Relation_Operators.union,
      equiv_aterm, succ_rpo, transp, Rof; auto.
  Qed.

  Definition bsucceq_rpo_sub : rel_of_bool bsucceq_rpo << succeq_rpo.

  Proof.
    intros t u. unfold rel_of_bool. intro h. apply bsucceq_rpo_ok. hyp.
  Qed.

  Lemma trans_succ_rpo : transitive succ_rpo.

  Proof.
    unfold succ_rpo. apply transp_trans. apply Rof_trans.
    intros t u v htu huv. apply rpo_trans with u; hyp.
  Qed.

  Lemma trans_equiv_aterm : transitive equiv_aterm.

  Proof.
    unfold equiv_aterm. apply Rof_trans.
    apply (equiv_trans _ _ (equiv_equiv Sig status' prec_nat' prec_eq_status')).
  Qed.

  Lemma trans_succeq_rpo : transitive succeq_rpo.

  Proof.
    unfold succeq_rpo, Relation_Operators.union, transitive.
    intuition.
    left. apply trans_succ_rpo with y; hyp.
    left. revert H. unfold equiv_aterm, succ_rpo, transp, Rof. intro.
    rewrite <- equiv_rpo_equiv_2. apply H1. hyp.
    left. revert H1. unfold equiv_aterm, succ_rpo, transp, Rof. intro.
    rewrite equiv_rpo_equiv_1. apply H. hyp.
    right. apply trans_equiv_aterm with y; hyp.
  Qed.

  (** Record type bWeaRedPair. *)

  (* Use the definition of mkbWeakRedPair2. *)
  
  
End WP_PRO.  

End S.

(*
(***********************************************************************)
(** decide compatibility of statuses wrt precedences *)

Definition beq_status (s1 s2 : status_type) : bool :=
  match s1, s2 with
    | Lex, Lex
    | Mul, Mul => true
    | _, _ => false
  end.

Lemma beq_status_ok : forall s1 s2, beq_status s1 s2 = true <-> s1 = s2.

Proof.
beq_symb_ok.
Qed.

(* FIXME: use rpo_extension2 *)

Require Import rpo_extension.

Section prec_eq_status.

  Variables (Sig : Signature) (status : Sig -> status_type)
    (prec_nat : Sig -> nat).

  Lemma prec_eq_ok : forall f g,
    prec_eq_bool prec_nat f g = true <-> prec_eq prec_nat f g.

  Proof.
    intros f g. gen (prec_eq_bool_ok prec_nat f g). intuition.
    rewrite H1 in H. hyp. case_eq (prec_eq_bool prec_nat f g); intros.
    refl. rewrite H2 in H. absurd (prec_eq prec_nat f g); hyp.
  Qed.

  Definition bprec_eq_status_symb f g :=
    implb (prec_eq_bool prec_nat f g) (beq_status (status f) (status g)).

  Lemma bprec_eq_status_symb_ok : forall f g,
    bprec_eq_status_symb f g = true
    <-> (prec_eq prec_nat f g -> status f = status g).

  Proof.
    intros f g. unfold bprec_eq_status_symb, implb.
    case_eq (prec_eq_bool prec_nat f g); intros.
    rewrite prec_eq_ok in H. rewrite beq_status_ok. intuition.
    intuition. rewrite <- prec_eq_ok in H1. rewrite H in H1. discr.
  Qed.

  Section bprec_eq_status_aux1.

    Variable f : Sig.

    Fixpoint bprec_eq_status_aux1 (b: bool) (gs: list Sig) : bool :=
      match gs with
        | nil => b
        | g :: gs' => bprec_eq_status_aux1 (b && bprec_eq_status_symb f g) gs'
      end.

    Lemma bprec_eq_status_aux1_true : forall gs b,
      bprec_eq_status_aux1 b gs = true -> b = true.

    Proof.
      induction gs; simpl; intros. hyp.
      cut (b && bprec_eq_status_symb f a = true). rewrite andb_eq. intuition.
      apply IHgs. hyp.
    Qed.

    Implicit Arguments bprec_eq_status_aux1_true [gs b].

    Lemma bprec_eq_status_aux1_ok : forall gs b,
      bprec_eq_status_aux1 b gs = true ->
      forall g, In g gs -> prec_eq prec_nat f g -> status f = status g.

    Proof.
      induction gs; simpl; intros. contr. destruct H0.
      subst g. ded (bprec_eq_status_aux1_true H). rewrite andb_eq in H0.
      destruct H0. rewrite bprec_eq_status_symb_ok in H2. intuition.
      eapply IHgs. apply H. hyp. hyp.
    Qed.

  End bprec_eq_status_aux1.

  Implicit Arguments bprec_eq_status_aux1_ok [f gs b].

  Fixpoint bprec_eq_status_aux2 (b:bool) (fs: list Sig) : bool :=
    match fs with
      | nil => b
      | f :: fs' => bprec_eq_status_aux2 (bprec_eq_status_aux1 f b fs') fs'
    end.

  Lemma bprec_eq_status_aux2_true : forall fs b,
    bprec_eq_status_aux2 b fs = true -> b = true.

  Proof.
    induction fs; simpl; intros. hyp. eapply bprec_eq_status_aux1_true.
    apply IHfs. apply H.
  Qed.

  Implicit Arguments bprec_eq_status_aux2_true [fs b].

  Lemma bprec_eq_status_aux2_ok : forall fs b,
    bprec_eq_status_aux2 b fs = true -> forall f g, In f fs -> In g fs ->
      prec_eq prec_nat f g -> status f = status g.

  Proof.
    induction fs; simpl; intros. contr. destruct H0; destruct H1.
    subst f. subst g. refl.
    subst f. ded (bprec_eq_status_aux2_true H).
    apply (bprec_eq_status_aux1_ok H0); hyp.
    subst g. ded (bprec_eq_status_aux2_true H).
    sym. apply (bprec_eq_status_aux1_ok H1). hyp. apply prec_eq_sym. hyp.
    eapply IHfs; ehyp.
  Qed.
  
  Definition bprec_eq_status : list Sig -> bool := bprec_eq_status_aux2 true.

  Variable (Fs : list Sig) (Fs_ok : forall f, In f Fs).

  Lemma bprec_eq_status_ok : bprec_eq_status Fs = true ->
    forall f g, prec_eq prec_nat f g -> status f = status g.

  Proof.
    intros. eapply bprec_eq_status_aux2_ok. ehyp.
    apply Fs_ok. apply Fs_ok. hyp.
  Qed.

End prec_eq_status.

Implicit Arguments bprec_eq_status_ok [Sig Fs].

Ltac prec_eq_status s p o := apply (bprec_eq_status_ok s p o); check_eq
  || fail 10 "statuses incompatible with precedences".*)