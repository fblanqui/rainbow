(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2013-08-29

* Polynomial interpretation over domain rational numbers

*)

Set Implicit Arguments.

Require Import ATrs NewPolynom2 NewAPolyInt2 NewMonotonePolynom2
  NewPositivePolynom2 List cpf2color cpf QArith cpf_util
  cpf2color_number ListForall ListUtil NatUtil LogicUtil.

(***********************************************************************)
(** Some properties of default polynomial that are not yet proof in
CoLoR library. *)
(* FIXME: MOVE TO COLOR? *)

(** Cast *)

Definition poly_cast n m (Heq: n = m)(p: Qpoly n) : Qpoly m.
rewrite <- Heq; auto.
Defined.

(** Check positive coefficient in default polynomial interpretation. *)

Lemma pcoef_default_check : forall n: nat, coef_not_neg (default_poly n).

Proof. 
  intro n. unfold default_poly, coef_not_neg.
  rewrite lforall_eq. intros x H. destruct (in_map_elim H).
  destruct H0. subst. simpl. unfold OrdRingType2.QgeA. unfold OrdRingType2.QgtA. 
  unfold OrdRingType2.QeqA. intuition.
Qed.

Lemma default_poly_mxi_1 n i (H : lt i n) : In (1, Qmxi H) (default_poly n).

Proof.
  apply in_map_iff. exists {| val := i; prf := H|}. intuition.
  assert (In (mk_nat_lt H) (mk_nat_lts n)). apply mk_nat_lts_complete.
  auto.
Qed.

(** REMARK: this lemma already have in [APolyInt] but the prove is not
complete. *)

Section S.

  Variable arity : symbol -> nat.

  Notation Sig := (Sig arity).
  
  Require Import OrdRingType2.

  Lemma pstrong_monotone_default : PolyStrongMonotone (default_pi Sig).

  Proof.
    intro f. unfold Qpstrong_monotone. split. apply pweak_monotone_default.
    intros i Hi. unfold default_pi. simpl in *.
    assert (Hin : In (1, Qmxi Hi) (default_poly (arity f))).
    apply default_poly_mxi_1.
    set (w := coef_not_In_coef (default_poly (arity f)) (Qmxi Hi) 1
      (pcoef_default_check (arity f)) Hin).  
    auto with zarith.
    unfold QgtA. unfold QgeA in w. destruct w.
    unfold QgtA in H. rewrite <- H.
    apply one_QgtA_zero.
    unfold QeqA in H.
    rewrite H.
    apply one_QgtA_zero.
  Qed.
  
  (** [fun_of_pairs_list] is a representation for an interpretation
     associating to every function symbol of arity [n], an integer
     polynomial with [n] variables. It is represented by a list of pairs
     [(g, pi)], where [g] is a function symbol and [pi] is its
     interpretation *)
  
  Section fun_of_pairs_list.
    
    Variable f: symbol.

    Fixpoint fun_of_pairs_list_q (l : list {g : symbol & Qpoly (arity g)}) :
      Qpoly (arity f) :=
      match l with
        | existT g p :: l' =>
          match @eq_symb_dec Sig g f with
            | left h => poly_cast (f_equal arity h) p
            | right _ => fun_of_pairs_list_q l'
          end
        | nil => default_poly (arity f)
      end.
    
  End fun_of_pairs_list.

(***********************************************************************)
(** ** Polynomial interpretations in the setting of monotone algebras.
   In CoLoR library for proving polynomial interpretation uses [modules]
   and [functors]. Modules cannot be defined inside sections. These files
   are redefine and reproof from CoLoR library for polynomial
   interpretation use [records] instead. *)
  
  Require Import ARedPair2 APolyInt_MAQ2 AMonAlg2 Equality OrdRingType2 BoolUtil.
  
  Section WeakRedPair.
    
    Variable l : list {g : symbol & Qpoly (arity g)}.

    Variable H: forallb (fun x : {f : symbol & Qpoly (arity f)} =>
      let (f, p) := x in bcoef_not_neg p) l = true.
    
    Definition trsInt f := fun_of_pairs_list_q f l.

    (** The proof of polynomial are weakly monotone. *)
    
    Lemma trsInt_wm : forall f, Qpweak_monotone (trsInt f).

    Proof.
      intro f. unfold Qpweak_monotone, trsInt, fun_of_pairs_list_q.
      induction l.
      (* nil *)
      (* TODO *)
      apply pcoef_default_check.
      (* cons *)
      simpl in *. destruct a as [g]. destruct (@eq_symb_dec Sig g f).
      (* f = g *)
      unfold poly_cast. simpl_eq.
      rewrite andb_eq in H. destruct H.
      rewrite <- bcoef_not_neg_ok. apply H0.
      (* f <> g *)
      apply IHl0. rewrite andb_eq in H. destruct H. 
      apply H1.
    Qed.
    
    (** Polynomial interpretations in the setting of monotone algebras. *)
    
    Definition TPolyIntQ := mkbTPolyInt Sig trsInt trsInt_wm.

    Definition Poly_MonoAlgTypeQ := matQ Sig TPolyIntQ.
    
    (** Polynomial interpretation weak reduction pair. *)
    
    Definition Poly_WeakRedPair del := bwrp (Poly_MonoAlgTypeQ del).
    
    (** Reduction pair associated to a monotone algebra. *)
    
    Definition poly_wrpQ del := mkbWeakRedPair (wf_succ (Poly_WeakRedPair del))
      (sc_succ (Poly_WeakRedPair del))(bsucc_sub (Poly_WeakRedPair del))
      (sc_succeq (Poly_WeakRedPair del))
      (cc_succeq (Poly_WeakRedPair del))(ARedPair2.refl_succeq (Poly_WeakRedPair del))
      (ARedPair2.succ_succeq_compat (Poly_WeakRedPair del))
      (bsucceq_sub (Poly_WeakRedPair del)) (ARedPair2.trans_succ (Poly_WeakRedPair del))
      (ARedPair2.trans_succeq (Poly_WeakRedPair del)).
    
  End WeakRedPair.

  (** The proof of polynomial are strong monotone. *)
  
  Section trsInt_pw.

    Require Import ListExtras.

    Variable l : list {g : symbol & Qpoly (arity g)}.

    (* Using the relation [QgtA x y] to compare a coef in Qpoly] *)

    Variable H: forallb (fun x : {f : symbol & Qpoly (arity f)} =>
      let (f, p) := x in bcoef_not_neg p) l &&
    forallb (fun x : {f : symbol & Qpoly (arity f)} =>
      let (f, p) := x in 
        forallb (fun x0: nat_lt (arity f) => QbgtA (Qcoef (Qmxi (prf x0)) p) 0)
        (mk_nat_lts (arity f))) l = true.

    Lemma trsInt_pw : forall f, Qpstrong_monotone (trsInt l f).

    Proof.
      intro f. unfold Qpstrong_monotone, trsInt. induction l.
      (* nil *)
      split. 
      (* pweak_monotone *)
      apply pcoef_default_check.
      (* pstrong_monotone *)
      intros i Hi. apply pstrong_monotone_default.
      (* cons *)
      simpl in *. destruct a as [g]. split.
      (* pweak_monotone *)
      destruct (@eq_symb_dec Sig g f).
      (* f = g *)
      change (coef_not_neg (poly_cast (f_equal arity e) q)).
      unfold poly_cast. simpl_eq.
      repeat rewrite andb_eq in IHl0. intuition.
      rewrite <- bcoef_not_neg_ok. auto.
      rewrite andb_eq in H. destruct H.
      rewrite andb_eq in H1. destruct H1.
      apply H1.
      (* f <> g *)
      apply IHl0. rewrite andb_eq. intuition.
      repeat rewrite andb_eq in H. destruct H.
      destruct H0. apply H2.
      repeat rewrite andb_eq in H. destruct H.
      destruct H1. apply H2.
      (* pstrong_monotone *)
      destruct IHl0. repeat rewrite andb_eq in H. intuition.
      intros i Hi. destruct (@eq_symb_dec Sig g f).
      (* f = g *)
      repeat rewrite andb_eq in H. subst.
      destruct H.
      assert (In (mk_nat_lt Hi) (mk_nat_lts (arity f))).
      apply mk_nat_lts_complete. intuition.
      rewrite forallb_forall in H5. ded (H5 _ H4).
      rewrite QbgtA_ok in H6. simpl in *.
      simpl_eq. unfold QgtA. apply H6. 
      (* f <> g *)
      ded (H1 i Hi). apply H2.
    Qed.

  End trsInt_pw.

End S.