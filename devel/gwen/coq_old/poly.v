(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2013-04-20

* Polynomial interpretation over domain natural numbers

*)

Set Implicit Arguments.

Require Import ATrs ARedPair2 APolyInt_MA2 AMonAlg2 Equality
  ListForall ListUtil ZUtil LogicUtil BoolUtil Polynom APolyInt
  MonotonePolynom PositivePolynom NatUtil AMatrixBasedInt2_Nat
  VecArith2 VecUtil Matrix2 AMatrixInt2 cpf2color cpf_util cpf
  AArcticBasedInt2 AArcticInt2.

(***********************************************************************)
(** Some properties of default polynomial that are not yet proof in
CoLoR library. *)

(* FIXME: MOVE TO COLOR? *)

(** Cast *)

Definition poly_cast n m (Heq: n = m)(p: poly n) : poly m.
rewrite <- Heq; auto.
Defined.

(** Check positive coefficient in default polynomial interpretation. *)

Lemma pcoef_default_check : forall n: nat, coef_pos (default_poly n).

Proof. 
  intro n. unfold default_poly, coef_pos.
  rewrite lforall_eq. intros x H. destruct (in_map_elim H).
  destruct H0. subst. simpl. omega.
Qed.

Lemma default_poly_mxi_1 n i (H : i < n) : In (1%Z, mxi H) (default_poly n).

Proof.
  apply in_map_iff. exists {| val := i; prf := H|}. intuition.
  assert (In (mk_nat_lt H) (mk_nat_lts n)). apply mk_nat_lts_complete.
  auto.
Qed.

(***********************************************************************)
(** REMARK: this lemma already have in [APolyInt] but the prove is not
   complete. *)

Section S.
  
  Variable arity : symbol -> nat.

  Notation Sig := (Sig arity).
  
  Lemma pstrong_monotone_default : PolyStrongMonotone (default_pi Sig).

  Proof.
    intro f. unfold pstrong_monotone. split. apply pweak_monotone_default.
    intros i Hi. unfold default_pi. simpl in *.
    assert (Hin : In (1%Z, mxi Hi) (default_poly (arity f))).
    apply default_poly_mxi_1.
    set (w := coefPos_geC (default_poly (arity f)) (mxi Hi) 1
      (pcoef_default_check (arity f)) Hin). auto with zarith.
  Qed.
  
  (** [fun_of_pairs_list] is a representation for an interpretation
     associating to every function symbol of arity [n], an integer
     polynomial with [n] variables. It is represented by a list of pairs
     [(g, pi)], where [g] is a function symbol and [pi] is its
     interpretation *)
  
  Section fun_of_pairs_list.
    
    Variable f: symbol.
      
    Fixpoint fun_of_pairs_list (l : list {g : symbol & poly (arity g)}) :
      poly (arity f) :=
      match l with
        | existT g p :: l' =>
          match @eq_symb_dec Sig g f with
            | left h => poly_cast (f_equal arity h) p
            | right _ => fun_of_pairs_list l'
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

  Section WeakRedPair.

    Variable l : list {g : symbol & poly (arity g)}.

    Variable H: forallb (fun x : {f : symbol & poly (arity f)} =>
      let (f, p) := x in bcoef_pos p) l = true.
    
    Definition trsInt f := fun_of_pairs_list f l.
    
  (** The proof of polynomial are weakly monotone. *)
    
    Lemma trsInt_wm : forall f, pweak_monotone (trsInt f).

    Proof.
      intro f. unfold pweak_monotone, trsInt, fun_of_pairs_list.
      induction l.
      (* nil *)
      apply pcoef_default_check.
      (* cons *)
      simpl in *. destruct a as [g]. destruct (@eq_symb_dec Sig g f).
      (* f = g *)
      unfold poly_cast. simpl_eq.
      rewrite andb_eq in H. destruct H.
      rewrite <- bcoef_pos_ok. hyp.
      (* f <> g *)
      apply IHl0. rewrite andb_eq in H. destruct H. hyp.
    Qed.
  
    (** Polynomial interpretations in the setting of monotone algebras. *)

    Definition TPolyInt := mkbTPolyInt Sig trsInt trsInt_wm.

    Definition Poly_MonoAlgType := mat Sig TPolyInt.
  
    (** Polynomial interpretation weak reduction pair. *)
    
    Definition Poly_WeakRedPair := bwrp Poly_MonoAlgType.
  
    (** Reduction pair associated to a monotone algebra. *)
  
    Definition poly_wrp := mkbWeakRedPair (wf_succ Poly_WeakRedPair)
      (sc_succ Poly_WeakRedPair)(bsucc_sub Poly_WeakRedPair)
      (sc_succeq Poly_WeakRedPair)
      (cc_succeq Poly_WeakRedPair)(ARedPair2.refl_succeq Poly_WeakRedPair)
      (ARedPair2.succ_succeq_compat Poly_WeakRedPair)
      (bsucceq_sub Poly_WeakRedPair) (ARedPair2.trans_succ Poly_WeakRedPair)
      (ARedPair2.trans_succeq Poly_WeakRedPair).
  
  End WeakRedPair.

  (** The proof of polynomial are strong monotone. *)

  Section trsInt_pw.

    Variable l : list {g : symbol & poly (arity g)}.

    Variable H: forallb (fun x : {f : symbol & poly (arity f)} =>
      let (f, p) := x in bcoef_pos p) l &&
    forallb (fun x : {f : symbol & poly (arity f)} =>
      let (f, p) := x in forallb
        (fun x0 : nat_lt (arity f) => is_pos (coef (mxi (prf x0)) p))
        (mk_nat_lts (arity f))) l = true.
    
    Lemma trsInt_pw : forall f, pstrong_monotone (trsInt l f).
      
    Proof.
      intro f. unfold pstrong_monotone, trsInt. induction l.
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
      change (coef_pos (poly_cast (f_equal arity e) p)).
      unfold poly_cast. simpl_eq.
      repeat rewrite andb_eq in H. intuition.
      rewrite <- bcoef_pos_ok. auto.
      (* f <> g *)
      apply IHl0. rewrite andb_eq. intuition.
      repeat rewrite andb_eq in H. destruct H.
      destruct H0. hyp.
      repeat rewrite andb_eq in H. destruct H.
      destruct H1. hyp.
      (* pstrong_monotone *)
      destruct IHl0. repeat rewrite andb_eq in H. intuition.
      intros i Hi. destruct (@eq_symb_dec Sig g f).
      (* f = g *)
      repeat rewrite andb_eq in H. subst.
      destruct H.
      assert (In (mk_nat_lt Hi) (mk_nat_lts (arity f))).
      apply mk_nat_lts_complete. intuition.
      rewrite forallb_forall in H5. ded (H5 _ H4).
      rewrite is_pos_ok in H6. simpl in *.
      simpl_eq. omega.
      (* f <> g *)
      ded (H1 i Hi). hyp.
    Qed.

  End trsInt_pw.
End S.