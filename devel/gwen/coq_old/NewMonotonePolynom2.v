(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-25
- Adam Koprowski, 2008-05-27, 
    introduced distinction of weak/strong monotonicity

monotone polynomials

- Kim Quyen Ly, 2013-08-26

Monotone polynomials in domain rational numbers.

*)

Set Implicit Arguments.

Require Import NewPolynom2 NewPositivePolynom2 NaryFunction VecUtil
  LogicUtil ListUtil ListForall List ZUtil RelUtil NatUtil
  OrdRingType2 VecArith2 ListExtras RingType2 QArith.

Section RingMonoPoly.
 
  Definition Qpweak_monotone n (p : Qpoly n) := coef_not_neg p.
   
  Notation "0" := QA0.
  Notation "x >A y" := (QgtA x y) (at level 70).
  Notation "x >=A y" := (QgeA x y) (at level 70).

  Definition Qpstrong_monotone n (p : Qpoly n) := Qpweak_monotone p /\
    forall i (H : lt i n), Qcoef (Qmxi H) p >A 0.

  Open Local Scope Q_scope.
 
  (* REMARK: Notation and Definition has different behaviour. *)
 
  Notation pos := (fun z => z >=A 0).
  Notation D := (sig pos).
  Notation inj := (@exist Q pos _).
  Notation vec := (vector D).
  Notation val := (@proj1_sig Q pos).
  Notation vals := (@Vmap D Q val _).
  
  Lemma meval_monotone_D : forall i (vi : vec i) (mi : monom i)
    j (vj : vec j) (mj : monom j) k x y (Hx : x >=A 0) (Hy : y >=A 0),
    x >=A y -> 
    meval (Vapp mi (Vcons k mj)) (vals (Vapp vi (Vcons (inj Hx) vj)))
    >=A meval (Vapp mi (Vcons k mj)) (vals (Vapp vi (Vcons (inj Hy) vj))).
    
  Proof.
    intros. do 2 rewrite Vmap_app. simpl Vmap. simpl in *.
    unfold QgeA. unfold OrdRingType2.QeqA. unfold QgtA.
    do 2 rewrite meval_app.
    apply Qmul_geA_mono_l. Focus 2. simpl meval. apply Qmul_geA_mono_r.
    Focus 2. apply Qpower_geA_compat. hyp. hyp.
    apply not_neg_meval. 
    apply not_neg_meval.
  Qed.

  Lemma coef_not_neg_monotone_peval_Dge : forall n (p : Qpoly n)
    (H : coef_not_neg p), Vmonotone1 (peval_D p H) QDge.
      
  Proof.
    unfold Vmonotone1, Vmonotone, peval_D, Vmonotone_i, restrict, monotone.
    intros n p H_coef_not_neg i j Hij vi vj. destruct x as (x, Hx).
    destruct y as (y, Hy). simpl. intro Hxy.
    generalize dependent p. intro p. elim p.
    intro. simpl. 
    apply QgeA_refl. 
    unfold coef_not_neg. intros (c, m) p' Hrec H_coef_not_neg.
    simpl in H_coef_not_neg. generalize H_coef_not_neg. clear H_coef_not_neg.
    intros (H_not_neg_c, H_coef_not_neg_p').
    generalize (Hrec H_coef_not_neg_p'). clear Hrec. intro H.
    lazy beta iota delta [peval]. fold peval.
    apply Qadd_geA_compat. 
    2: apply H.
    clear H.
    apply Qmul_geA_mono_l. 
    hyp.
    rewrite (Vbreak_eq_app_cast Hij m).
    set (mi := (fst (Vbreak (n1:=i) (n2:=S j) (Vcast m (sym_equal Hij))))).
    set (mj := (snd (Vbreak (n1:=i) (n2:=S j) (Vcast m (sym_equal Hij))))).
    rewrite (VSn_eq mj).
    case Hij. simpl. repeat rewrite Vcast_refl.
    apply meval_monotone_D.
    hyp.
  Qed.

  Implicit Arguments coef_not_neg_monotone_peval_Dge [n p i j x y].

  (* TODO *)
  Lemma pmonotone_imp_monotone_peval_Dgt : forall n (p : Qpoly n) 
    (H: Qpstrong_monotone p), Vmonotone1 (peval_D p (proj1 H)) QDgt.

  Proof. 
    unfold QDgt. unfold QgtA.
    intros n p (H_coef_not_neg_p, H_pmonotone_p) i j Hij.
    gen (H_pmonotone_p _ (i_lt_n (sym_equal Hij))). unfold QgtA.
   intro H. elim H. clear H. intros p1 H. 

  Admitted.

  Lemma pmonotone_imp_monotone_peval_Dgt' : forall n (p : Qpoly n)
    (wm : Qpweak_monotone p) (sm : Qpstrong_monotone p), 
     Vmonotone1 (peval_D p wm) QDgt.

  Proof.
    intros n p wm sm. generalize (pmonotone_imp_monotone_peval_Dgt).
    unfold Vmonotone1, Vmonotone, Dgt, Vmonotone_i, peval_D, restrict,
      monotone.
    intros H0 i j Hij vi vj. destruct x as (x, Hx). destruct y as (y, Hy).
    simpl. intro Hxy.
    generalize (H0 n p sm i j Hij vi vj (exist _ x Hx) (exist _ y Hy) Hxy). 
    clear H0. simpl. intuition.
  Qed.

  (***********************************************************************)
  (** Bolean functions for checking monotony conditions. *)

  Definition bQpweak_monotone n (p : Qpoly n) := bcoef_not_neg p.
  Definition bQpweak_monotone_ok n (p : Qpoly n) := bcoef_not_neg_ok p.
  
  Implicit Arguments mk_nat_lts [].
  Implicit Arguments mk_nat_lts_aux [].

  (** Using QbgtA to compare coef in p > 0 *)

  Definition bQpstrong_monotone n (p : Qpoly n) :=
    bcoef_not_neg p
    && forallb (fun x => QbgtA (Qcoef (Qmxi (prf x)) p)0) (mk_nat_lts n).

  Require Import BoolUtil.
  
  (** Using relation QbgtA to compare a coef in Qpoly > 0 *)
 
  Lemma bpstrong_monotone_ok : forall n (p : Qpoly n),
    bQpstrong_monotone p = true <-> Qpstrong_monotone p.
    
  Proof.
    induction p.
    (* nil *)
    unfold Qpstrong_monotone, bQpstrong_monotone, Qpweak_monotone. simpl.
    intuition. unfold mk_nat_lts in H. unfold QbgtA in H. destruct n.
    unfold QgtA. unfold QgtA_dec in H. unfold Qgt_dec in H. absurd_arith.
    unfold QgtA_dec in H. unfold Qgt_dec in H.
    destruct n; discr.
    destruct n. refl. ded (H1 n (le_n (S n))). unfold QbgtA. unfold QgtA_dec.
    unfold Qgt_dec. unfold QgtA in H.
    (* cons *)
    Focus 2.
    destruct a. intuition.
    (* -> *)
    unfold Qpstrong_monotone, Qpweak_monotone.
    unfold bQpstrong_monotone, bcoef_not_neg in H1.
    Opaque Qcoef. simpl in *.
    rewrite !andb_eq in H1. intuition. change (bcoef_not_neg p = true) in H4. 
    rewrite <- Qbnot_neg_ok. apply H1.
    change (bcoef_not_neg p = true) in H4.
    rewrite <- bcoef_not_neg_ok. apply H4.
    assert (In (mk_nat_lt H2) (mk_nat_lts n)). apply mk_nat_lts_complete.
    rewrite forallb_forall in H3. ded (H3 _ H5).
    rewrite QbgtA_ok in H6. simpl in H6. unfold QgtA.
    apply H6.
    (* <- *)
    unfold Qpstrong_monotone, Qpweak_monotone in H1.
    unfold bQpstrong_monotone, bcoef_not_neg. simpl in *. 
    rewrite !andb_eq. intuition. rewrite Qbnot_neg_ok.
    apply H1.
    change (bcoef_not_neg p = true). rewrite bcoef_not_neg_ok.
    apply H4.
    rewrite forallb_forall. intros [i hi Hi]. simpl.
    rewrite QbgtA_ok. ded (H3 _ hi). unfold QgtA in H2.
    apply H2. Transparent Qcoef.
    (* TODO *)
    
  Admitted.

End RingMonoPoly.
  
(***********************************************************************)
(** forall_lt *)

Section forall_lt.
  
  Variables (P: nat -> Prop) (bP: nat -> bool)
    (bP_ok: forall i, bP i = true <-> P i).
  
  Open Local Scope nat_scope.
  
  (* P is satisfied for all i < n *)
  
  Definition forall_lt n:= forall i, i<n -> P i.
  
  (* bP is true for all i < n *)

  Fixpoint bforall_lt n :=
    match n with
      | O => true
      | S n' => bP n' && bforall_lt n'
    end.
  
  Lemma forall_lt_S : forall n, forall_lt (S n) <-> P n  /\ forall_lt n.
    
  Proof.
    intros. unfold forall_lt. firstorder.
    case (lt_ge_dec i n); intro. firstorder.
    assert (i=n). omega. subst. hyp.
  Qed.
  
  (*REMOVE: already in BoolUtil*)
  
  Lemma bP_ko : forall i, bP i = false <-> ~ P i.
    
  Proof.
    intros. case_eq (bP i); intros.
    rewrite bP_ok in H. intuition.
    rewrite <- bP_ok. intuition.
    rewrite H in H1. discr.
  Qed.
  
  Lemma bforall_lt_S : forall n,  bforall_lt (S n) = bP n && bforall_lt n.
    
  Proof.
    refl.
  Qed.
  
  Lemma bforall_lt_ok : forall n, bforall_lt n = true <-> forall_lt n.
    
  Proof.
    induction n. unfold forall_lt. simpl. firstorder.
    rewrite forall_lt_S. rewrite bforall_lt_S. rewrite andb_eq. rewrite bP_ok.
    tauto.
  Qed.
  
End forall_lt.

  (***********************************************************************)
  (** and_or *)

  (* MOVE: added in BoolUtil *)

Section and_or.

  Variables (A : Type) (P Q : A->Prop) (bP bQ : A->bool)
    (bP_ok : forall x, bP x = true <-> P x)
    (bQ_ok : forall x, bQ x = true <-> Q x).
  
  Lemma band_ok : forall x, bP x && bQ x = true <-> P x /\ Q x.
    
  Proof.
    intros. rewrite andb_eq. split. intros. split. destruct H. 
    rewrite bP_ok in H. hyp. destruct H. rewrite bQ_ok in H0. hyp. 
    intros. split. destruct H. rewrite <- bP_ok in H. hyp. 
    destruct H. rewrite <- bQ_ok in H0. hyp. 
  Qed.
  
  Lemma bor_ok : forall x, bP x || bQ x = true <-> P x \/ Q x.
    
  Proof.
    intros. rewrite orb_eq. split. intros. destruct H. left.  
    rewrite bP_ok in H. hyp. right. rewrite bQ_ok in H. hyp. intros. destruct H. 
    left. rewrite <- bP_ok in H. hyp. right. rewrite <- bQ_ok in H. hyp. 
  Qed.
  
End and_or.

(***********************************************************************)
(** Polynomials of degree 2 *) 

Section poly2.
  
  Open Local Scope nat_scope.
  
  Fixpoint degree n (v : monom n) {struct v} : nat :=
    match v with
      | Vnil => O
      | Vcons k _ v => (k + degree v)%nat
    end.
  
  Variables (n : nat) (p : Qpoly n).
  
  Variable hyp : forall m : monom n, degree m >= 3 -> Qcoef m p =A= 0.
  
  (***********************************************************************)
  (** Coefficients of polynomials of degree 2. *) 
  
  Definition mxij i (hi: i<n) j (hj: j<n) := mmult (Qmxi hi) (Qmxi hj).

  Definition a i (hi: i<n) j (hj: j<n) := Qcoef (mxij hi hj) p.
  Definition b i (hi: i<n) := Qcoef (Qmxi hi) p.
  Definition c := Qcoef (mone n) p.
  
  (***********************************************************************)
  (** Predicate saying that coefficients are non-negative, except 
     the coefficients of the linear monomials: aij >= 0, aj >= -ajj , a0 >= 0 *)
  
  (***********************************************************************)
  (** P: aj >= - ajj*)

  Notation "x >=A y" := (QgeA x y) (at level 70).
  Notation "x >A y" := (QgtA x y) (at level 70).

  Definition P j := forall (hj: j<n), b hj  >=A - a hj hj.

  Definition bP j := match lt_ge_dec j n with
                       | left hj => QbgeA (b hj) (- a hj hj)
                       | _ => true
                     end.
  
  Lemma bP_ok : forall j, bP j = true <-> P j.
    
  Proof.
    intro j. unfold bP, P. case (lt_ge_dec j n); intro hj. rewrite QbgeA_ok.
    split; intro h. intro hj'. rewrite (lt_unique hj' hj). hyp. auto.
    firstorder.
  Qed.
  
  (***********************************************************************)
  (** P': aj > - ajj*)
  
  Definition P' j := forall (hj: j<n), b hj >A - a hj hj.
  
  Definition bP' j := match lt_ge_dec j n with
                        | left hj => QbgtA (b hj) (- a hj hj)
                        | _ => true
                      end.
  
  Lemma bP'_ok : forall j, bP' j = true <-> P' j.
    
  Proof.
    intro j. unfold bP', P'. case (lt_ge_dec j n); intro hj.
    rewrite QbgtA_ok.
    split; intro h. intros hj'. rewrite (lt_unique hj' hj). hyp. 
    auto. firstorder. intuition.
  Qed.
  
  (***********************************************************************)
  (** R: aij >= 0 *)
  
  Section R.
    
    Variable i : nat .
    
    Definition R j := forall (hi: i < n) (hj: j < n), a hi hj >=A QA0.
    
    Definition bR j :=
      match lt_ge_dec i n, lt_ge_dec j n with
        | left hi, left hj => Qbnot_neg (a hi hj)
        | _, _ => true
      end.
    
    Lemma bR_ok : forall j, bR j = true <-> R j.
      
    Proof.
      intro j. unfold bR, R. case (lt_ge_dec i n); intros hi.
      case (lt_ge_dec j n); intros hj. rewrite Qbnot_neg_ok. split; intro h.
      intros hi' hj'. rewrite (lt_unique hi' hi). rewrite (lt_unique hj' hj). hyp.
      auto. firstorder. firstorder.
    Qed.
    
  End R.
  
  Definition Q i := forall_lt (R i) n.
  
  Definition bQ i := bforall_lt (bR i) n.
  
  Lemma bQ_ok : forall i, bQ i = true <-> Q i.
    
  Proof.
    intro i. unfold bQ, Q. apply bforall_lt_ok. 
    intros j. apply bR_ok. 
  Qed.
  
  (***********************************************************************)
  (** Monotone *) 
  
  Definition monotone := 
    c >=A QA0
    /\ forall j (hj: j<n), b hj >=A - a hj hj 
      /\ forall i j (hi: i<n) (hj: j<n), a hi hj >=A QA0.

  Notation not_neg := (fun z => z >=A QA0).
  
  Definition monotone' := not_neg c /\ forall_lt P n /\ forall_lt Q n.
  
  Lemma monotone_eq' : monotone <-> monotone'.
    
  Proof.
    unfold monotone, monotone', forall_lt, P, Q, R, forall_lt. intuition.
    destruct (H1 _ hj). hyp. destruct (H1 _ hj). apply H4.
  Qed.
  
  Definition bmonotone := Qbnot_neg c && bforall_lt bP n && bforall_lt bQ n.
  
  (***********************************************************************)
  (** Strict monotone *)

  Definition strict_monotone := 
    c >=A QA0
    /\ forall j (hj: j<n), b hj >A - a hj hj 
      /\ forall i j (hi: i<n) (hj: j<n), a hi hj >=A QA0.
  
  Definition strict_monotone' :=
    not_neg c /\ forall_lt P' n /\ forall_lt Q n.
  
  Lemma strict_monotone_eq' : strict_monotone <-> strict_monotone'.
    
  Proof.
    unfold strict_monotone, strict_monotone', forall_lt, P', Q, R, forall_lt. 
    intuition. destruct (H1 _ hj). hyp. destruct (H1 _ hj).  apply H4.
  Qed.
  
  Definition bstrict_monotone :=
    Qbnot_neg c && bforall_lt bP' n && bforall_lt bQ n.
  
  (***********************************************************************)
  (** Logic *) 

  (* MOVE: added to LogicUtil*)

  Section logic.
    
    Variables P Q P' Q' : Prop.
    
    Lemma and_iff : ((P <-> P') /\ (Q <-> Q')) -> ((P /\ Q) <-> (P' /\ Q')).
      
    Proof.
      tauto.
    Qed.
    
  End logic.
  
  (***********************************************************************)
  (** Correctness of monotone and strictly monotone conditions. *)
  
  Lemma bmonotone_ok : bmonotone = true <-> monotone.
    
  Proof.
    rewrite monotone_eq'. unfold bmonotone, monotone'. repeat rewrite andb_eq.
    rewrite <- and_assoc. apply and_iff. split. rewrite Qbnot_neg_ok. tauto.
    apply and_iff. split. apply bforall_lt_ok. apply bP_ok.
    apply bforall_lt_ok. unfold bQ, Q. intro i. apply bforall_lt_ok. intro j.
    apply bR_ok.
  Qed.
  
  Lemma bstrict_monotone_ok : bstrict_monotone = true <-> strict_monotone.
    
  Proof.
    rewrite strict_monotone_eq'. unfold bstrict_monotone, strict_monotone'.
    repeat rewrite andb_eq. rewrite <- and_assoc. apply and_iff. split.
    rewrite Qbnot_neg_ok. tauto.
    apply and_iff. split. apply bforall_lt_ok. apply bP'_ok.  
    apply bforall_lt_ok. unfold bQ, Q. intros i. apply bforall_lt_ok. intro j.
    apply bR_ok. 
  Qed.
  
End poly2.
