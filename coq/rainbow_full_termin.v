(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2011-04-06

* CPF correctness checker

*)

Set Implicit Arguments.

Require Import ATrs SN ZArith EqUtil String List ListDec ListForall
  ListUtil ZUtil LogicUtil BoolUtil VecUtil NArith RelUtil RelMidex
  ARelation NatUtil ADP ADuplicateSymb ListExtras RelUtil AVarCond
  AMorphism ADecomp ADPUnif ACalls OrdSemiRing2 Polynom2
  MonotonePolynom2 PositivePolynom2 AMannaNess ARedPair2 APolyInt2
  error_monad cpf2color AWFMInterpretation cpf Z_as_SR.

Section Top.

  (* Assume given a function translating variable names into
     natural numbers. *)

  Variable nat_of_string : string -> nat.

  (* Assume the maximum number of arguments compared lexicographically
  in RPO. *)

  Variable rpo_arg : nat.

  (* An extra argument for function [dpProof], decreasing argument in a
  Fixpoint. *)

  Variable n : nat.

  (**************************************************************************)
  (** ** Check that [p] is a valid termination proof for [red R].           *)
  (**************************************************************************)

  Section S.

    (* We assume given an arity function. *)

    Variable arity : symbol -> nat.

    Notation aterm := (aterm arity).
    Notation arule := (arule arity).
    Notation arules := (arules arity).
    Notation abrule := (abrule arity).
    
    Implicit Type R : arules.

    Section Full_Termin.

      (* Declare Notation for Sig inside this section. *)

      Notation Sig := (Sig arity).

      (************************************************************************)
      (** ** Polynomial interpretation on N. *)
      (************************************************************************)

      Import OSR_Notations.
      
      (* Build coefficient of [Z] on ring structure. *)
      
      Global Instance coef_ring_Z : CPFRing.
      
      Proof.
        apply Build_CPFRing with (or:= Z_as_OR).
        apply color_coef_Z.
      Defined.

      (* Conditions for polynomial interpretation on N terminates:
       - check that coefficients are non-negative (=> polynomials are
      monotone).
      - in general, polynomial interpretation on naturals is
      undecidable.  We chose the method checking the positivity of
      coefficients (=> coef > 0). This problem is undecidable in
      general. The comparision of polynomials amounts to the
      positiveness check where we consider: [Pn(x) - Qn(x) - 1]. It
      states that evaluation of a polynomial is always greater
      [resp. greater or equal] than [0] iff all of its coefficients
      are non-negative and the constanst factor is positive. *)

      Definition conditions_poly_nat l :=
        forallb (fun x => match x with 
          existT f p => bcoef_not_neg p end) l &&
        forallb (fun x => match x with
          existT f p => forallb (fun x => or_bgt (coef (mxi (prf x)) p) 0)
            (mk_nat_lts (arity f)) end) l.

      (* >= has coefficents are non-negative *)
     
      Definition redpair_poly_nat_ge t u pi :=
        bcoef_not_neg (@rulePoly_ge _ Sig pi (mkRule t u)).

      (* > has coefficients are non-negative *)

      Definition redpair_poly_nat_gt t u pi :=
        bcoef_not_neg (@rulePoly_gt _ Sig pi (mkRule t u)).

      Definition poly_nat (is: list (symbol * cpf.arity * function)) :
        result ((aterm -> aterm -> bool) * (aterm -> aterm -> bool)) :=
        (* We first check that interprets can be translated into polynomials
         with a number of variables less than the arity of the corresponding
         function symbols. *)
        Match map_rev (@color_interpret arity coef_ring_Z) is With l ===>
         if conditions_poly_nat l
         then (* build polynomial interpretation *)
           let pi := fun f : Sig => fun_of_pairs_list arity f l in
           (* A reduction pair (>=, >) where coefficients are non-negative *)
           Ok (fun t u => redpair_poly_nat_ge t u pi,
               fun t u => redpair_poly_nat_gt t u pi)
         else Ko _ (Fail FNotMonotone).

      (************************************************************************)
      (** Correctness of polynomial interpretation of domain natural numbers.
       REMARK: use function [I] in [APolyInt_MA2.v]. *)

      Require Import APolyInt_MA2.

      (* check >= in R *)

      Definition ge_R R bge := forallb (brule bge) R.

      (* remove > in R *)

      Definition gt_R R bgt := Ok (filter (brule (neg bgt)) R).

      (* REMOVE *)
      Lemma poly_nat_ok' : forall (R R': arules) is
        (h: match poly_nat is with
              | Ok (bge, bgt) =>
                if   ge_R R bge
                then gt_R R bgt
                else Ko _ (Fail FRuleNotInLargeOrdering_poly)
              | Ko e => Ko _ e
            end = Ok R') (wf: WF (red R')), WF (red R).
      
      Proof.
        intros R R' is h wf.
        case_eq (poly_nat is); intros p H; rewrite H in h; try discr.
        (* Declare [bge bgt]. *)
        destruct p as [bge bgt].
        (* check >= in R *)
        case_eq (ge_R R bge); intros H0; rewrite H0 in h; try discr.
        unfold gt_R in h. unfold ge_R in H0.
        (* bgt \in R = R' *)
        inversion h. subst R'. clear h.
        unfold poly_nat in H. revert H.
        case (map_rev (color_interpret arity) is); intros l H; try discr.
        case_eq (conditions_poly_nat l); intro H2; rewrite H2 in H;
        try discr.
        inversion H. clear H.
        unfold conditions_poly_nat in H2.
        set (trsInt := fun f: symbol => fun_of_pairs_list arity f l).
        cut (forall f: symbol, pweak_monotone (trsInt f)).
        intro trsInt_wm.
        (** Proving [WF (red R)] by redPair interpretation *)
        rewrite andb_eq in H2. destruct H2.
        apply WF_rp_red with (WP := @WP arity _ l H).
        (** A proof of [>] are closed by context: IR_context_closed. *)
        change (context_closed (IR (@I Sig _(TPolyInt_poly arity l H)) succ)).
        apply IR_context_closed. apply pi_monotone.
        simpl. intro f.
        (** Polynomial is strong monotone. *)
        apply trsInt_pw_poly. rewrite andb_eq. split. hyp. hyp.
        (** Check that all rules [R] are included in [>=]. *)
        simpl; unfold brule, bsucceq, bool_of_rel; simpl.
        rewrite forallb_forall. intros x Hx. subst bge.
        rewrite forallb_forall in H0. ded (H0 x Hx). destruct x as [t u].   
        simpl in *.
        case_eq (succeq'_dec Sig (TPolyInt_poly arity l H) t u);
          intros s Hs. auto. unfold redpair_poly_nat_ge in H2.
        unfold brule in H2. unfold succeq' in s.
        rewrite bcoef_not_neg_ok in H2. contradiction.
        (** Remove all rules [R] are included in [>]. *)
        apply WF_incl with (S:=red (filter (brule (neg bgt))R)).
        unfold inclusion. intros t u H7. redtac. unfold red.
        exists l0. exists r. exists c. exists s. intuition.
        apply filter_In. apply filter_In in lr. intuition.
        unfold brule, neg. unfold brule, neg in H5. simpl in *.
        unfold bsucc, bool_of_rel in H5. simpl in *.
        destruct succ'_dec in H5. discr.
        unfold succ' in n0. rewrite <- bcoef_not_neg_ok in n0.
        apply eq_true_not_negb in n0.
        subst bgt. apply n0. hyp.
        (** Proving polynomial is weak monotone. *)
        intro f. apply trsInt_wm_poly. rewrite andb_eq in H2.
        destruct H2. hyp.
      Qed.

      (* TODO *)
      Lemma poly_nat_ok : forall R bge bgt is, 
                            poly_nat is = Ok (bge, bgt) -> 
                            forallb (brule bge) R = true ->
                            WF (red (filter (brule (neg bgt)) R)) -> WF (red R).
     
      Proof.
      Admitted.

      (************************************************************************)
      (** ** Polynomial interpretation on Q. *)
      (************************************************************************)

      (* Given a positive real number [delta] \in R_>0, a well-founded
       and stable (strict) ordering [>_delta] on terms is defined as
       follows: for all [t, s \in T(F, V), t >_delta s] if and only if
       [[t] - [s] >=_R delta].
       
       - [delta > 0]
       - rulePoly_gtQ x y : P_x - P_y - delta >= 0. *)
      
      Require Import Q_as_R QArith APolyInt2.
      
      Open Scope Q_scope.

      (* Build coefficient of type [Q] on ring structure. *)
      
      Global Instance coef_ring_Q: CPFRing.
      
      Proof.
        apply Build_CPFRing with (or:= Q_as_OR).
        apply color_coef_Q.
      Defined.

      (* Conditions of Polynomial interpretations on [Q]. *)

      Definition conditions_poly_rat l :=
        forallb (fun x => match x with
          existT f p => bcoef_not_neg p end) l &&
        forallb (fun x => match x with
           existT f p => forallb (fun x => or_bgt (coef (mxi (prf x)) p)0)
             (mk_nat_lts (arity f)) end) l.

      (* >= coefficient are non-negative *)
      Definition redpair_poly_rat_ge t u pi :=
        bcoef_not_neg (@rulePoly_ge Q_as_OR Sig pi (mkRule t u)).

      (* > coefficient are non-negative *)
      Definition redpair_poly_rat_gt t u pi del :=
        bcoef_not_neg (@rulePoly_gtQ Q_as_OR Sig pi del (mkRule t u)).

      Definition poly_rat (is: list (symbol * cpf.arity * function)) (del:Q) :
        result ((aterm -> aterm -> bool) * (aterm -> aterm -> bool)) :=
        (* first check that the interprets can be translated into polynomials *)
        Match map_rev (@color_interpret arity coef_ring_Q) is With l ===>
        if conditions_poly_rat l
        then (* build polynomial interpretations *)
          let pi := fun f : Sig => fun_of_pairs_list arity f l in
          (* If the two conditions above satisfy,
             then return the reduction pair (>=, >) *)
          Ok (fun t u => redpair_poly_rat_ge t u pi,
              fun t u => redpair_poly_rat_gt t u pi del)
        (* Otherwise, return error if not satisfy the conditions. *)
        else Ko _ (Fail FNotMonotone_rat).

      (*******************************************************************) 

      Definition type_poly_rationals del is :=
        match del with
          | Number_integer i      => poly_rat is (inject_Z i) (* i/1 *)
          | Number_rational i pos =>
            let q := Qmake i pos in
            poly_rat is q
        end.
      
      (************************************************************************)
      (** Correctness proof of polynomial interpretation over domain
      rational numbers. *)
    
      (** This is a common proof for polynomial of type rational
      number. *)

      Lemma poly_rat_comm_ok : forall (R R' : arules) del is
       (h:match poly_rat is del with
            | Ok (bge, bgt) =>
              if   ge_R R bge
              then gt_R R bgt
              else Ko _ (Fail FRuleNotInLargeOrdering_poly)
            | Ko e => Ko _ e
          end = Ok R')(wf:WF (red R')), WF (red R).

      Proof.
        intros R R' del is h wf.
        case_eq (poly_rat is del);
          intros p H1; rewrite H1 in h; try discr.       
        destruct p as [bge bgt].
        (* check R [=] R' *)
        (*case_eq (equiv_rules R R'); intro H2; rewrite H2 in h;
        try discr.*)
        (* check >= in R *)
        case_eq (ge_R R bge); intro H3; rewrite H3 in h;
        try discr.
        unfold gt_R in h. unfold ge_R in H3.
        inversion h. subst R'. clear h.
        unfold poly_rat in H1.
        case_eq (map_rev (color_interpret arity) is); intros l H4;
        rewrite H4 in H1; try discr.
        (* check conditions for poly rat terminates *)
        case_eq (conditions_poly_rat l); intro H5; rewrite H5 in H1;
        try discr.
        inversion H1. clear H1.
        unfold conditions_poly_rat in H5.
        set (trsInt:=fun f : symbol => fun_of_pairs_list arity f l).
        cut (forall f: Sig, pweak_monotone (trsInt f)).
        intro trsInt_wm.
        rewrite andb_eq in H5. destruct H5.
        (** REMARK: PolyInt for type rational need different WPQ *)
        apply WF_rp_red with (WP:=@WP_Q _ _ l H del).       
        (** A proof of [>] are closed by context: IR_context_closed. *)
        change (context_closed (IR (@I Sig _ (TPolyInt_poly arity l H)) succ)).
        apply IR_context_closed. apply pi_monotone.
        simpl. intro f.
        (** Polynomial is strong monotone. *)
        apply trsInt_pw_poly. rewrite andb_eq. split. hyp. hyp.
        (** Check that all rules [R] are included in [>=]. *)
        simpl; unfold brule, bsucceq, bool_of_rel; simpl.
        rewrite forallb_forall. intros x Hx. subst bge.
        rewrite forallb_forall in H3. ded (H3 x Hx). destruct x as [t u].
        simpl in *.
        case_eq (succeq'_dec Sig (TPolyInt_poly arity l H) t u);
          intros s Hs. auto.
        unfold brule in H0. unfold succeq' in s.
        unfold redpair_poly_rat_ge in H0.
        rewrite bcoef_not_neg_ok in H0. contradiction.
        (** Remove all rules [R] are included in [>]. *)       
        apply WF_incl with (S:=red (filter (brule (neg bgt))R)).
        unfold inclusion. intros t u H7. redtac. unfold red.
        exists l0. exists r. exists c. exists s. intuition.
        apply filter_In. apply filter_In in lr. intuition.
        unfold brule, neg. unfold brule, neg in H6. simpl in *.
        unfold bsucc, bool_of_rel in H6. simpl in *.
        destruct succQ'_dec in H6. discr.
        unfold succQ' in n0. rewrite <- bcoef_not_neg_ok in n0.
        apply eq_true_not_negb in n0.
        subst bgt. apply n0. hyp.
        (** Proving polynomial is weak monotone. *)
        intro f. apply trsInt_wm_poly.
        rewrite andb_eq in H5. destruct H5. hyp.
      Qed.
    
      (************************************************************************)
      (** 1.b. Correctness proof of polynomial interpretation over
      domain rational numbers. *)

      Lemma poly_rat_ok : forall n (R R': arules) is
      (h: match type_poly_rationals n is with
            | Ok (bge, bgt) =>
              if   ge_R R bge
              then gt_R R bgt
              else Ko _ (Fail FRuleNotInLargeOrdering_poly)
            | Ko e => Ko _ e
          end = Ok R') (wf: WF (red R')), WF (red R).
    
      Proof.
        intros n0 R R' is h wf.
        unfold type_poly_rationals in h.
        destruct n0; simpl in h; try discr.
        (* Coefficient of type integer *)
        set (del := inject_Z i). fold del in h.
        apply poly_rat_comm_ok with (R':=R')(del:=del)(is:=is).
        hyp. hyp.
        (* Coefficient of type natural numbers. *)
        set (t := (Qmake i p)). fold t in h.
        apply poly_rat_comm_ok with (R':=R')(del:=t)(is:=is).
        hyp. hyp.
      Qed.

      Close Scope Q_scope.
      
      (************************************************************************)
      (** Define function for polynomial call to the polynomial
       interpretation over domain natural numbers and rational
       numbers. *)
    
      Definition type_polynomial is dom :=
        match dom with
          | Domain_naturals               => poly_nat is
          | Domain_integers               =>
            Ko _ (Todo Ttype_polynomialDomain_integers)
          | Domain_rationals del          => type_poly_rationals del is
          | Domain_arctic dom'            =>
            Ko _ (Todo Ttype_polynomialDomain_arctic)
          | Domain_tropical dom'          =>
            Ko _ (Todo Ttype_polynomialDomain_tropical)
          | Domain_matrices dim sdim dom' =>
            Ko _ (Todo Ttype_polynomialDomain_matrices)
        end.

      (************************************************************************)

      Lemma type_polynomial_ok : forall R bge bgt is d, 
       type_polynomial is d = Ok (bge, bgt) ->
       forallb (brule bge) R = true ->
       WF (red ( (filter (brule (neg bgt)) R))) -> WF (red R).

      Proof.
        intros. unfold type_polynomial in H. destruct d; try discr.
        eapply poly_nat_ok. apply H. apply H0. apply H1.
        (* domain rational *)
              
      Admitted.

      (** Termination by using compatible reduction orderings.
       Condition for check the termination by rule elimination with reduction
       pairs [ARedPair.v] Lemma [WF_rp_red].
       
       Manna-Ness theorem: given a pairs of relations ([>], [>=]) closed by
       substitution such that [>] is well-founded, the orders are
       compatible, i.e., [> - >= \in >] or [>= - > \in >], and
       [>=](resp. [>]) are closed by context. If all rules [R] are included
       in [>=] then all rules are included in [>] can be removed. 

      Remark: this function use for both natural and rational numbers. *)

      Definition polynomial_interpretation (R: arules) is dom : result arules :=
        match type_polynomial is dom with
          | Ok (bge, bgt) =>
            if   ge_R R bge
            then gt_R R bgt
            else Ko _ (Fail FRuleNotInLargeOrdering_poly)
          | Ko e => Ko _ e
      end.
      
      (************************************************************************)

      Lemma polynomial_interpretation_ok : forall (R R': arules)
        is d,
        polynomial_interpretation R is d = Ok R' -> WF (red R') -> WF (red R).
        
        Proof.
          intros. unfold polynomial_interpretation in H.
          case_eq (type_polynomial is d); intros p H1; rewrite H1 in H.
          destruct p as [bge bgt].
          case_eq (ge_R R bge); intros H2; rewrite H2 in H.
          apply type_polynomial_ok with (bge:= bge)(bgt:= bgt)(is:=is)(d:=d).
          apply H1. unfold ge_R in H2. apply H2.
          unfold gt_R in H. inversion H. subst R'. apply H0.
          try discr. try discr.
        Qed.

      (************************************************************************)
      (** ** Matrix interpretation on N. *)
      (************************************************************************)

      (** Matrix interpretation over domain natural numbers: given a
       pairs of relations ([>], [>=]), such that [>] is well-founded,
       the orders are compatible.

       - For the interpretation [f] of a symbol [f \in Signature] of
       arity [n>=1] we choose [n] matrices [M1, M2,..., Mn] over [N],
       each of size [dxd], such that the upper left elements [Mi(1,1)]
       are positive for all [i=1,2,...,n] and a vector [c \in N^d].
       
       - Check that [f] is monotone with respect to [>=], because of
       positiveness of the upper left matrix elements. We also have [f] is
       monotone with respect to [>]. So, by choosing all [f] of this shape,
       all requirements of an extended monotone algebra are fulfilled.
       
       - [get_elem m dim_pos dim_pos] : get the element at the upper left (i =
       0, j = 0) [M(0,0)], index matrix rows and columns starting from [0].
       The relation [gt : fun n m, m < n]. Where [dim_pos : dim > 0]. 
    
       Matrix orders, we define orders [ge(>=)] and [gt(>)] on [A =
       N^d] as follows: [(u1, ..., ud) >= (v1, ..., vd) <=> \forall i,
       ui >=_Nat vi (mint_ge) (u1, ..., ud) > (v1, ..., ud) <=> (u1,
       ..., ud) >= (v1, ..., vd) /\ u1 >_Nat v1 (mint_gt)]
       
       where [>=_Nat] and [>_Nat]: are orders over natural numbers. *)

      Require Import AMatrixBasedInt2 Matrix2 OrdSemiRing2 AMatrixInt2
              Nat_as_OSR.
      
      Open Scope nat_scope.
    
      (**********************************************************************)

      Section weakRedPair_matrix_nat.

        (* Define coefficient of type natural over semi-ring structure. *)
        
        Global Instance coef_sring_N: CPFSRing.

        Proof. 
          apply Build_CPFSRing with (OSR := Nat_as_OSR).
          apply color_coef_N.
        Defined.

        (* Declare dimension as a variable to be able to use it in the
          matrix_nat function. *)
      
        Variable dim : nat.
        Notation dim_pos := (dim_pos dim).
        Notation mint := (@matrixInt _ dim).
      
        Variable l: list {g: symbol & mint (arity g)}.
      
        (* Build the monotone algebra for matrix interpretation on N. *)
        Definition TMatrix_Mon_Nat    := @MonotoneAlgebra Sig dim
                                      (@TMatrix_Int arity dim coef_sring_N l).
        (* Build the weak reduction pair for matrix interpretation on N. *)
        Definition WP_Matrix_Nat      := @WP_MonAlg Sig TMatrix_Mon_Nat.
        (* Build matrix method conf for matrix interpretation on N. *)
        Definition TMatrix_Conf       := @Conf Sig dim (@TMatrix_Int _ _ _ l).
      
        (** Proving monotone interpretation of trsInt_matrix of type nat. *)
          
        Variable H: forallb  (fun x : {f : symbol & mint (arity f)} =>
                  let (f, mi) := x in
                  bVforall (fun m : matrix dim dim =>
                  bgt Nat_as_OSR (get_elem m dim_pos dim_pos) 0)
                  (args mi)) l = true.

        Lemma trsInt_nat_default_mon: forall f, 
          monotone_interpretation (default_matrix dim (arity f)).
          
        Proof.
          intros. unfold default_matrix. unfold monotone_interpretation.
          apply Vforall_intro; simpl in *.
          intros. unfold id_matrix in H0. unfold VecArith2.id_vec in H0.
        Admitted.

        (*Parameter trsInt_nat_default_mon: forall f, 
        monotone_interpretation (default_matrix dim (arity f)).*)

        (* Proving that matrix is a monotone interpretations. *)
        Lemma trsInt_nat_mon: forall f,
        monotone_interpretation (@trsInt_matrix _ _ _ l f).
      
        Proof.
          intro f. unfold trsInt_matrix. unfold fun_of_pairs_list_matrix. 
          induction l; simpl in *; try discr.  
          (* Default matrix monotone *)
          apply trsInt_nat_default_mon.
          simpl in *.
          destruct a as [g]; try discr.
          destruct (@eq_symb_dec Sig g f).
          (* g = f *)
          unfold matrix_cast. Equality.simpl_eq.
          rewrite andb_eq in H. destruct H.
          rewrite <- bmonotone_interpretation_ok.
          unfold bmonotone_interpretation. hyp.
          (* g <> f *)
          apply IHl0.
          rewrite andb_eq in H.
          destruct H. hyp.
        Qed.
      
      End weakRedPair_matrix_nat.

      Import OSR_Notations.

      (** Conditions for matrix interpretation over natural numbers is
      monotone:
       - Fix a dimension [d].
       – For every symbol [f] \in Signature choose matrices [Mi \in
       N(dxd)] for [i = 1, 2,...,n] for [n] being the arity of [f] ,
       such that the upper left elements [(Mi)1,1] are positive for
       all [i = 1, 2,.., n], and a vector [c\in N^d].
       – For every rule [l \rightarrow r \in R union S], we check
       whether [[Mi] \rightarrow [Ri] for [i = 1,.., k]] and [vector l >=
       vector r] for the corresponding matrices Mi, Ri and vectors [l, r]
       as defined above.
       – If this does not hold, the method fails.
       – If this holds, then we remove all rules from [R] and [S]
       moreover satisfying [l1 > r1].
       – If the remaining [R] is empty, we are finished; otherwise we
       repeat the process for the reduced TRSs [R, S] or apply any
       other technique for proving (relative) termination.
       REMARK: use relation [bgt].  *)

      Definition condition_matrix_nat dim
      (l: list ({f: symbol & matrixInt dim (arity f)})) :=
        (* check that the upper left of matrix Mi[1,1] > 0 *)
       forallb (fun x => match x with
         existT f mi   => bVforall (fun m =>
           bgt Nat_as_OSR (get_elem m (dim_pos dim) (dim_pos dim)) 0)(args mi)
             end) l.

      (* >=, bmint_ge: is a boolean function of mint_ge
         (comparation of odering greater than equal between two matrices.
      where [rule_mi is a pair of term interpretation (lhs, rhs)]*)

      Definition redpair_matrix_nat_ge t u dim Conf :=
        let (l, r) := @rule_mi Nat_as_OSR Sig dim Conf (mkRule t u) in
        bmint_ge l r.
      
      (* >, bmint_gt_nat: is a boolean function of mint_gt on
         natural numbers (ordering greater between two matrices. *)

      Definition redpair_matrix_nat_gt t u dim Conf :=
        let (l, r) := @rule_mi Nat_as_OSR Sig dim Conf (mkRule t u) in
        bmint_gt_nat l r.

      Definition matrix_nat (is: list (symbol * cpf.arity * function))
      (dim: nat): result ((aterm -> aterm -> bool) * (aterm -> aterm -> bool))
      :=
      (* check that interprets can be translated into matrix interpretations. *)
      Match map_rev (@color_interpret_matrix arity dim coef_sring_N) is With l
        ===> if condition_matrix_nat l
             then let Conf := TMatrix_Conf l in
             (* if yes: return a reduction pair (>=, >). *)
             Ok (fun t u => redpair_matrix_nat_ge t u Conf,
                 fun t u => redpair_matrix_nat_gt t u  Conf)
             (* if no: return error message. *)
             else Ko _ (Fail FNotMonotone_matrix_naturals).

      (** NOTE: [Domain_naturals] that if the domain is "matrices of
       naturals" then everything has to be a matrix, even the
       constants. This is in contrast to "matrixInterpretations" where the
       constants are vectors.
       
       [Domain_matrices]: the domain of matrices where the elements are
       from the subdomain specified. *)
      
      (* TODO: domain rational for matrix ?? *)

      Definition type_matrix is dom dim :=
        match dom with
          | Domain_naturals               => matrix_nat is dim
          | Domain_integers               =>
            Ko _ (Todo Ttype_polynomialDomain_integers)
          | Domain_rationals delta        =>
            Ko _ (Todo Ttype_polynomialDomain_rationals)
          | Domain_arctic dom'            =>
            Ko _ (Todo Ttype_polynomialDomain_arctic)
          | Domain_tropical dom'          =>
            Ko _ (Todo Ttype_polynomialDomain_tropical)
          | Domain_matrices dim sdim dom' =>
            Ko _ (Todo Ttype_polynomialDomain_matrices)
        end.
      
      Definition matrix_interpretation (R: arules) is dom dim: result arules :=
        match type_matrix is dom dim with
          | Ok (bge, bgt) =>
            if   ge_R R bge
            then gt_R R bgt
            else Ko _ (Fail FRuleNotInLargeOrdering_matrix_naturals)
          | Ko e => Ko _ e
      end.
      
      Require Import AMatrixBasedInt2 AMonAlg2.
      
      (***********************************************************************)
      (** 2.a. Correctness Proof of matrix interpretation of domain
      natural numbers. *)

      Lemma matrix_interpretation_ok : forall (R R': arules) is d
      (h: matrix_interpretation R is Domain_naturals (Pos.to_nat d) = Ok R')
      (wf: WF(red R')), WF (red R).

      Proof.
        intros R R' is d h wf.
        unfold matrix_interpretation in h.
        destruct Domain_naturals; simpl in h; try discr.
        case_eq (matrix_nat is (Pos.to_nat d));
          intros p H; rewrite H in h; try discr.
        destruct p as [bge bgt].
        (* check >= in R *)
        case_eq (ge_R R bge); intro H0;
        rewrite H0 in h; try discr.
        unfold gt_R in h. unfold ge_R in H0.
        inversion h. subst R'. clear h.
        unfold matrix_nat in H. revert H.
        case (map_rev (color_interpret_matrix arity (Pos.to_nat d)) is);
          intros l H1; try discr.
        (* check condition of matrix nat terminate *)
        case_eq (condition_matrix_nat l); intro H2; rewrite H2 in H1;
        try discr.
        inversion H1. clear H1.
        unfold condition_matrix_nat in H2.
        (** Proving [WF(red R)]. *)
        apply WF_rp_red with (WP:=@WP_Matrix_Nat _ l). 
        (** A proof of [>] are closed by context: IR_context_closed. *)
        change (context_closed (IR 
               (@AMatrixBasedInt2.I _ Sig _ _
               (@mi_eval_ok _ _ (@TMatrix_Int _ _ _ l)))
               (@AMatrixInt2.succ _ _ (@TMatrix_Int _ _ _ l)))).
        apply IR_context_closed. apply monotone_succ. simpl. intro f.
        apply trsInt_nat_mon. hyp.       
        (** Check that rules [R] is included in [>=]. *)
        simpl; unfold brule, bsucceq, bool_of_rel; simpl.
        rewrite forallb_forall. intros x Hx. subst bge.
        rewrite forallb_forall in H0. ded (H0 x Hx).
        unfold redpair_matrix_nat_ge in H.
        destruct x as [t u]. simpl in *.
        destruct (succeq'_dec t u); intros; try discr; auto.
        unfold brule in H.
        unfold term_ge, term_ord, mint_ge in n0.
        eapply bmint_ge_ok in H. simpl in *.
        unfold mint_ge in H. simpl in *. try contradiction.       
        (** Remove all rules [>] in [R]. *)
        apply WF_incl with (S := red (filter (brule (neg bgt)) R)).
        unfold inclusion. intros t u H7. redtac. unfold red.
        exists l0. exists r. exists c. exists s. intuition.
        apply filter_In. apply filter_In in lr. intuition.
        unfold brule, neg. unfold brule, neg in H1. simpl in *.
        unfold bsucc, bool_of_rel in H1.
        destruct ma_succ'_dec in H1; try discr.
        simpl in *.
        unfold AMatrixInt2.term_gt, term_gt, term_ord in n0; simpl in *;
        auto. unfold mint_gt in n0.
        rewrite <- bmint_gt_ok in n0. apply eq_true_not_negb in n0.
        subst bgt. apply n0. hyp.
      Qed.
      
      Close Scope nat_scope.

      (** [type_matrixInterpertation] type for matrix interpretation
         with different domain natural number. Where the elements are
         vectors.
         Example: if the domain is naturals, then the
         coefficients in front of variables have to be matrices and
         the constants should be vectors over the naturals. *)
    
      Definition type_matrix_interpretation (R: arules) is dom dim :=
        match dom with
          | Domain_naturals => matrix_interpretation R is dom (nat_of_P dim)
          | Domain_integers =>
            Ko _ (Todo Ttype_polynomialDomain_integers)
          | Domain_rationals delta =>
            Ko _ (Todo Ttype_polynomialDomain_rationals)
          | Domain_tropical _ =>
            Ko _ (Todo Ttype_polynomialDomain_tropical)
          (*matrix_int_tropical R is dom (nat_of_P dim)*)
          | Domain_arctic dom' =>
            Ko _ (Todo Ttype_polynomialDomain_arctic)
          | Domain_matrices dim sdim dom' =>
            Ko _ (Todo Ttype_polynomialDomain_matrices)
        end.
    
      (***********************************************************************)
      (** ** Reduction pair interpretation with polynomial and matrix
             interpretation in domain: natural numbers and rational numbers. *)
      (***********************************************************************)
    
      Definition redPair_interpretation (R: arules) (t: type_t9) 
        (is: list (symbol * cpf.arity * function)): result arules :=
        match t with
          | Type_t9_polynomial dom degmax =>
            polynomial_interpretation R is dom
          | Type_t9_matrixInterpretation dom dim sdim =>
            type_matrix_interpretation R is dom dim
        end.
    
      (***********************************************************************)
      (** Correctness proof of redPair interpretation.
      Proof structure:
       1. Correctness proof of polynomial interpretation.
          a. Domain natural numbers.
          b. Domain rational numbers
            - Coefficients are of domain integer.
            - Coefficients are of domain rationals
       2. Correctness proof of matrix interpretation.
          a. Domain natural numbers.
          b. Domain tropical numbers (TODO). *)

      Lemma redPair_interpretation_ok : forall (R R': arules) t is,
        redPair_interpretation R t is = Ok R' -> WF (red R') -> WF (red R).

      Proof.
        intros R R' t is h wf.
        destruct t as [d | de]; simpl in h; try discr.
        apply polynomial_interpretation_ok in h.
        apply h. apply is. apply wf.

        (** TODO: 1.b. Correctness proof of polynomial of domain rational
            numbers. *)
        (*eapply poly_rat_ok. apply h. apply wf.*)
        (** 2.a. Correctness proof of matrix interpretation. *)
        unfold type_matrix_interpretation in h.
        destruct de; try discr.
        (* Correctness proof of matrix int of domain natural numbers. *)
        eapply matrix_interpretation_ok. apply h. apply wf.
        (* TODO *)
        (* Correctness proof of matrix int of domain tropical
           numbers. *)
        (*eapply matrix_interpretation_tropical_ok. apply h. apply wf.*)
      Qed.

    End Full_Termin.
    
    (***********************************************************************)
    (** ** Recursive path ordering (RPO) *)
    (***********************************************************************)

    (** It is an ordering introduced by Dershowitz.

     It extends a well-founded order on the signature, called a
     precedence, to a reduction order on terms. We used the
     Coccinelle's library.

     REMARK: do not define notation for [Sig] to be able to use
     [filter_arity] in [AFilterPerm.filter] later. *)

    Require Import rpo2 ordered_set rpo_extension Coccinelle2.

    (* Condition for RPO:
       - check that the status and its precedence are compatible.
       For example:
       prec(plus)  = 2;  status = Lex
       prec(minus) = 2;  status = Mul.
       This is imcompatible. For they have different status. *)

    Definition condition_rpo l :=
      let fs := split_list l in
      forallb (fun f => forallb (fun g =>
        @cpf2color.bprec_eq_status_symb arity l f g) fs) fs.

    (* Translate RPO term *)

    Definition pathOrder_term l :=
      let prec := Precendence_Imp arity l rpo_arg in
      if condition_rpo l
      then Ok (fun t u => @bsucceq rpo_arg (Sig arity) prec t u,
               fun t u => @bsucc rpo_arg (Sig arity) prec t u)
      else Ko _ (Fail FNotpathOrder_term).

    (************************************************************************)
    (** Correctness proof of RPO *)

    Lemma rpo_without_af_ok : forall (R R': arules) l
      (h: match pathOrder_term l  with
            | Ok (bge, bgt) =>
              if   ge_R R bge
              then gt_R R bgt
              else Ko _ (Fail FNotpathOrder_rpo)
            | Ko e => Ko _ e
          end = Ok R') (wf: WF (red R')), WF (red R).

    Proof.
      intros R R' l h wf.
      case_eq (pathOrder_term l);
        intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt]; try discr.
      case_eq (ge_R R bge); intro H1; rewrite H1 in h;
      try discr. unfold gt_R in h. unfold ge_R in H1.
      inversion h. subst R'. clear h.
      unfold pathOrder_term in H. 
      (* check rpo condition to terminate *)
      case_eq (condition_rpo l); intro H2; rewrite H2 in H;
      try discr. inversion H. clear H.
      (* using the reduction pair method *)
      apply WF_rp_red with (WP:= @WP_RPO rpo_arg (Sig arity)
                           (Precendence_Imp arity l rpo_arg)).
      (** A proof of [>] are closed by context. *)
      apply cc_succ.
      (** Check that all rules [R] are included in [>=] *)       
      simpl; unfold brule, bsucceq.
      rewrite forallb_forall.
      intros x Hx. subst bge. unfold bsucceq in H1.
      rewrite forallb_forall in H1.
      ded (H1 x Hx). destruct x as [t u]. simpl in *.
      unfold brule in H. hyp.
      (** Remove all rules [R] are included in [>]. *)      
      apply WF_incl with (S:= red (List.filter (brule (neg bgt))R)).
      unfold inclusion. intros u v H5. redtac.
      unfold red. exists l0. exists r. exists c. exists s.
      intuition. apply filter_In. apply filter_In in lr.
      intuition. unfold brule, neg. unfold brule, neg in H0. simpl in *.
      unfold bsucc in H0. simpl in *. subst bgt. hyp. hyp.
    Qed.

    (***********************************************************************)
    (** ** RPO with argument filtering AF. *)
    (***********************************************************************)

    (** Collapsing/non-collapsing:
       - Non-collapsing: an argument filtering is non-collapsing if, for every
       symbol f of arity n, pi(f) is a list of positions.
       - Collpasing: if for every symbol f of arity n, either
       pi(f)=[1, ..., n] or pi(f) \in [1,n].
       - Every argument filtering can be defined as the composition of one
       collpasing and one non-collapsing AF.
       - The weak reduction pair associated to a non-collpasing AF is defined in
       ARedPair2.v (class Perm), and collapsing with class (Proj). *)

    Require Import AFilterPerm AProj List ListRepeatFree.

    Open Scope nat_scope.

    Require Import List.

    (** Conditions of RPO + AF:
       - check the status of RPO.
       - check there is no duplication argument in PI (collapsing case).*)

    Definition conditions_rpo_filter l args :=
      let ls := List.map (pi_filter arity) args in
      condition_rpo l &&
      forallb
     (fun x : {f : symbol & nat_lts (arity f)} =>
      let (f, p) := x in brepeat_free beq_nat (map (val (n:=arity f)) p)) ls.

    (** The signature is changed in the case of filtering (collapsing).
       This is embedded in the compute of [filter_sig] in CoLoR. *)

    Definition sig args :=
      Sig (@ASignature.arity (Sig (filter_arity (Sig arity)
        (@color_pi_filter arity args)))).

    (* translate term: RPO + AF (collapsing and non-collapsing). *)

    Definition rpo_term t args :=
      let l := List.map (@pi_filter arity) args in
      @term_of_aterm (sig l) (color_proj args
     (@color_filter arity l t)).

    (* >= *)

    Definition rpo_proj_filter_redpair_ge args l t u :=
      match cpf2color.rpo_eval l rpo_arg
           (rpo_term t args) (rpo_term u args) with
        | Some Equivalent | Some Greater_than => true
        | _ => false
      end.

    (* > *)
    Definition rpo_proj_filter_redpair_gt args l t u :=
      match cpf2color.rpo_eval l rpo_arg
            (rpo_term t args) (rpo_term u args) with
        | Some Greater_than => true
        | _ => false
      end.

    (* return a pair (>=, >) *)

    Definition pathOrder_rpo_proj_filter
      (l: list (symbol * cpf.arity * nonNegativeInteger * t10))
      (args : list (symbol * cpf.arity * t11)) : error_monad.result
      ((aterm -> aterm -> bool) * (aterm -> aterm -> bool)) :=
      if   conditions_rpo_filter l args
      then Ok (fun t u => rpo_proj_filter_redpair_ge args l t u,
               fun t u => rpo_proj_filter_redpair_gt args l t u)
      else Ko _ (Fail FPrecedence_incompatible_statuses).

    Require Import List.

    (* every argument filtering can be defined as the composition
       of one collapsing and one non-collapsing argument filtering. *)

    Definition pathOrder_term_rpo_af
      (l: list (symbol * cpf.arity * nonNegativeInteger * t10))
      (args : list (symbol * cpf.arity * t11)) : error_monad.result
      ((aterm -> aterm -> bool) * (aterm -> aterm -> bool)) :=
       match args with
        | (_, _, t) :: _ =>
          if is_proj_filter t (* CHECK *)
          then Match pathOrder_rpo_proj_filter l args With
                     rpo_proj_filter ===> Ok rpo_proj_filter
          else Ko _ (Fail Frpo_af)
        | nil => Ko _ (Fail Frpo_af_nil)
      end.

    (***********************************************************************)
    (** Correctness proof of RPO with AF *)

    Lemma rpo_with_af_ok : forall (R R': arules) args l
     (h: match pathOrder_term_rpo_af l args with
           | Ok (bge, bgt) =>
             if   ge_R R bge
             then gt_R R bgt
             else Ko _ (Fail FNotpathOrder_with_af)
           | Ko m => Ko _ m
         end = Ok R') (wf: WF (red R')), WF (red R).
    
    Proof.
      intros R R' args l h wf.
      case_eq (pathOrder_term_rpo_af l args);
        intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt]; try discr.
      case_eq (ge_R R bge); intro H1; rewrite H1 in h;
      try discr. unfold gt_R in h. unfold ge_R in H1.
      inversion h. subst R'. clear h.
      unfold pathOrder_term_rpo_af in H.
      destruct args; try discr. 
      destruct p; try discr.
      destruct p; try discr.
      (*1. collapsing + non-collapsing *)
      case_eq (is_proj_filter t); intro H2; rewrite H2 in H; try discr.
      set (args' := (s, a, t) :: args). fold args' in H.
      (* unfold term with filter and projection embeded inside rpo *)
      case_eq (pathOrder_rpo_proj_filter l args'); intros p H3;
      rewrite H3 in H; try discr.
      (* unfold term, and separate the reduction pair *)
      unfold pathOrder_rpo_proj_filter in H3.
      set (ls := map (pi_filter arity) args').
      fold ls in H3.
      (* check the condition for rpo_filter *)
      case_eq (conditions_rpo_filter l args'); intros H0; rewrite H0 in H3;
      try discr. inversion H3. clear H3.
      subst p. inversion H. clear H.
      (* Proof the WF (red R) by using the reduction pair processor *)
      apply WF_rp_red with (WP :=
        (* WP_Perm : Sig -> Perm Sig -> DS_WeakRedPair (perm_Sig (Sig := Sig))
          -> DS_WeakRedPair Sig *)
        @WP_Perm (Sig arity) (Perm_Imp arity ls)
        (* WP_Proj: Sig -> Proj Sig -> DS_WeakRedPair Sig ->
           DS_WeakRedPair Sig *)
        (@WP_Proj (Sig (@ASignature.arity (color_perm_Sig arity _)))
        (* Proj_Imp : arity -> args -> Proj (Sig arity) *) 
        (@Proj_Imp (@ASignature.arity (color_perm_Sig arity _)) args')
        (* WP_RPO : nat -> Sig -> Pre Sig -> DS_WeakRedPair Sig *)   
        (@WP_RPO rpo_arg (Sig (@ASignature.arity (color_perm_Sig arity _)))
        (* Precendence_Imp : arity -> args -> nat -> Pre (Sig arity) *)
        (Precendence_Imp (@ASignature.arity (color_perm_Sig arity ls))
        l rpo_arg)))).

      (** Proof the context closure of relation [>] *)

      Focus 2.

      (** Check that all rules [R] are included in [>=],
         where [pbsucceq] is a [succeq] of filtering defined in ARedPair2.v *)

      simpl; unfold brule, pbsucceq.
      rewrite forallb_forall. intros x Hx.
      (* unfold relation [>=] in hypothesis *)
      unfold rpo_proj_filter_redpair_ge in H4.
      subst bge. rewrite forallb_forall in H1.
      ded (H1 x Hx). destruct x as [u v].
      simpl in *.
      (* unfold all definitions in hypothesis *)
      unfold brule, rpo_term, color_proj, color_filter in H.
      (* solve the sub-goal by the hypothesis *)
      apply H.

      (** Remove all rules [R] are included in [>]. *)     

      Focus 2.
      apply WF_incl with (S := red (List.filter (brule (neg bgt)) R)).
      unfold inclusion. intros u v H6. redtac.
      unfold red.
      exists l0. exists r. exists c. exists s0.
      intuition.
      (* apply filter_In *)
      apply filter_In. apply filter_In in lr. intuition.
      (* unfold all definitions *)
      unfold brule, neg. unfold brule, neg in H3.
      simpl in *. subst bgt. hyp. hyp.
      
      (** Proof the context closure of relation [>].
          where [psucc] is a definition of relation [>] of filtering
          defined in ARedPair2.v  *)

      unfold ds_weak_rp. simpl in *.
      (* apply the lemma in filtering using strong monotony wrt context,
         need to proof two subgoals:
         - there is no argument duplication in pi
         - all filterings are permutations *)

      apply filter_strong_cont_closed.

      (* there is no argument duplcation *)

      unfold conditions_rpo_filter in H0.
      rewrite andb_eq in H0. destruct H0.
      unfold non_dup.
      apply pi_filter_non_dup. unfold condition_rpo in H.
      apply H0.

      (* all filtering are permutations. *)

      unfold permut. apply pi_filter_permut.

      (* Then proof context closure in collapsing case,
         where [pr_succ] is the definition of relation [>] in projection. *)

      simpl in *.

      (* apply the lemma proof stability wrt contexts in AProj.v in CoLor.
         need to proof two subgoals: where [succ] is a relation defined in
         MonAlg in ARedPair2.v
         - reflexivity of relation [succ],
         - context closure of [succ] of rpo *)

      apply proj_cont_closed.

      (* Proof the second sub-goal by using the lemma in RPO *)

      Focus 2. apply cc_succ.

      (* The first sub-goal TODO *)

      simpl in *. (* reflexivity of relation [>] in rpo *)

     (* TODO: there is no theory/lemma able to proof this.*)

      unfold succ.

   Admitted.

    (***********************************************************************)
    
    (* Define a function RPO + AF *)
    Definition rpo_af R sp af :=
      match pathOrder_term_rpo_af sp af with
        | Ok (bge, bgt) =>
          if   ge_R R bge
          then gt_R R bgt
          else Ko _ (Fail FNotpathOrder_with_af)
        | Ko e => Ko _ e
      end.
    
    (* Define a function only using RPO *)
    Definition path_rpo_term R sp :=
      match pathOrder_term sp with
        | Ok (bge, bgt) =>
          if   ge_R R bge
          then gt_R R bgt
          else Ko _ (Fail FNotpathOrder_rpo)
        | Ko e => Ko _ e
      end.

    Definition pathOrder (R: arules) sp (af: option argumentFilter):
      error_monad.result arules :=
      match af with
        | Some af => rpo_af R sp af (* Combination with argument filter *)
        | None    => path_rpo_term R sp (* Without argument filter *)
      end.

    (***********************************************************************)
    (** Correctness proof of RPO *)

    Lemma pathOrdering_ok : forall (R R': arules) l o,
     pathOrder R l o = Ok R' -> WF (red R') -> WF (red R).
      
    Proof.
      intros R R' l o h wf.
      unfold pathOrder in h.
      destruct o; try discr.
      (** RPO with argument filtering method. *)
      apply rpo_with_af_ok with (R':=R')(args:=a)(l:=l).
        apply h. apply wf.
      (** RPO without argument filtering method. *)
      apply rpo_without_af_ok with (R':=R')(l:=l).
      hyp. hyp.
    Qed.

    (***********************************************************************)
    (** Ordering constrainst proof with reduction pair interpretation.
     REMARK: the patten condition that is in comment belongt to the
     case when using CPF version 2.1x. *)
    (***********************************************************************)

    Definition redPair (R:arules) (rp: redPair) : error_monad.result arules :=
      match rp with
        | RedPair_interpretation t is    => redPair_interpretation R t is
        | RedPair_pathOrder sp oaf       => pathOrder R sp oaf
        | RedPair_knuthBendixOrder _ _ _ =>
          Ko _ (Todo TRedPair_knuthBendixOrder)
        | RedPair_scnp _ _ _             =>
          Ko _ (Todo TRedPair_scnp)
      end.

    Definition ruleRemoval (R: arules) ocp :=
      match ocp with
        | OrderingConstraintProof_redPair rp              => redPair R rp
        | OrderingConstraintProof_satisfiableAssumption _ =>
          Ko _ (Todo TOrderingConstraintProof_satisfiableAssumption)
      end.

  End S.

  (*************************************************************************)
  (** ** Check that [p] is a valid termination proof for [hd_red_mod R D]. *)
  (*************************************************************************)

  Require Import APolyInt2 ARedPair2.
  
  Section Top_Termination.   
      
    Import OR_Notations error_monad.
      
    Open Scope Z_scope.

    (*************************************************************************)
    (** ** Polynomial intepretation with DP on N. *)
    (*************************************************************************)

    (* >= *)
    Definition redpair_poly_nat_dp_ge a t u pi :=
      bcoef_not_neg (@rulePoly_ge Z_as_OR (Sig a) pi (mkRule t u)).

    (* > *)
    Definition redpair_poly_nat_dp_gt a t u pi :=
      bcoef_not_neg (@rulePoly_gt Z_as_OR (Sig a) pi (mkRule t u)).

    (* Conditions of PI with DP on N only require: 
       -  check that the polynomial has non-negative coefficients. *)

    Definition poly_nat_dp a (is: list (symbol * cpf.arity * function)) :
      result ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)) :=
      (* check that interprets can be translated into polynomial *)
      Match map_rev (@color_interpret a coef_ring_Z) is With l ===>
      if forallb (fun x =>  match x with
           existT f p  => bcoef_not_neg p end) l
      then (* build polynomial interpretations *)
      let pi := fun f : Sig a => fun_of_pairs_list a f l in
        Ok (fun t u => redpair_poly_nat_dp_ge t u pi,
          fun t u => redpair_poly_nat_dp_gt t u pi)
      else Ko _ (Fail FNotMonotone_dp).

    (***********************************************************************)
    (** Correctness proof of polynomial interpretations on DP on N. 
       return a success reduction pair (>=, >) boolean functions.
       it requires both D R rules are in >=,
       if yes, then remove all > on D,
       otherwise, return error message *)

    (* Define a function check >= on D and R *)

    Definition ge_R_D a (R D : arules a) bge :=
      forallb (brule bge) D && forallb (brule bge) R.

    (* Define a function remove > in D *)

    Definition gt_D a (D: arules a) bgt :=
      Ok (filter (brule (neg bgt)) D).

    Lemma poly_nat_dp_ok : forall a (R D D': arules a) is
      (h:  match poly_nat_dp a is with
             | Ok (bge, bgt) =>
               if   ge_R_D R D bge
               then gt_D D bgt
               else Ko _ (Fail FRuleNotInLargeOrdering_dp)
             | Ko e => Ko _ e
           end = Ok D')(wf: WF (hd_red_mod R D')), WF (hd_red_mod R D).

    Proof.
      intros a R D D' is h wf.
      case_eq (poly_nat_dp a is);
        intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt].
      case_eq (ge_R_D R D bge); intro H1; rewrite H1 in h; try discr.
      unfold gt_D in h. unfold ge_R_D in H1.
      inversion h. subst D'. clear h.
      unfold poly_nat_dp in H. revert H.
      case (map_rev (color_interpret a) is);
        intros l H; try discr. gen H.
      set (b:= forallb (fun x : {f : symbol & poly (a f)} =>
          let (f, p) := x in bcoef_not_neg p) l).
      case_eq b; intros H2 H3; subst b; try discr.
      inversion H3. clear H3.
      set (trsInt := (fun f: (Sig a) => fun_of_pairs_list a f l)).
      cut (forall f: (Sig a), pweak_monotone (trsInt f)).
      intros trsInt_wm.
      apply WF_wp_hd_red_mod with (WP :=@WP _ _ l H2).
      (** Check that all rules [R] are included in [>=]. *)
      simpl. unfold brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H1. destruct H1.
      rewrite forallb_forall in H1. ded (H1 x Hx).
      destruct x as [t u]. simpl in *.
      destruct APolyInt_MA2.succeq'_dec; auto.
      unfold redpair_poly_nat_dp_ge in H3.
      unfold abrule, brule in H3. unfold APolyInt_MA2.succeq' in n0.
      rewrite bcoef_not_neg_ok in H3. contradiction.
      (** Check that all rules [D = dp R] are included in [>=]. *)
      simpl. unfold brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H1. destruct H1.
      rewrite forallb_forall in H0. ded (H0 x Hx).
      destruct x as [t u]. simpl in *.
      destruct APolyInt_MA2.succeq'_dec; auto.
      unfold redpair_poly_nat_dp_ge in H3.
      unfold brule in H3. unfold APolyInt_MA2.succeq' in n0.
      rewrite bcoef_not_neg_ok in H3. contradiction.
      (** Remove all rules [D] that are included in [>]. *)
      apply WF_incl with (S := hd_red_mod R (filter (abrule (neg bgt)) D)).
      unfold inclusion. intros t u H3. redtac.
      unfold hd_red_mod. unfold compose.
      exists t0. split. hyp. unfold hd_red.
      exists l0. exists r. exists s. intuition.
      apply filter_In. apply filter_In in lr.
      intuition. unfold brule, neg. unfold brule, neg in H6. simpl in *.
      unfold bsucc, bool_of_rel in H6. simpl in *.
      destruct APolyInt_MA2.succ'_dec in H6. discr.
      unfold APolyInt_MA2.succ' in n0.
      rewrite <- bcoef_not_neg_ok in n0.
      apply eq_true_not_negb in n0. subst bgt.
      apply n0. hyp.
      intro f. apply trsInt_wm_poly. hyp.      
    Qed.
    
    Close Scope Z_scope.

    (*************************************************************************)
    (** ** Polynomial intepretation with DP on Q. *)
    (*************************************************************************)

    (* Formalization of DP on polynomial interpertation on domain rational 
       REMARK: rulePoly for rational number : P_x - P_y - del >= 0 *)
    
    Require Import Q_as_R QArith.
    
    Open Scope Q_scope.
    
    (* >= *)
    Definition redpair_poly_rat_dp_ge a t u pi :=
     bcoef_not_neg (@rulePoly_ge Q_as_OR (Sig a) pi (mkRule t u)).
    
    (* > *)
    Definition redpair_poly_rat_dp_gt a t u pi del :=
      bcoef_not_neg (@rulePoly_gtQ Q_as_OR (Sig a) pi del (mkRule t u)).

    Definition poly_rat_dp a (is: list (symbol * cpf.arity * function)) (del:Q):
      result ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)) :=
      (* translate interprets into polynomial *)
      Match map_rev (@color_interpret a coef_ring_Q) is With l ===>
        (* check that polynomial having coefficient are non-negative *)
        if forallb (fun x => match x with
           existT f p => bcoef_not_neg p end) l
        then (* build polynomial interpretations *)
          let pi := fun f : Sig a => fun_of_pairs_list a f l in
          (* if yes, then return the reduction pair (>=, >) *)
          Ok (fun t u => redpair_poly_rat_dp_ge t u pi,
              fun t u => redpair_poly_rat_dp_gt t u pi del)
        (* otherwiser, return an error message *)
        else Ko _ (Fail FNotMonotone_rat_dp).
    
    (***********************************************************************)

    Definition type_poly_rationals_dp a del is :=
      match del with
        | Number_integer i      => poly_rat_dp a is (inject_Z i) (* i/1 *)
        | Number_rational i pos => let q := Qmake i pos in
                                   poly_rat_dp a is q
      end.

    (***********************************************************************)
    (** Correctness proof of DP on PI of domain rational. Common proof.
        return an successful reduction pair (>=, >) boolean functions;
        requires both D R included in >=;
        if yes, then remove all the > on D;
        if not, then return an error message *)

    Lemma poly_rationals_dp_common_ok: forall a del (R D D': arules a) is
      (H: match poly_rat_dp a is del with
            | Ok (bge, bgt) =>
              if   ge_R_D R D bge
              then gt_D D bgt
              else Ko _ (Fail FRuleNotInLargeOrdering_dp)
            | Ko e => Ko _ e
          end = Ok D')(wf: WF (hd_red_mod R D')), WF (hd_red_mod R D).
    
    Proof.
      intros a del R D D' is h wf.
      case_eq (poly_rat_dp a is del);
        intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt].
      (* check >= in R and D *)
      case_eq (ge_R_D R D bge); intro H1; rewrite H1 in h; try discr.
      unfold gt_D in h. unfold ge_R_D in H1.
      inversion h. subst D'. clear h.
      unfold poly_rat_dp in H. revert H.
      case (map_rev (color_interpret a) is);
        intros l H2; try discr. gen H2.
      set (b:=  forallb (fun x : {f : symbol & poly (a f)} =>
          let (f, p) := x in bcoef_not_neg p) l).
      case_eq b; intros H3 H4; subst b; try discr.
      inversion H4. clear H4.
      set (trsInt := (fun f: (Sig a) => fun_of_pairs_list a f l)).
      cut (forall f: (Sig a), pweak_monotone (trsInt f)).
      intros trsInt_wm.
      apply WF_wp_hd_red_mod with (WP:=@WP_Q _ _ l H3 del).
      (** Check that all rules [R] are included in [>=]. *)
      simpl. unfold brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H1. destruct H1.
      rewrite forallb_forall in H0. ded (H0 x Hx).
      destruct x as [t u]. simpl in *.
      destruct APolyInt_MA2.succeq'_dec; auto.
      unfold redpair_poly_rat_dp_ge in H1.
      unfold brule in H1. unfold APolyInt_MA2.succeq' in n0.
      rewrite bcoef_not_neg_ok in H1. contradiction.
      (** Check that all rules [D = dp R] are included in [>=]. *)
      simpl. unfold brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H1. destruct H1.
      rewrite forallb_forall in H. ded (H x Hx).
      destruct x as [t u]. simpl in *.
      destruct APolyInt_MA2.succeq'_dec; auto.
      unfold redpair_poly_rat_dp_ge in H1.
      unfold brule in H1. unfold APolyInt_MA2.succeq' in n0.
      rewrite bcoef_not_neg_ok in H1. contradiction.
      (** Remove all rules [D] that are included in [>]. *)
      apply WF_incl with (S := hd_red_mod R (filter (abrule (neg bgt)) D)).
      unfold inclusion. intros t u H7. redtac.
      unfold hd_red_mod. unfold compose. exists t0.
      split. hyp. unfold hd_red. exists l0. exists r. exists s.
      intuition. apply filter_In. apply filter_In in lr.
      intuition. unfold brule, neg. unfold brule, neg in H6.
      simpl in *. unfold bsucc, bool_of_rel in H6.
      simpl in *. destruct succQ'_dec in H6.
      discr. unfold succQ' in n0.
      rewrite <- bcoef_not_neg_ok in n0.
      apply eq_true_not_negb in n0. subst bgt. apply n0.
      hyp.
      (* polynomial is weak monotone *)
      intro f. apply trsInt_wm_poly. hyp.
    Qed.

    (***********************************************************************)
    (** Correctness proof of DP on PI of domain rational.
      return a successful reduction pair (>=, >) boolean functions
      check that both rules D R included in >=;
      if yes, then remove all the order > in D;
      if not, then return an error message *)

    Lemma poly_rationals_dp_ok: forall a n (R D D': arules a) is
      (h: match type_poly_rationals_dp a n is with
            | Ok (bge, bgt) =>
              if   ge_R_D R D bge
              then gt_D D bgt
              else Ko _ (Fail FRuleNotInLargeOrdering_dp)
            | Ko e => Ko _ e
          end = Ok D')(wf : WF (hd_red_mod R D')), WF (hd_red_mod R D).
    
    Proof.
      intros a n0 R D D' is h wf.
      unfold type_poly_rationals_dp in h.
      destruct n0; simpl in h; try discr.
      (** In the case of rationals -> natural numbers, where it
       convert a natural number to rational number by divide by 1. *)
      set (del:= inject_Z i). fold del in h.
      apply poly_rationals_dp_common_ok with (is:=is)(del:=del)(D':=D').
      hyp. hyp.
      (** In the case of rationals -> rational numbers. *)
      set (t := Qmake i p). fold t in h.
      apply poly_rationals_dp_common_ok with (is:=is)(del:=t)(D':=D').
      hyp. hyp.
    Qed.    
    
    Close Scope Q_scope.

    (***********************************************************************)
    (** Define function for polynomial call to the polynomial
    interpretation over domain natural numbers and rational
    numbers. *)
    
    Definition type_polynomial_dp a is dom :=
      match dom with
        | Domain_naturals => poly_nat_dp a is
        | Domain_integers =>
          Ko _ (Todo Ttype_polynomialDomain_integers)
        | Domain_rationals del => type_poly_rationals_dp a del is
        | Domain_arctic dom' =>
          Ko _ (Todo Ttype_polynomialDomain_arctic)
        | Domain_tropical dom' =>
          Ko _ (Todo Ttype_polynomialDomain_tropical)
        | Domain_matrices dim sdim dom' =>
          Ko _ (Todo Ttype_polynomialDomain_matrices)
      end.
    
    Definition polynomial_interpretation_dp a (R D: arules a) is dom:
      result (arules a) :=
      match type_polynomial_dp a is dom with
        | Ok (bge, bgt) =>
          if   ge_R_D R D bge
          then gt_D D bgt
          else Ko _ (Fail FRuleNotInLargeOrdering_dp)
        | Ko e => Ko _ e
      end.
    
    (***********************************************************************)
    (** Correctness proof of DP on PI *)
    
    Lemma polynomial_interpretation_dp_ok: forall a (R D D': arules a) is
      (d:domain)
      (h: polynomial_interpretation_dp R D is d = Ok D')
      (wf : WF (hd_red_mod R D')), WF (hd_red_mod R D).

    Proof.
      intros a R D D' is d h wf.
      unfold polynomial_interpretation_dp in h.
      destruct d; simpl in h; try discr.
      (** Polynomial interpretation over natural numbers. *)
      apply poly_nat_dp_ok with (D':=D')(is:=is).
      apply h. apply wf.
      (** Polynomial interpretation over rational numbers. *)
      apply poly_rationals_dp_ok with (n:=n0)(D':=D')(is:=is).
      apply h. apply wf.
    Qed.
  
    (*************************************************************************)
    (** ** Matrix intepretations with DP on N. *)
    (*************************************************************************)

    (* REMARK: the relation is [bge], rule_mi need to give
       the paramater of Nat_as_OSR if not COQ will not compile *)

    Import OSR_Notations.
    
    (* >= *)
    Definition redpair_mat_nat_dp_ge a t u dim Conf :=
      let (l, r) := @rule_mi _ (Sig a) dim Conf (mkRule t u)
      in bmint_ge l r.
    
    (* > *)
    Definition redpair_mat_nat_dp_gt a t u dim Conf :=
      let (l, r) := @rule_mi _ (Sig a) dim Conf (mkRule t u)
      in bmint_gt_nat l r.
    
    Definition matrix_nat_dp a (is: list (symbol * cpf.arity * function))dim:
      result ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)) :=
      (* translates an intepret into matrix interpretations *)
      let d := dim_pos dim in
      Match map_rev (@color_interpret_matrix a dim coef_sring_N) is With l ===>
       (* check that the upper left of matrices are >= 0 *)
        if forallb (fun x => match x with
           existT f mi => bVforall (fun m =>
             bge Nat_as_OSR (get_elem m d d) 0) (args mi)
               end) l
        then (* build the MatrixBasedConf *)
          let Conf := @TMatrix_Conf a dim l in
          (* return a successfull reduction pair (>=, >) *)
          Ok (fun t u => redpair_mat_nat_dp_ge t u Conf,
              fun t u => redpair_mat_nat_dp_gt t u Conf)
        (* if not, return an error message *)
        else Ko _ (Fail FNotMonotone_matrix_naturals_dp).

    (* matrix interpretation on N. *)

    Definition type_matrix_dp a is dom dim :=
      match dom with
        | Domain_naturals => matrix_nat_dp a is dim
        | Domain_integers =>
          Ko _ (Todo Ttype_polynomialDomain_integers)
        | Domain_rationals delta =>
          Ko _ (Todo Ttype_polynomialDomain_rationals)
        | Domain_arctic dom' =>
          Ko _ (Todo Ttype_polynomialDomain_arctic)
        | Domain_tropical dom' =>
          Ko _ (Todo Ttype_polynomialDomain_tropical)
        | Domain_matrices dim sdim dom' =>
          Ko _ (Todo Ttype_polynomialDomain_matrices)
      end.
    
    Definition matrix_interpretation_dp a (R D: arules a) is dom dim:
      result (arules a) :=
      match type_matrix_dp a is dom dim with
        | Ok (bge, bgt) =>
          if   ge_R_D R D bge
          then gt_D D bgt
          else Ko _ (Fail FRuleNotInLargeOrdering_matrix_nat_dp)
        | Ko e => Ko _ e
      end.

    (***********************************************************************)
    (** Correctness proof of matrix int of domain nat *)

    Require Import AMatrixInt2.

    Lemma matrix_interpretation_dp_ok : forall a (R D D': arules a) d is
      (h: matrix_interpretation_dp R D is Domain_naturals (Pos.to_nat d) = Ok D')
      (wf : WF (hd_red_mod R D')), WF (hd_red_mod R D).

    Proof.
      intros a R D D' d is h wf.
      unfold matrix_interpretation_dp in h.
      destruct Domain_naturals; simpl in h; try discr.
      case_eq (matrix_nat_dp a is (Pos.to_nat d));
        intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt].
      (* check >= in R and D *)
      case_eq (ge_R_D R D bge); intro H1; rewrite H1 in h; try discr.
      unfold gt_D in h. unfold ge_R_D in H1.
      inversion h. subst D'. clear h.
      unfold matrix_nat_dp in H. revert H.
      case (map_rev (color_interpret_matrix a (Pos.to_nat d)) is);
        intros l H2; try discr. gen H2.
      set (b:= forallb (fun x : {f : symbol & matrixInt (Pos.to_nat d) (a f)} =>
          let (f, mi) := x in bVforall (fun m : matrix (Pos.to_nat d)
          (Pos.to_nat d) =>
          OrdSemiRing2.bge Nat_as_OSR (get_elem m (dim_pos (Pos.to_nat d))
          (dim_pos (Pos.to_nat d))) 0) (args mi)) l).
      case_eq b; intros H3 H4; subst b; try discr.
      inversion H4. clear H4.
      apply WF_wp_hd_red_mod with (WP:=@WP_Matrix_Nat _ _ l).       
      (** Check that rules [R] is included in [>=]. *)
      unfold brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H1. destruct H1. 
      rewrite forallb_forall in H0.
      ded (H0 x Hx). destruct x as [t u]. simpl in *.
      unfold bsucceq, bool_of_rel.
      destruct ma_succeq'_dec; auto.
      unfold redpair_mat_nat_dp_ge in H1.
      unfold abrule, brule in H1. simpl in *.
      unfold AMatrixBasedInt2.succeq', succeq', term_ge, term_ord, mint_ge in n0.
      apply bmint_ge_ok in H1. contradiction.
      (** Check that rules [D = dp R] is included in [>=]. *)
      unfold brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H1. destruct H1.
      rewrite forallb_forall in H.
      ded (H x Hx). destruct x as [t u]. simpl in *.
      unfold bsucceq, bool_of_rel.
      destruct ma_succeq'_dec; auto.
      unfold redpair_mat_nat_dp_ge in H1.
      unfold abrule, brule in H1. simpl in *.
      unfold AMatrixBasedInt2.succeq', succeq', term_ge, term_ord, mint_ge in n0.
      apply bmint_ge_ok in H1. contradiction.
      (** Remove all rules [>] in [D]. *)
      apply WF_incl with (S := hd_red_mod R (filter (abrule (neg bgt)) D)).
      unfold inclusion. intros t u H4. redtac.
      unfold hd_red_mod. unfold compose. exists t0. split. hyp.
      unfold hd_red. exists l0. exists r. exists s.
      intuition. apply filter_In. apply filter_In in lr.
      intuition. unfold abrule, brule, neg.
      unfold brule, neg in H6. simpl in *.
      unfold bsucc, bool_of_rel in H6.
      destruct ma_succ'_dec in H6; try discr. simpl in *.
      unfold term_gt, AMatrixBasedInt2.term_gt, term_ord in n0;
        simpl in *. unfold mint_gt in n0. rewrite <- bmint_gt_ok in n0.
      apply eq_true_not_negb in n0. subst bgt. apply n0. hyp.
    Qed.

    (*************************************************************************)
    (** ** Matrix intepretations with DP on Arctic N. *)
    (*************************************************************************)

    Require Import AArcticBasedInt2 Arctic_as_OSR AArcticInt2.

    Section weakRedPair.

      (* Arctic natural numbers. *)

      Global Instance coef_sring_arc_nat: CPFSRing.
      
      Proof. 
        apply Build_CPFSRing with (OSR := Arctic_as_OSR).
        apply color_coef_Arcnat.
      Defined.
      
      Variable arity: symbol -> nat.
      Variable dim: nat.
      Notation dim_pos := (dim_pos dim).
      Notation mint:=(@matrixInt _ dim).
      
      Variable l: list {g: symbol & mint (arity g)}.
      
      (* Monotone Algebra of matrix interpretation of domain
        [Nat]. *)
      Definition TM_Mon_ArcNat := @MonotoneAlgebra_ArcNat (Sig arity) dim
                                  (@TMatrix_Int arity dim coef_sring_arc_nat l).
      
      (* Definition of MethodMatrixConf in [AMatrixInt2.v] *)
      Definition TM_Conf_ArcNat :=@Conf (Sig arity) dim _ (@TMatrix_Int _ _ _ l).
        
      (* Definition of weakRedPair of matrix int *)   
      Definition WP_Matrix_ArcNat := @WP_MonAlg (Sig arity) TM_Mon_ArcNat.
        
    End weakRedPair.

    (** Matrix interpretations on arctic natural numbers only happen on
    the top relation.
      Given two orders [>], [>=], they are compatible. However
       with this choice we do not get well-foundedness of the strict order
       as [-oo > -oo].
       Theorem [arctic top termination]: Let [R, R', S] be TRSs over a
       signature [F] and [.] be an arctic F-interpretation over
       [A_N]. If:
       - For each [f \in F], [f] is somewhere finite,
       - [l] >= [f] for every rule [l -> r \in R union S],
       - [l] >> [r] for every rule [l -> r \in R'] and,
       - [SN (R_top/S)]
       Then [SN (R_top \union R'_top/S)]*)

    Require Import AArcticBasedInt2 Arctic_as_OSR AArcticInt2 SemiRing.

    (* >= *)
    Definition redpair_matrix_ar_nat_ge a t u dim Conf :=
      let (l, r)  := @rule_mi _ (Sig a) dim Conf (mkRule t u)
      in bmint_ge l r.

    (* > *)
    Definition redpair_matrix_ar_nat_gt a t u dim Conf :=
      let (l, r)  := @rule_mi _ (Sig a) dim Conf (mkRule t u)
      in bmint_gt l r.

    (* REMARK: need to give the return type if not COQ will complain. *)

    Definition matrix_arctic_nat a (is: list (symbol * cpf.arity * function))
      (dim: nat) :
      result ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)):=
      Match map_rev (@color_interpret_matrix a dim coef_sring_arc_nat) is
      With l ===>
        if forallb (fun l => match l with
           existT f mi   => bVexists (fun m =>
               is_finite (get_elem m (dim_pos dim)(dim_pos dim))) (args mi)
           ||  is_finite (Vnth (const mi) (dim_pos dim)) end) l
       then
       (* REMARK: need to define Conf here *)
       let Conf    := TM_Conf_ArcNat a l in
        Ok (fun t u => redpair_matrix_ar_nat_ge t u Conf,
            fun t u => redpair_matrix_ar_nat_gt t u Conf)
        else Ko _ (Fail FNotMonotone_matrix_arc_naturals).

    Definition type_matrix_arctic a is dom dim :=
      match dom with
        | Domain_naturals => matrix_arctic_nat a is dim
        | Domain_integers =>
          Ko _ (Todo Ttype_polynomialDomain_integers)
        | Domain_rationals delta =>
          Ko _ (Todo Ttype_polynomialDomain_rationals)
        | Domain_arctic dom' =>
          Ko _ (Todo Ttype_polynomialDomain_arctic)
        | Domain_tropical dom' =>
          Ko _ (Todo Ttype_polynomialDomain_tropical)
        | Domain_matrices dim sdim dom' =>
          Ko _ (Todo Ttype_polynomialDomain_matrices)
      end.

    Definition matrix_interpretation_arctic_nat a (R D: arules a) is dom dim :=
      match type_matrix_arctic a is dom dim with
        | Ok (bge, bgt) =>
          if   ge_R_D R D bge
          then gt_D D bgt
          else Ko _ (Fail FRuleNotInLargeOrdering_matrix_arc_naturals)
        | Ko e => Ko _ e
      end.

    (***********************************************************************)
    (** Correctness proof for DP on MI on domain Arctic natural numbers. *)
    
    Require Import ARedPair2.
    
    Lemma matrix_interpretation_arctic_nat_ok : forall a (R D D': arules a) d is
      (h: matrix_interpretation_arctic_nat R D is Domain_naturals
          (Pos.to_nat d) = Ok D')
      (wf : WF (hd_red_mod R D')), WF (hd_red_mod R D).
      
    Proof.
      intros a R D D' d is h wf.
      unfold matrix_interpretation_arctic_nat in h.
      destruct Domain_naturals; simpl in h; try discr.
      case_eq (matrix_arctic_nat a is (Pos.to_nat d)); intros p H;
      rewrite H in h; try discr.
      destruct p as [bge bgt].
      case_eq (ge_R_D R D bge); intro H1; rewrite H1 in h; try discr.
      unfold gt_D in h. unfold ge_R_D in H1.
      inversion h. subst D'. clear h.
      unfold matrix_arctic_nat in H. revert H.
      case (map_rev (color_interpret_matrix a (Pos.to_nat d)) is);
        intros l H2; try discr. gen H2.
      set (b:= forallb (fun l0 : {f : symbol & matrixInt (Pos.to_nat d) (a f)} =>
           let (f, mi) := l0 in bVexists (fun m : matrix (Pos.to_nat d)
           (Pos.to_nat d) =>
           is_finite (@get_elem Arctic_as_OSR  (Pos.to_nat d) (Pos.to_nat d)m _ _
           (dim_pos (Pos.to_nat d))(dim_pos (Pos.to_nat d)))) (args mi) ||
           is_finite (Vnth (const mi)(dim_pos (Pos.to_nat d)))) l).
      case_eq b; intros H3 H4; subst b; try discr.
      inversion H4. clear H4.
      apply WF_wp_hd_red_mod with (WP:=@WP_Matrix_ArcNat _ _ l).
      (** Check that rules [R] is included in [>=]. *)
      unfold brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H1. destruct H1.
      rewrite forallb_forall in H0.
      ded (H0 x Hx). destruct x as [t u]. simpl in *.
      unfold bsucceq, bool_of_rel.
      destruct ma_succeq'_dec; auto; try discr.
      unfold redpair_matrix_ar_nat_ge in H1.
      unfold abrule, brule in H1. simpl in *.
      unfold succeq', AMatrixBasedInt2.succeq', term_ge, term_ord, mint_ge in n0.
      apply bmint_ge_ok in H1. try contradiction.
      (** Check that rules [D = dp R] is included in [>=]. *)
      unfold brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H1. destruct H1.
      rewrite forallb_forall in H.
      ded (H x Hx). destruct x as [t u]. simpl in *.
      unfold bsucceq, bool_of_rel.
      destruct ma_succeq'_dec; auto.
      unfold redpair_matrix_ar_nat_ge in H1.
      unfold abrule, brule in H1. simpl in *.
      unfold succeq', AMatrixBasedInt2.succeq', term_ge, term_ord, mint_ge in n0.
      apply bmint_ge_ok in H1. try contradiction.
      (** Remove all rules [>] in [D]. *)
      apply WF_incl with (S := hd_red_mod R (filter (abrule (neg bgt)) D)).
      unfold inclusion. intros t u H4. redtac. unfold hd_red_mod.
      unfold compose. exists t0. split. hyp.
      unfold hd_red. exists l0. exists r. exists s.
      intuition. apply filter_In. apply filter_In in lr.
      intuition. unfold brule, neg.
      unfold brule, neg in H6. simpl in *.
      unfold bsucc, bool_of_rel in H6.
      destruct ma_succ'_dec in H6; try discr. simpl in *.
      unfold term_gt, AMatrixBasedInt2.term_gt, term_ord, mint_gt in n0.
      simpl in *. rewrite <- bmint_gt_ok in n0. apply eq_true_not_negb in n0.
      subst bgt. apply n0. hyp.
    Qed.

    (*************************************************************************)
    (** ** Matrix intepretations with DP on Arctic Z (below zero). *)
    (*************************************************************************)
    
    Require Import ArcticBZ_as_OSR AArcticBZInt2.
     
    Section weakRedPair_ABZ. (* MOVE? *)
        
      (* Arctic integer numbers. *)

      Global Instance coef_sring_arc_int : CPFSRing.
      
      Proof. 
        apply Build_CPFSRing with (OSR := ArcticBZ_as_OSR).
        apply color_coef_ArcInt.
      Defined.
      
      Variable arity: symbol -> nat.
      Variable dim: nat.
      
      Notation dim_pos := (dim_pos dim).
      Notation mint := (@matrixInt _ dim).
      
      Variable l: list {g: symbol & mint (arity g)}.
      
      (** Monotone Algebra of matrix interpretation of domain
        [Nat]. *)        
      Definition TM_Mon_ArcInt := @MonotoneAlgebra_ArcInt (Sig arity) dim
                                  (@TMatrix_Int arity dim coef_sring_arc_int l).
      
      (** Definition of MethodMatrixConf in [AMatrixInt2.v] *)
      Definition TM_Conf_ArcInt :=@Conf (Sig arity) dim _
                                 (@TMatrix_Int arity dim coef_sring_arc_int l).
        
      (** Definition of weakRedPair of matrix int *)
      Definition WP_Matrix_ArcInt := @WP_MonAlg (Sig arity) TM_Mon_ArcInt.
          
    End weakRedPair_ABZ.

    (***********************************************************************)

    (* >= *)
    Definition redpair_mat_ar_int_ge a t u dim Conf :=
      let (l, r)  := @rule_mi _ (Sig a) dim Conf (mkRule t u)
      in bmint_ge l r.

    (* > *)
    Definition redpair_mat_ar_int_gt a t u dim Conf :=
      let (l, r)  := @rule_mi _ (Sig a) dim Conf (mkRule t u)
      in bmint_gt l r.

    (* REMARK: need to give the return type if not COQ will complain. *)

    Definition matrix_arctic_int a (is: list (symbol * cpf.arity * function))
      dim:result ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)):=
      Match map_rev (@color_interpret_matrix a dim coef_sring_arc_int) is
      With l ===>
      if forallb (fun l => match l with
         existT f mi => is_above_zero (@Vnth ArcticBZDom dim (const mi)
                       _ (dim_pos dim)) end) l
      then (* REMARK: need to define Conf here. *)
        let Conf := @TM_Conf_ArcInt a dim l in
        Ok (fun t u => redpair_mat_ar_int_ge t u Conf,
            fun t u => redpair_mat_ar_int_gt t u Conf)
      else Ko _ (Fail FNotMonotone_matrix_arc_bz).

    Definition type_matrix_arctic_int a is dom dim :=
      match dom with
        | Domain_naturals =>
          Ko _ (Todo Ttype_polynomialDomain_naturals)
        | Domain_integers => matrix_arctic_int a is dim
        | Domain_rationals delta =>
          Ko _ (Todo Ttype_polynomialDomain_rationals)
        | Domain_arctic dom' =>
          Ko _ (Todo Ttype_polynomialDomain_arctic)
        | Domain_tropical dom' =>
          Ko _ (Todo Ttype_polynomialDomain_tropical)
        | Domain_matrices dim sdim dom' =>
          Ko _ (Todo Ttype_polynomialDomain_matrices)
      end.
    
    Definition matrix_interpretation_arctic_int a (R D: arules a) is dom dim:=
      match type_matrix_arctic_int a is dom dim with
        | Ok (bge, bgt) =>
          if   ge_R_D R D bge
          then gt_D D bgt
          else Ko _ (Fail FRuleNotInLargeOrdering_matrix_arcbz_dp)
        | Ko e => Ko _ e
      end.
    
    (***********************************************************************)
    (** Correctness proof of matrix int of domain arctic integers. *)
    
    Require Import ArcticBZ_as_OSR SemiRing.
    
    Lemma matrix_interpretation_arctic_int_ok : forall a (R D D': arules a)d is
      (h: matrix_interpretation_arctic_int R D is Domain_integers
          (Pos.to_nat d) = Ok D') (wf: WF (hd_red_mod R D')),
      WF (hd_red_mod R D).
      
    Proof.
      intros a R D D' d is h wf.
      unfold matrix_interpretation_arctic_int in h.
      destruct Domain_integers; simpl in h; try discr.
      case_eq (matrix_arctic_int a is (Pos.to_nat d));
        intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt].
      case_eq (ge_R_D R D bge); intro H1; rewrite H1 in h; try discr.
      unfold gt_D in h. unfold ge_R_D in H1.
      inversion h. subst D'. clear h.
      unfold matrix_arctic_int in H. gen H.
      case_eq (map_rev (color_interpret_matrix a (Pos.to_nat d)) is);
        intros l H2; rewrite H2 in H; try discr.
      set (b:=forallb
         (fun l0 : {f : symbol & matrixInt (Pos.to_nat d) (a f)} =>
          let (f, mi) := l0 in
          is_above_zero (@Vnth ArcticBZDom _ (@const ArcticBZ_as_OSR _ _ mi) _
          (dim_pos (Pos.to_nat d)))) l).
      case_eq b; intros H3 H4; subst b; try discr.
      inversion H4. clear H4.
      apply WF_wp_hd_red_mod with (WP:=@WP_Matrix_ArcInt _ _ l).
      (** Check that rules [R] is included in [>=]. *)
      unfold brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H1. destruct H1.
      rewrite forallb_forall in H1.
      ded (H1 x Hx). destruct x as [t u]. simpl in *.
      unfold bsucceq, bool_of_rel.
      destruct ma_succeq'_dec; auto; try discr.
      unfold redpair_mat_ar_int_ge in H4.
      unfold abrule, brule in H4. simpl in *.
      unfold succeq', AMatrixBasedInt2.succeq', term_ge, term_ord, mint_ge in n0.
      apply bmint_ge_ok in H4. try contradiction.
      (** Check that rules [D = dp R] is included in [>=]. *)
      unfold brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H1. destruct H1.
      rewrite forallb_forall in H0.
      ded (H0 x Hx). destruct x as [t u]. simpl in *.
      unfold bsucceq, bool_of_rel.
      destruct ma_succeq'_dec; auto.
      unfold redpair_mat_ar_int_ge in H4.
      unfold abrule, brule in H4. simpl in *.
      unfold succeq', AMatrixBasedInt2.succeq', term_ge, term_ord, mint_ge in n0.
      apply bmint_ge_ok in H4. try contradiction.
      (** Remove all rules [>] in [D]. *)
      apply WF_incl with (S := hd_red_mod R (filter (abrule (neg bgt)) D)).
      unfold inclusion. intros t u H4. redtac.
      unfold hd_red_mod. unfold compose. exists t0. split. hyp.
      unfold hd_red. exists l0. exists r. exists s.
      intuition. apply filter_In. apply filter_In in lr.
      intuition. unfold brule, neg. unfold brule, neg in H7. simpl in *.
      unfold bsucc, bool_of_rel in H7. destruct ma_succ'_dec in H7; try discr.
      simpl in *. unfold term_gt, AMatrixBasedInt2.term_gt,
      term_ord, mint_gt in n0.
      simpl in *. rewrite <- bmint_gt_ok in n0.
      apply eq_true_not_negb in n0. subst bgt. apply n0. hyp.
    Qed.

    (***********************************************************************)
    (** Matrix interpretation on different domains of arctic. *)

    Definition matrix_interpretation_arctic a (R D: arules a) dom dim is :=
      let n := nat_of_P dim in
      match dom with
        | Domain_naturals =>
          matrix_interpretation_arctic_nat R D is dom n
        | Domain_integers =>
          matrix_interpretation_arctic_int R D is dom n
        | Domain_rationals _ =>
          Ko _ (Todo Ttype_polynomialDomain_rationals)
        | Domain_arctic _ =>
          Ko _ (Todo Ttype_polynomialDomain_arctic)
        | Domain_tropical _ =>
          Ko _ (Todo Ttype_polynomialDomain_tropical)
        | Domain_matrices _ _ _ =>
          Ko _ (Todo Ttype_polynomialDomain_matrices)
      end.

    Definition type_matrix_interpretation_dp a (R D: arules a) is dom dim :=
      match dom with
        | Domain_naturals =>
          matrix_interpretation_dp R D is dom (nat_of_P dim)
        | Domain_integers =>
          Ko _ (Todo Ttype_polynomialDomain_integers)
        | Domain_rationals delta =>
          Ko _ (Todo Ttype_polynomialDomain_rationals)
        | Domain_tropical _ =>
          Ko _ (Todo Ttype_polynomialDomain_tropical)
        | Domain_arctic dom' =>
          matrix_interpretation_arctic R D dom' dim is
        | Domain_matrices dim sdim dom' =>
          Ko _ (Todo Ttype_polynomialDomain_matrices)
      end.

    (***********************************************************************)
    
    Definition redPair_interpretation_dp a (R D: arules a) (t: type_t9) 
      (is: list (symbol * cpf.arity * function)): result (arules a) :=
      match t with
        | Type_t9_polynomial dom degmax =>
          polynomial_interpretation_dp R D is dom
        | Type_t9_matrixInterpretation dom dim sdim =>
          type_matrix_interpretation_dp R D is dom dim
      end.

    (***********************************************************************)
    (** Structure proof of reduction pair interprertaion of DP. 
     1. Polynomial interpreration
       a. Domain natural numbers.
       b. Domain rational numbers.
     2. Matrix interpertation
       a. Domain natural numbers.
       b. Domain Arctic natural numbers.
       c. Domain Arctic integer numbers. *)

    Lemma redPair_interpretation_dp_ok : forall a (R D D' : arules a) t is,
      redPair_interpretation_dp R D t is = Ok D' -> WF (hd_red_mod R D') ->
      WF (hd_red_mod R D).

    Proof.
      intros a R D D' t is h wf. destruct t; simpl in h; try discr.
      (** Polynomial interpretation over natural numbers and rational
          numbers. *)
      eapply polynomial_interpretation_dp_ok.
      apply h. apply wf.     
      (** Matrix interpretation over natural numbers. *)
      destruct d; simpl in h; try discr.
      eapply matrix_interpretation_dp_ok.
      apply h. apply wf.
      (** Matrix interpretation over arctic natural numbers.  *)
      destruct d; simpl in h; try discr.
      eapply matrix_interpretation_arctic_nat_ok.
      apply h. apply wf.     
      (** Matrix interpretation over arctic integer numbers. *)
      eapply matrix_interpretation_arctic_int_ok.
      apply h. apply wf.
    Qed.
    
    (*************************************************************************)
    (** ** Recursive Path Order (RPO) with DP *)
    (*************************************************************************)
    
    (** RPO is an ordering introduced by Dershowitz. It extends a
    well-founded order on the signature, called a precedence, to a
    reduction order on terms. We used the Coccinelle's library. *)

    Require Import ordered_set Coccinelle2 rpo2.

    (* Define a rpo_redpair_dp_ge *)

    Definition rpo_term_dp a t := @term_of_aterm (Sig a) t.

    (* >= *)
    Definition rpo_redpair_dp_ge (a:symbol->nat) l t u :=
      match cpf2color.rpo_eval l rpo_arg
            (@rpo_term_dp a t) (@rpo_term_dp a u) with
        | Some Equivalent | Some Greater_than => true
        | _ => false
      end.

    (* > *)
    Definition rpo_redpair_dp_gt a l t u :=
      match cpf2color.rpo_eval l rpo_arg
            (@rpo_term_dp a t) (@rpo_term_dp a u) with
        | Some Greater_than => true
        | _ => false
      end.

    (* Conditions of RPO:
        - Check the status of two symbols, they are the same symbol
        if they have the same precendence. *)

    Definition condition_rpo_dp a l :=
      let fs := split_list l in
      forallb (fun f => forallb (fun g =>
      @cpf2color.bprec_eq_status_symb a l f g) fs) fs.

    Definition pathOrder_term_dp a (l: list (symbol * cpf.arity *
      nonNegativeInteger * t10)):
      error_monad.result ((aterm a -> aterm a -> bool) *
                          (aterm a -> aterm a -> bool)) :=
      if condition_rpo_dp a l
      then Ok (fun t u => rpo_redpair_dp_ge l t u,
               fun t u => rpo_redpair_dp_gt l t u)
      else Ko _ (Fail FNotpathOrder_term).
 
    (*************************************************************************)
    (** Correctness proof of RPO with DP *)

    Lemma rpo_without_af_dp_ok: forall a (R D D': arules a) l
      (h: match pathOrder_term_dp a l with
            | Ok (bge, bgt) =>
              if   ge_R_D R D bge
              then gt_D D bgt
              else Ko _ (Fail FNotpathOrder_rpo_dp)
            | Ko e => Ko _ e
          end = Ok D')(wf : WF(hd_red_mod R D')), WF(hd_red_mod R D).
      
    Proof.
      intros a R D D' l h wf.
      case_eq (pathOrder_term_dp a l); intros p H;
      rewrite H in h; try discr.
      destruct p as [bge bgt].
      case_eq (ge_R_D R D bge); intro H1; rewrite H1 in h; try discr.
      unfold gt_D in h. unfold ge_R_D in H1.
      inversion h. subst D'. clear h.
      unfold pathOrder_term_dp in H. 
      case_eq (condition_rpo_dp a l); intros H2; rewrite H2 in H;
      try discr. unfold condition_rpo_dp in H2.
      inversion H. clear H.       
      apply WF_wp_hd_red_mod with (WP:= @WP_RPO rpo_arg (Sig a)
            (Precendence_Imp a l rpo_arg)).
      (** Check that all rules [R] are included in [>=] *)
      simpl. unfold brule, bsucceq; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H1. destruct H1.
      rewrite forallb_forall in H0.
      ded (H0 x Hx). destruct x as [t u]. simpl in *.
      unfold rpo_redpair_dp_ge in H1.
      unfold brule in H1. apply H1.
      (** Check that all rules in [D = dp R] are included in [>=]. *)
      simpl. unfold brule, bsucceq; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H1. destruct H1.
      rewrite forallb_forall in H.
      ded (H x Hx). destruct x as [t u]. simpl in *.
      unfold rpo_redpair_dp_ge in H1.
      unfold abrule, brule in H1. apply H1.
      (** Remove all rules [D] that are included in [>]. *)
      apply WF_incl with (S:= hd_red_mod R (filter (brule (neg bgt)) D)).
      unfold inclusion. intros t u H5. redtac.
      unfold hd_red_mod. unfold compose.
      exists t0. split. hyp. unfold hd_red.
      exists l0. exists r. exists s. intuition.
      apply filter_In. apply filter_In in lr.
      intuition. unfold brule, neg. unfold brule, neg in H5.
      simpl in *. subst bgt. apply H5. hyp.
    Qed.

    (*************************************************************************)
    (** ** Recursive Path Order (RPO) + Argument filtering (AF) with DP *)
    (*************************************************************************)
 
    (** Argument filtering defined in CoLoR has two cases:
       - Collapsing
       - Non-collapsing. *)
    
    Open Scope nat_scope.

    (** The signature is changed in case of filtering (collapsing) *)

    Definition sig_dp a args := Sig (@ASignature.arity (
      Sig (filter_arity (Sig a) (@color_pi_filter a args)))).

    (* Combination of collapsing and non-collapsing term *)

    Definition rpo_term_pf_dp a t args :=
      let l := List.map (@pi_filter a) args in
      @term_of_aterm (sig_dp a l) (color_proj args
      (@color_filter a l t)).

    (* >= *)

    Definition redpair_pf_ge a args l t u :=
      match cpf2color.rpo_eval l rpo_arg
            (rpo_term_pf_dp t args) (@rpo_term_pf_dp a u args) with
        | Some Equivalent | Some Greater_than => true
        | _ => false
      end.

    (* > *)
    Definition redpair_pf_gt a args l t u :=
      match cpf2color.rpo_eval l rpo_arg
            (rpo_term_pf_dp t args) (@rpo_term_pf_dp a u args) with
        | Some Greater_than => true
        | _ => false
      end.

    (* return an ordering pair (>=, >) *)

    Definition pathOrder_rpo_proj_filter_dp a
      (l: list (symbol * cpf.arity * nonNegativeInteger * t10))
      (args : list (symbol * cpf.arity * t11)): error_monad.result
      ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)) :=
      if condition_rpo_dp a l  (* CHECK: do I really need this condition? *)
      then Ok (fun t u => redpair_pf_ge args l t u,
               fun t u => redpair_pf_gt args l t u)             
      else Ko _ (Fail FPrecedence_incompatible_statuses_dp).

    (* Combination of collapsing and non-collapsing AF. *)
    Definition pathOrder_term_rpo_af_dp a
     (l: list (symbol * cpf.arity * nonNegativeInteger * t10))
     (args : list (symbol * cpf.arity * t11)) : error_monad.result
      ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)) :=
      match args with
        | (_, _, t) :: _ as args' =>
          if is_proj_filter t
          then Match pathOrder_rpo_proj_filter_dp a l args With
               rpo_filter_proj ===> Ok rpo_filter_proj
          else  Ko _ (Fail Frpo_af_dp)
        | nil => Ko _ (Fail Frpo_af_dp_nil)
      end.

    (***********************************************************************)
    (** Correctness proof of RPO with AF. *)

    Lemma rpo_with_af_dp_ok: forall a (R D D': arules a) l o
      (h: match pathOrder_term_rpo_af_dp a l o with
            | Ok (bge, bgt) =>
              if   ge_R_D R D bge
              then gt_D D bgt
              else Ko _ (Fail FNotpathOrder_with_af_dp)
            | Ko e => Ko _ e
          end = Ok D') (wf: WF (hd_red_mod R D')), WF (hd_red_mod R D).
    
    Proof.
      intros a R D D' l args h wf.
      case_eq (pathOrder_term_rpo_af_dp a l args);
        intros p H; rewrite H in h; try discr.
      destruct p as [bge bgt].
      case_eq (ge_R_D R D bge); intros H1; rewrite H1 in h; try discr.
      unfold gt_D in h. unfold ge_R_D in H1.
      inversion h. subst D'. clear h.
      unfold pathOrder_term_rpo_af_dp in H.
      destruct args; try discr.
      destruct p; try discr.
      destruct p; try discr.
      (* collapsing + non-collapsing *)
      case_eq (is_proj_filter t); intros H2; rewrite H2 in H; try discr.
      set (args':= (s, a0, t) :: args). fold args' in H.
      case_eq (pathOrder_rpo_proj_filter_dp a l args');
        intros p H3; rewrite H3 in H; try discr.
      inversion H. clear H. subst p.
      (* unfold definition in hyp *)
      unfold pathOrder_rpo_proj_filter_dp in H3.
      (* check the condition of RPO *)
      case_eq (condition_rpo_dp a l); intro H4; rewrite H4 in H3;
      try discr.
      inversion H3. clear H3.
      (* set pair *)
      set (ls := List.map (pi_filter a) args').
      (* this is a condition of projection + filter in AF *)
      
      apply WF_wp_hd_red_mod with (WP:=
       (* WP_Perm : Sig -> Perm Sig -> DS_WeakRedPair (perm_Sig (Sig := Sig))
                    -> DS_WeakRedPair Sig *)
       @WP_Perm (Sig a)
      (* Perm_Imp : arity -> ls -> Perm (Sig a) *)
      (Perm_Imp a ls)
      (* WP_Proj : Sig -> Proj Sig -> DS_WeakRedPair Sig -> DS_WeakRedPair Sig *)
      (@WP_Proj (Sig (@ASignature.arity (color_perm_Sig a ls)))
      (* Proj_Imp : arity -> ls -> Proj (Sig a) *)
      (@Proj_Imp (@ASignature.arity (color_perm_Sig a _)) args')
      (* WP_RPO: nat -> Sig -> Pre Sig -> DS_WeakRedPair Sig *)
      (@WP_RPO rpo_arg (Sig (@ASignature.arity (color_perm_Sig a ls)))
      (* Precedence_Imp : arity -> ls -> nat -> Pre (Sig a) *)
      (Precendence_Imp (@ASignature.arity (color_perm_Sig a ls)) l rpo_arg)))).

      (** Check that all rules [R] are included in [>=] *)

      simpl. unfold brule, pbsucceq; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H1. destruct H1.
      unfold redpair_pf_ge in H0.
      rewrite forallb_forall in H0. unfold rpo_term_pf_dp in H0.
      unfold color_filter, color_proj in H0.
      ded (H0 x Hx). destruct x as [u v]. simpl in *.
      unfold brule in H1. apply H1.

      (** Check that all rules in [D = dp R] are included in [>=]. *)
      
      simpl. unfold brule, pbsucceq; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H1. destruct H1.
      unfold redpair_pf_ge in H.
      rewrite forallb_forall in H. unfold rpo_term_pf_dp in H.
      unfold color_filter, color_proj in H.
      ded (H x Hx). destruct x as [u v]. simpl in *.
      unfold brule in H1. apply H1.
      
      (** Remove all rules [D] that are included in [>]. *)

      apply WF_incl with (S:= hd_red_mod R (List.filter (brule (neg bgt)) D)).
      unfold inclusion. intros u v H8. redtac.
      unfold hd_red_mod. unfold compose.
      exists t0. split. hyp.
      unfold hd_red. exists l0. exists r.
      exists s0. intuition.
      apply filter_In. apply filter_In in lr. intuition.
      unfold brule, neg. unfold brule, neg in H6.
      simpl in *. subst bgt. apply H6. hyp.
    Qed.

    (***********************************************************************)
    (** DP + RPO + AF *)

      Definition rpo_filter_dp a (R D: arules a) sp af :=
        match pathOrder_term_rpo_af_dp a sp af with
          | Ok (bge, bgt) =>
            if   ge_R_D R D bge
            then gt_D D bgt
            else Ko _ (Fail FNotpathOrder_with_af_dp)
          | Ko e => Ko _ e
        end.

      (** DP + RPO *)

      Definition rpo_dp a (R D : arules a) sp :=
        match pathOrder_term_dp a sp with
          | Ok (bge, bgt) =>
            if   ge_R_D R D bge
            then gt_D D bgt
            else Ko _ (Fail FNotpathOrder_rpo_dp) 
          | Ko e => Ko _ e
        end.

      Definition pathOrder_dp a (R D: arules a) sp (af: option argumentFilter)
      : error_monad.result (arules a) :=
        match af with
          | Some af => (* Combination with argument filter *)
            rpo_filter_dp R D sp af
          | None    => rpo_dp R D sp (* Without argument filter *)
        end.
    
    (***********************************************************************)
    (** Correctness proof of [pathOrder_dp] *)

    Lemma pathOrder_dp_ok : forall a (R D D': arules a) l o,
      pathOrder_dp R D l o = Ok D' -> WF (hd_red_mod R D') ->
      WF (hd_red_mod R D).

    Proof.
      intros a R D D' l oaf h wf.
      unfold pathOrder_dp in h.
      destruct oaf; try discr.      
      (** Path ordering with argument filtering. *)
      apply rpo_with_af_dp_ok with (D':=D')(l:=l)(o:=a0).
      hyp. hyp.
      (** Path ordering without argument filtering. *)
      apply rpo_without_af_dp_ok with (D':=D')(l:=l).
      hyp. hyp.
    Qed.

    (***********************************************************************)
    (** Ordering constrainst proof with reduction pair interpretation of
     dependency pair transformation. Currently support interpretation
     and path ordering. *)
    
    Definition redPair_dp a (R D:arules a) rp : error_monad.result (arules a) :=
      match rp with
        | RedPair_interpretation t is => redPair_interpretation_dp R D t is
        | RedPair_pathOrder sp oaf => pathOrder_dp R D sp oaf
        | RedPair_knuthBendixOrder _ _ _ =>
          Ko _ (Todo TRedPair_knuthBendixOrder)
        | RedPair_scnp _ _ _ =>
          Ko _ (Todo TRedPair_scnp)
      end.
    
    Definition ruleRemoval_dp a (R D: arules a) ocp :=
      match ocp with
        | OrderingConstraintProof_redPair rp => redPair_dp R D rp
        | OrderingConstraintProof_satisfiableAssumption _ =>
          Ko _ (Todo TOrderingConstraintProof_satisfiableAssumption)
      end.

    (**************************************************************************)
    (** ** Check that [D = dp R] is a trivial proof by stating the set
     of DPs is empty valid termination proof for [hd_red_mod R D]. *)
    (**************************************************************************)  
    Definition pIsEmpty a (D: arules a) :=
      if is_empty D then OK else Ko _ (Error ErDPNotEmpty).

    Lemma pIsEmpty_ok : forall a (R D: arules a),
      pIsEmpty D = OK -> WF (hd_red_mod R D).
    
    Proof.
      intros a R D. unfold pIsEmpty. destruct D; simpl; intro.
      apply WF_hd_red_mod_empty. discr.
    Qed.
    
    (*************************************************************************)
    (** ** Decomposition of Dependency Graph (DG) *)
    (*************************************************************************)
 
    (** A decomposition of a list of rules is a list of list of rules.
       WARNING: the list of DPs is reversed since in CPF, all forward
       arcs are given while in Rainbow, there must be no forward arcs.
       (reverse component list.) *)

    Definition decomp_aux a
      (ci: cpf.dps*boolean*option (list positiveInteger)*option cpf.dpProof) :=
      match ci with
        | (dps, b, f, p) => Match map_rev (color_rule a nat_of_string) dps
                            With dps' ===> Ok (dps', b, f, p)
      end.
    
    Definition decomp a cs := map_rev (decomp_aux a) cs.

    (*************************************************************************)
    (** ** Dependency Pair problems *)
    (*************************************************************************)
    
    (** A). [pIsEmpty]: is the most basic technique which demands that the set
       of [D] is empty. (trivial proof by stating that the set of DPs is
       empty).     

       B). [depGraphProc] Dependency graph: split the current set of
       DPs into several smaller subproblems by using some DP-graph
       estimation. Note that all components of the graph have to be
       specified, including singleton nodes which do not form an SCC
       on their own. The list of components has to be given in
       topological order, where the components with no incoming
       edges are listed first.

       - Dependency graph is the graph where the nodes are the dependency pairs
       of [R]. In general the dependency graph is undecidable. We used an
       approximation graph based on unification instead of the dependency
       graph.

       - Assumptions in CoLoR library proving decomposition graph based on
       unification [ADPUnif.v]:
       - [hypR.] there is no variable at the left hand side of [R] and
       - [hypD.] there is no undefined symbol at the right hand side of [D]
       - Conditions for check the termination in a dependency graph
       ADecomp.v: [Lemma WF_decomp_co_scc].

       [hypD.] preserve variables in [D] [cs]. check in the decomposition
       graph [cs]
       [hyp4-hyp1.] cs [=] D;
       [hyp2.] check the valid of decomposition graph: a decomposition
       [(c1,..cn)] is valid if there is no edge from [j (j in cj)] to [i (i
       in ci)], for all [i < j];
       [hyp3.] check termination of relations: first condition, the [SCC] is
       satisfied the condition of valid decomposition graph; Or each
       component is terminating when its [dpProof] is satisfied; taking a
       list of [SCC cs], testing each component with two arguments:
       - Is it a [SCC b]: true/false? (the topological list for
       decomposition graph has to be given) in each subproblem [ci].
       - Is there an option proof tree [op]?

       C). [redPairProc] An application of the reduction pair processor:
       Use a reduction pair where only the "non-strict order" has to be
       monotone. It allows to delete those DPs which are "strictly
       oriented". The remaining DPs have to be given. If the ordering
       constraint proof is only an assumption, the
       orderingConstraints-element becomes mandatory.
       - Three inputs are required:
       1. The reduction pair [ocp] i.e, some polynomial interpretations.
       2. The dependency pairs [dps] that remains after the application of
       the reduction pair processor.     
       3. A proof [p] that the remaining DP problem.

       - [n: nat]: define function [dpProof] and [depGraphProc] by recursive
       functions by adding an artificial (is a natural number [n]) extra
       argument which purpose is to make the function structually recursive
       with respect to this argument. The function then naturally performs a
       case analysis on the artificial argument. When the base case is
       reached [0].

       - [DpProof_monoRedPairProc]: use a reduction pair where both the
       non-strict and the strict order have to be monotone. It allows to
       delelte those DPs and those rules of the TRSs which are strictly
       oriented. The remaining DPs and the remaining TRSs have to be
       given.  (* handled like redPairProc *)*)

    Require Import error_monad.

    Open Scope nat_scope.
    
    (* Assume given the number of unifications for approximation graph. *)

    Variable uni: nat. 

    Require Import AReverse AUnary ATerm_of_String String_of_ATerm.

    (***********************************************************************)
    (** Define auxilary function for [subtermProc]. *)

    Definition subtermProc_aux args (m: nat) a (R D: arules a) p
      (DP: nat ->forall a : symbol -> nat, arules a -> arules a ->
       cpf.dpProof -> result unit) :=
      match args with
        | (f, _, t) :: l' =>
          if is_collapsing t (* only check the case of collapsing *)
          then
            let pR := color_proj_rules args R in
            let pD := color_proj_rules args D in
            DP m a pR pD p
          else Ko _ (Todo Todo1) (* TODO: change message  *)
        | nil => Ko _ (Todo Todo1) (* TODO *)
      end.

    (***********************************************************************)
    (** Define auxilary function for [dpGraphProc] *)

    (* Conditions to check DG: 
      - check that there is no variable on the left hand side of R,
      - check that there is no undefined symbol on the right hand
        side of R,
      - check that the variables of D are preserve *)

    Definition conditions_depGraphProc a (R D: arules a):= 
      forallb (@is_notvar_lhs (Sig a)) R &&
      forallb (undefined_rhs R) D        &&
      brules_preserve_vars D.

    (** Define an approximate graph *)

    Definition approx a (R D: arules a) := dpg_unif_N uni R D.

    (** The fourth condition of DG:
    - if it is a real SCC, and has some dpProof then continue to call
      to the dpProof,
    - if it is not a SCC, then we do not care about the dpProof. Call
      to the function [co_scc] to compute the approximate graph with
      dps. 
    - the pair (<realScc>, dpProof):
      Each SCC terminates whether if SCC is truly a SCC then check it
      WF; if SCC is not a SCC then test co_scc = true (means there is
      no edge from i -> j (j > i);
      REMARK: in COQ the inductive function [dpProof] fails to guess
      the decreasing argument. Add a new argument [n] to be accepted
      by COQ. [m] becomes a decreasing argument,*)

    Definition fourth_condition (m: nat) a (R D: arules a) cs'
      (DP : nat ->forall a : symbol -> nat, arules a -> arules a ->
       cpf.dpProof -> result unit) :=
      forallb (fun ci: arules a * bool * option (list positiveInteger) *
                       option dpProof =>
      let '(dps, b, _, op) := ci in
      (* check the pair (<realScc>,dpProof) *)
      match b, op with
        | true, Some pi => bool_of_result (DP m a R dps pi)       
        | false, _      => co_scc (approx R D) dps
        | _, _          => false
      end) cs'.

    (** The third condition of DG:
       - if it is a valid decomposition graph then continue to check
         the fourth condition. *)

    Definition third_condition a m (R D: arules a) ls cs' DP :=
    if valid_decomp (approx R D) ls
    then
      if fourth_condition m R D cs' DP
      then OK
      else Ko _ (Fail FComponent)
    else   Ko _ (Fail FDecomp).

    (* TODO *)
    (** Define an auxiliary function for DG. *)

    Definition depGraphProc_aux a m (R D: arules a) cs 
      (DP : nat -> forall a : symbol -> nat, arules a -> arules a ->
            cpf.dpProof -> result unit) :=
        if conditions_depGraphProc R D
        then 
          Match decomp a cs With cs' ===>
                let ls := split_list cs' in
                if   equiv_rules (flat ls) D
                then third_condition m R D ls cs' DP
                else Ko _ (Todo Todo1)
          (*else
            if  equiv_rules (reverse_trs (flat ls)) (reverse_trs D)
            then third_condition m R D ls cs' DP
            else Ko _ (Todo TDpProof_redPairProc)*)
        else Ko _ (Todo TDpProof_redPairProc).
         
           (*(* Check with string reverse *)
           if brules_preserve_vars R
           then
             (* 1: DP with the rules are translated to string reverse *)
             if equiv_rules (reverse_trs (flat ls)) (reverse_trs D)(* CHECK *)
             then third_condition m R D ls cs' DP
             else
               (* 2: DP Without apply string reverse *)
               if equiv_rules (flat ls) D
                  then third_condition m R D ls cs' DP
                  else Ko _ (Todo TDpProof_redPairProc) (* TEST *)
           else Ko _ (Fail FDpProof_zerobound)
      else Ko _ (Todo Todo1).*)

    (** Auxiliary function of argument filtering proc *)

    Definition is_nonCollapsing t :=
      match t with
        | T11_nonCollapsing _ => true
        | _ => false
      end.
    
    (** AF projection (non-collapsing pi ) *)

    Definition AF_proj_aux a (R D: arules a) m args p
       (DP : nat -> forall a : symbol -> nat, arules a -> arules a ->
            cpf.dpProof -> result unit) :=
      let pR := color_proj_rules args R in
      let pD := color_proj_rules args D in
      DP m a pR pD p.

    (** AF filtering (collpasing p) *)

    Definition AF_filter_aux a (R D: arules a) m args p
       (DP : nat -> forall a : symbol -> nat, arules a -> arules a ->
            cpf.dpProof -> result unit) :=
      let l := List.map (@pi_filter a) args in
      let pi := color_pi_filter a l in
      let fR := color_filter_rules pi R in 
      let fD := color_filter_rules pi D in
      @DP m (filter_arity (Sig a) pi) fR fD p.

    Definition conditions_AF_filter_aux a args t :=
      let ls := List.map (@pi_filter a) args in
      is_nonCollapsing t &&
      forallb (fun x : {f : symbol & nat_lts (a f)} =>
      let (f, p) := x in brepeat_free beq_nat
      (List.map (val ( n:= a f)) p)) ls.

    (***********************************************************************)
    (** ** Dependency proof:
        - D is empty
        - DP graph
        - Rule removal
        - String reverse *)

    Fixpoint dpProof (n: nat) a (R D: arules a) p {struct n} : result unit :=
      match n with
        | 0   => Ko _ (Fail FDpProof_zerobound)
        | S m =>
          match p with
            | DpProof_pIsEmpty => pIsEmpty D
            | DpProof_depGraphProc cs =>
              (* TEST string reverse *)
              (*if brules_preserve_vars R
              then
              depGraphProc m (reverse_trs R) (reverse_trs D) cs*) (* CHECK *)
              (*else *)depGraphProc m R D cs
            | DpProof_redPairProc (Some _) _ _ _ =>
              Ko _ (Todo TDpProof_redPairProc)
            | DpProof_redPairProc None ocp dps p =>
              Match ruleRemoval_dp R D ocp With D' ===>
                dpProof m R D' p
            | DpProof_redPairUrProc oc ocp dps usr p =>
              Ko _ (Todo TDpProof_redPairUrProc)
            | DpProof_monoRedPairProc (Some _) _ _ _ _ =>
              Ko _ (Todo TDpProof_monoRedPairProc)
            | DpProof_monoRedPairProc None ocp dps rs p =>
              Match ruleRemoval_dp R D ocp With D' ===> dpProof m R D' p
            | DpProof_monoRedPairUrProc oc ocp dps rs usr p =>
              Ko _ (Todo TDpProof_monoRedPairUrProc)
            | DpProof_subtermProc af ls _ p => (* TODO *)
              match ls with
                | Datatypes.nil => subtermProc m R D af p
                (* only check on list (rule * rewriteSequence) is nil *)
                | _ => Ko _ (Todo TDpProof_subtermProc)
              end
            | DpProof_argumentFilterProc args dps rs p =>
              argumentFilterProc m R D args p
            | DpProof_semlabProc _ _ _ _ _ =>
                Ko _ (Todo TDpProof_semlabProc)
            | DpProof_unlabProc _ _ _  =>
              Ko _ (Todo TDpProof_unlabProc)
            | DpProof_sizeChangeProc _ _ =>
              Ko _ (Todo TDpProof_sizeChangeProc)
            | DpProof_flatContextClosureProc _ _ _ _ _  =>
              Ko _ (Todo TDpProof_flatContextClosureProc)
            | DpProof_uncurryProc _ _ _ _ _ =>
              Ko _ (Todo TDpProof_flatContextClosureProc)
            | DpProof_finitenessAssumption _ =>
              Ko _ (Todo TDpProof_finitenessAssumption)
            | DpProof_usableRulesProc _ _  =>
              Ko _ (Todo TDpProof_usableRulesProc)
            | DpProof_innermostLhssRemovalProc _ _ =>
              Ko _ (Todo TDpProof_innermostLhssRemovalProc)
            | DpProof_switchInnermostProc _ _  =>
              Ko _ (Todo TDpProof_switchInnermostProc)
            | DpProof_rewritingProc _ _ _ _ _ =>
              Ko _ (Todo TDpProof_rewritingProc)
            | DpProof_instantiationProc _ _ _  =>
              Ko _ (Todo TDpProof_instantiationProc)
            | DpProof_forwardInstantiationProc _ _ _ _  =>
              Ko _ (Todo TDpProof_forwardInstantiationProc)
            | DpProof_narrowingProc _ _ _ _  =>
              Ko _ (Todo TDpProof_narrowingProc)
            | DpProof_splitProc _ _ _ _ =>
              Ko _ (Todo TDpProof_splitProc)
            | DpProof_generalRedPairProc _ _ _ _ _ _ _ =>
              Ko _ (Todo TDpProof_generalRedPairProc)
          end
      end

    (** translate rules to proj_rules in the case of AProj and in the
       case of Filter translate rules to filter_rules *)

    with argumentFilterProc n a (R D: arules a) args p {struct n} :=
      match n with
        | 0   => Ko _ (Fail FDpProof_zerobound)
        | S m =>
          match args with
            | (f, _, t) :: l' => 
              if is_collapsing t
              then AF_proj_aux R D m args p dpProof
              else
                if   conditions_AF_filter_aux a args t
                then AF_filter_aux R D m args p dpProof
                else @argumentFilterProc m a R D l' p
            | nil => Ko _ (Fail Fdp_argumentfilter_nil)
          end
      end

    (** Subterm *)
    with subtermProc n a (R D: arules a) args p {struct n} :=
      match n with
        | 0   => Ko _ (Fail FDpProof_zerobound)
        | S m => subtermProc_aux args m R D p dpProof
      end
       
    (** Dependency pair graph *)

    with depGraphProc (n : nat) a (R D : arules a) cs {struct n} :=
      match n with
        | 0   => Ko _ (Fail FDpProof_zerobound)
        | S m => depGraphProc_aux m R D cs dpProof
      end.

    Close Scope nat_scope.

    Lemma unit_ok : forall u, Ok u = OK.
    
    Proof.
      induction u. unfold OK. refl.
    Qed.

    (***********************************************************************)
    (** Correctness proof of DP:
      1. DP is empty.
      2. Rule removal of DP.
      3. Path ordering.
      4. Decomposition graph. *)

    Require Import AFilterPerm.

    Lemma dpProof_ok : forall n a (R D: arules a) dps,
          dpProof n R D dps = OK -> WF (hd_red_mod R D)
    with  argumentFilterProc_ok : forall n a (R D : arules a) a0 dps,
          argumentFilterProc n R D a0 dps = OK -> WF (hd_red_mod R D)        
    with  subtermProc_ok : forall n a (R D : arules a) af dps,
          subtermProc n R D af dps = OK -> WF (hd_red_mod R D)
    with  depGraphProc_ok: forall n a (R D: arules a) cs,
          depGraphProc n R D cs = OK -> WF (hd_red_mod R D).

    Proof.
    induction n0; try discr; simpl in *.
    (** 1. Correctness proof by using dependency pair. *)
    destruct dps; try discr.
    (** Correctness proof when the dependency pair (D) is empty. *)       
    intros H. apply pIsEmpty_ok. hyp.
    (** 2. Correctness proof of rule removal in the case of dependency
        pair method. *)
    Focus 2. destruct o; simpl in *; try discr.
    (*case_eq (color_rules a nat_of_string d); intros rs H; simpl in *;
     try discr.*)
    unfold ruleRemoval_dp.
    (* check the translation of cpf rules into color rules *)
    destruct o0; simpl in *; try discr.
    unfold redPair_dp. destruct r; simpl in *; try discr.
    case_eq (redPair_interpretation_dp R D t l);
      intros l0 H1 H2; try discr.
    (*case_eq (equiv_rules l0 rs); intros H0; rewrite H0 in H2; try discr.*)
    (* proof by applying interpretation *)
    apply redPair_interpretation_dp_ok in H1. hyp.
    eapply dpProof_ok. apply H2.      
    (** 3. Correctness proof of path ordering. *)      
    case_eq (pathOrder_dp R D l o); intros l0 H1 H2; try discr.     
    (* check the equality of rules *)
    (*case_eq (equiv_rules l0 rs); intros H0; rewrite H0 in H2; try discr.*)
    apply pathOrder_dp_ok in H1. hyp. eapply dpProof_ok. apply H2.
    (** 4. Decomposition graph. *)        
    destruct n0; try discr; simpl in *.
    unfold depGraphProc_aux.
    case_eq (conditions_depGraphProc R D); intros H0; try discr.
    case_eq (decomp a l); intros l0 H2; try discr.
    set (l1:= split_list l0).
    case_eq (equiv_rules (flat l1) D); intros H4; try discr.
    unfold third_condition.
    case_eq (valid_decomp (approx R D) l1); intros H5; try discr.
    case_eq (fourth_condition n0 R D l0 dpProof); intros H6 H7; try discr.
    eapply WF_decomp_co_scc.
    (** Over graph using a finite number of unification steps. *)
    apply dpg_unif_N_correct.
    (** [hypR: forallb (@is_notvar_lhs Sig) R = true]. *)       
    unfold conditions_depGraphProc in H0.
    do 2 rewrite andb_eq in H0. intuition.
    (** [hypD: forallb (undefined_rhs R) D = true]. *)
    unfold conditions_depGraphProc in H0.
    do 2 rewrite andb_eq in H0. intuition.       
    (** [hypD: rules_preserve_vars D]. *)       
    unfold conditions_depGraphProc in H0.
    do 2 rewrite andb_eq in H0. intuition.
    apply brules_preserve_vars_ok. hyp.       
    (** [hyp4: D [= flat cs]. *)       
    unfold equiv_rules in H4. rewrite equiv_ok in H4. apply H4.
    intros r1 r2. split. intros. rewrite ATrs.beq_rule_ok in H. hyp.
    intros. apply ATrs.beq_rule_ok. hyp.
    (** [hyp1: flat cs [= D] *)
    unfold equiv_rules in H4. apply equiv_ok in H4. apply H4.
    intros r1 r2. split. intros. rewrite ATrs.beq_rule_ok in H. hyp.
    intros. apply ATrs.beq_rule_ok. hyp.
    (** [hyp2 : valid_decomp cs = true] *)
    unfold approx in H5. apply H5.
    (** [hyp3 : lforall (fun ci => co_scc ci = true \/
         WF (hd_red_Mod S ci)) cs] *)
    clear H2 H4 H5 H7. induction l0; simpl in *; try auto.
    split. Focus 2. apply IHl0. rewrite andb_eq in H6. destruct H6.
    apply H1. rewrite andb_eq in H6. destruct H6.
    destruct a0; try discr; simpl in *.
    do 2 destruct p; try discr. destruct b; try discr.
    destruct o; try discr.
    (* proof that co_scc is true *)
    right. unfold bool_of_result in H.
    case_eq (dpProof n0 R l2 d); intros u Hdp; rewrite Hdp in H; try discr.
    eapply dpProof_ok. erewrite <- unit_ok. apply Hdp.
    (* proof a right hand side *)
    left. unfold approx in H. apply H.
    (** Correctness of depGraphProc. *)
    Focus 6. induction n0; simpl in *; try discr; auto.
    intros a R D cs.
    unfold depGraphProc_aux.
    case_eq (conditions_depGraphProc R D); intros H0; try discr.
    case_eq (decomp a cs); intros l1 H2; try discr.
    case_eq (equiv_rules (flat (split_list l1)) D); intros H3; try discr.
    unfold third_condition.
    case_eq (valid_decomp (approx R D) (split_list l1));
      intros H4; try discr.
    case_eq (fourth_condition n0 R D l1 dpProof); intros H5 H6; try discr.
    clear H6. eapply WF_decomp_co_scc.
    (** Over graph using a finite number of unification steps. *)
    apply dpg_unif_N_correct.
    (** [hypR: forallb (@is_notvar_lhs Sig) R = true] *)
    unfold conditions_depGraphProc in H0.
    do 2 rewrite andb_eq in H0. intuition.
    (** [hypD: forallb (undefined_rhs R) D = true] *)
    unfold conditions_depGraphProc in H0.
    do 2 rewrite andb_eq in H0. intuition.
    (** [hypD: rules_preserve_vars D] *)
    unfold conditions_depGraphProc in H0.
    do 2 rewrite andb_eq in H0. intuition.
    apply brules_preserve_vars_ok. hyp.        
    (** [hyp4: D [= flat cs] *)        
    unfold equiv_rules in H3. rewrite equiv_ok in H3. apply H3.
    intros r1 r2. split. intros. rewrite ATrs.beq_rule_ok in H. hyp.
    intros. apply ATrs.beq_rule_ok. hyp.
    (** [hyp1: flat cs [= D] *)
    unfold equiv_rules in H3. apply equiv_ok in H3. apply H3.
    intros r1 r2. split. intros. rewrite ATrs.beq_rule_ok in H. hyp.
    intros. apply ATrs.beq_rule_ok. hyp.
    (** [hyp2 : valid_decomp cs = true] *)
    try apply H4.
    (** [hyp3 : lforall (fun ci => co_scc ci = true 
             \/ WF (hd_red_Mod S ci)) cs] *)
    clear H2 H3 H4. induction l1; simpl in *; try auto.
    split. Focus 2. apply IHl1. rewrite andb_eq in H5.
    destruct H5. apply H1. rewrite andb_eq in H5.
    destruct H5. destruct a0; try discr.
    do 2 destruct p; try discr. destruct b; try discr.
    destruct o; try discr. right. unfold bool_of_result in H.
    case_eq (dpProof n0 R l d); intros u Hdp;
    rewrite Hdp in H; try discr. eapply dpProof_ok. erewrite <- unit_ok.
    apply Hdp. left. unfold approx in H. apply H.
    (** monoRedPairProc *)
    destruct o; simpl in *; try discr. unfold ruleRemoval_dp.
    destruct o0; simpl in *; try discr. unfold redPair_dp.
    destruct r; simpl in *; try discr.       
    (** Reduction pair interpretation in DP. *)
    case_eq (redPair_interpretation_dp R D t0 l);
      intros l0 H1 H2; try discr.
    apply redPair_interpretation_dp_ok in H1. hyp.
    eapply dpProof_ok. apply H2.
    (** Path ordering in DP. *)
    case_eq (pathOrder_dp R D l o); intros l0 H1 H2; try discr.
    apply pathOrder_dp_ok in H1. hyp. eapply dpProof_ok. apply H2.    
    (** subterm Proc *)
    destruct l; try discr; simpl in *.
    induction n0; try discr; simpl in *.
    destruct a0; try discr.
    destruct p; try discr.
    destruct p; try discr.
    (* check t is in the case of collapsing *)
    unfold subtermProc_aux.
    case_eq (is_collapsing t); intros H H1; try discr.    
    apply dpProof_ok in H1.
    eapply WF_hd_red_mod_proj. unfold color_proj_rules in H1.
    unfold color_pi_proj in H1. apply H1.
    (* another direction *)
    Focus 3.
    intros n0 a R D af dps.
    induction n0; try discr; simpl in *.
    destruct af; try discr.
    destruct p; try discr.
    destruct p; try discr.
    unfold subtermProc_aux.
    (* check that t is in the case of collapsing *)
    case_eq (is_collapsing t); intros H H1; try discr.
    apply dpProof_ok in H1. unfold color_proj_rules, color_pi_proj in H1.
    eapply WF_hd_red_mod_proj. apply H1.
    (** argument filter proc *)
    destruct n0; try discr; simpl in *.
    destruct a0; try discr. destruct p; try discr.
    destruct p; try discr.        
    (** In the case it is a collapsing. *)
    case_eq (is_collapsing t0); intros H H0; try discr.
    eapply WF_hd_red_mod_proj.
    unfold AF_proj_aux in H0.
    apply dpProof_ok in H0.
    unfold color_proj_rules, color_pi_proj in H0. apply H0.
    (** In the case of non-collapsing. *)
    revert H0.
    case_eq (conditions_AF_filter_aux a ((s, a1, t0) :: a0) t0);
      intros H0 H1; try discr.
    unfold conditions_AF_filter_aux in H0.
    rewrite andb_eq in H0. destruct H0.
    unfold AF_filter_aux in H1.
    apply dpProof_ok in H1.
    apply WF_hd_red_mod_filter with
    (pi := color_pi_filter a (List.map (pi_filter a) ((s, a1, t0) :: a0))).
    unfold non_dup. unfold color_pi_filter.
    eapply pi_filter_non_dup. apply H2.
    unfold color_filter_rules, color_filter_rule, color_pi_filter in H1.
    apply H1.
    eapply argumentFilterProc_ok. apply H1.
    (* Correctness proof of AF. *)
    induction n0; simpl in *; try discr. intros a R D af dps.
    destruct af; try discr. destruct p; try discr.
    destruct p; try discr.
    (* Collapsing is true *)
    case_eq (is_collapsing t); intros H H0; try discr.
    eapply WF_hd_red_mod_proj. apply dpProof_ok in H0.
    unfold color_proj_rules, color_pi_proj in H0. apply H0.
    (* Non-collapsing is true. *)
    revert H0.
    case_eq (conditions_AF_filter_aux a ((s, a0, t) :: af) t); intros H0 H1;
    try discr.
    unfold conditions_AF_filter_aux in H0.
    rewrite andb_eq in H0. destruct H0.
    unfold AF_filter_aux in H1.
    apply dpProof_ok in H1.
    unfold color_filter_rules, color_filter_rule, color_pi_filter in H1.
    apply WF_hd_red_mod_filter with
    (pi :=color_pi_filter a (List.map (pi_filter a) ((s, a0, t) :: af))).
    (* argument filtering does not duplicate arguments *)
    unfold non_dup. unfold color_pi_filter.
    eapply pi_filter_non_dup. apply H2. apply H1.
    eapply argumentFilterProc_ok. apply H1.
    Qed. (* take a little time *)

    (***********************************************************************)
    (** ** Dependency pair transformation *)
    (***********************************************************************)

    (** Marked symbols:
      - Without mark symbols: rewriting with the rules is not allowed
        at the root.
      - With mark symbols: the whole dp-proof is using the notion of
        chain where rewriting with the rules is applied at arbitrary
        positions (including the root). *)

    (***********************************************************************)
    (** Without marked symbols:
       - first translate cpf rules into color rules.
       - then check that the rules D is equivalence to (dp R). *)

    Definition dpTrans_unmark a (R:arules a) (dps: rules) (p: cpf.dpProof):
      result unit :=
      Match color_rules a nat_of_string dps With D ===>
      if   equiv_rules D (dp R)
      then dpProof n R D p
      else Ko _ (Fail FDPTransUnmark).

    (* TODO: string reverse REMOVE  *)
    Definition dpTrans_unmark2 a (R:arules a) (dps: rules) (p: cpf.dpProof):
      result unit :=
      (* first translate cpf rules into color rules *)
      Match color_rules a nat_of_string dps With D ===>
      (* check that the rules D is equivalence to (dp R) *)
      if   equiv_rules (reverse_trs D) (dp (reverse_trs R))
      (* if yes, then call to the function dpProof *)
      then dpProof n (reverse_trs R) (reverse_trs D) p
      (* if fail, then return an error message *)
      else Ko _ (Fail FDPTransUnmark).

    (***********************************************************************)
    (** Correctness proof of DP transformation without marked symbols. *)
      
    Lemma dpTrans_unmark_ok : forall a rs dps p
      (Hm: dpTrans_unmark rs dps p = OK)
      (* H this hypothesis used in the dpTrans function *)
      (H : forallb (is_notvar_lhs (Sig:=Sig a)) rs &&
           brules_preserve_vars rs = true), WF (red rs).

    Proof.
      intros a rs dps p Hm H. unfold dpTrans_unmark in Hm.
      case_eq (color_rules a nat_of_string dps);
        intros l H0; rewrite H0 in Hm; simpl in *; try discr.
      case_eq (equiv_rules l (dp rs)); intros H1;
      rewrite H1 in Hm; simpl in *; try discr.       
      (* Using well-founded induction on chain. *)
      apply WF_chain.
      (* No variables at the left hand side of rules [R]. *)
      rewrite andb_eq in H. destruct H. hyp.
      (* Preserve variables of rules [R]. *)
      rewrite andb_eq in H. destruct H.
      apply brules_preserve_vars_ok. apply H2.
      (* Change [chain] into [hd_red_mod rs [dp rs]]. *)       
      rewrite chain_hd_red_mod.        
      (* rs [=] dp rs *)        
      unfold equiv_rules in H1.
      rewrite equiv_ok in H1. rewrite <- H1.        
      (* Correctness proof of dpProof: WF (hd_red_mod rs l). *)
      eapply dpProof_ok. apply Hm.
      (* beq_rule. *)
      intros r1 r2. split. intro.
      rewrite ATrs.beq_rule_ok in H2; hyp.
      intro. apply ATrs.beq_rule_ok; hyp.
    Qed.
    
    (***********************************************************************)
    (** With marked symbols:
       - The arities are changed.
       - First translate cpf rules into color rules where the dp_arity is a
         function compute the arity in dp.
          + rules below R : compute the arity at below the top steps of R
          + rules top R   : compute the arity at the top of (dp R) rules
       - then check the equivalance of the new rules at top is
         equivalance with D'. *)

    Definition dpTrans_mark a (R:arules a) (dps: rules) (p:cpf.dpProof):
      result unit :=
      Match color_rules (dp_arity a) nat_of_string dps With D' ===>
      let rs  := Fl (HFSig_of_dup_Sig_eq (arity := a)) (dup_int_rules R) in
      let rs' := Fl (HFSig_of_dup_Sig_eq (arity := a)) (dup_hd_rules (dp R)) in
      if   equiv_rules D' rs'
      then dpProof n rs D' p
      else Ko _ (Fail FDPTransMark).

    (* TODO: change name marked symbols with string reverse *)

    Definition dpTrans_mark_string a (R:arules a) (dps: rules) (p:cpf.dpProof):
      result unit :=
      Match color_rules (dp_arity (ar (SSig_of_ASig (Sig a))))
      nat_of_string dps With D' ===>
      let rs := Fl (HFSig_of_dup_Sig_eq (arity := ar (SSig_of_ASig (Sig a))))
                   (dup_int_rules (reverse_trs R)) in
      let rs' := Fl (HFSig_of_dup_Sig_eq (arity := ar (SSig_of_ASig (Sig a))))
                    (dup_hd_rules (dp (reverse_trs R))) in
      if   equiv_rules (reverse_trs D') (reverse_trs rs')
      then dpProof n (reverse_trs rs) (reverse_trs D') p
      else Ko _ (Todo Todo1). (* TODO: change message *)

    (***********************************************************************)
    (** Correctness proof of dpTrans with marked symbols .*)

    Lemma dpTrans_mark_ok : forall a rs dps p
      (Hm: dpTrans_mark rs dps p = OK)
      (H : forallb (is_notvar_lhs (Sig:=Sig a)) rs      &&
           forallb (is_notvar_lhs (Sig:=Sig a)) (dp rs) &&
           forallb (is_notvar_rhs (Sig:=Sig a)) (dp rs) && 
           brules_preserve_vars rs = true), WF (red rs).

    Proof.
      intros a rs dps p Hm H.
      unfold dpTrans_mark in Hm.
      case_eq (color_rules (dp_arity a) nat_of_string dps); intros l H0;
      rewrite H0 in Hm; try discr.
      case_eq (equiv_rules l (Fl (HFSig_of_dup_Sig_eq (arity:=a))
              (dup_hd_rules (dp rs)))); intros H1;
      rewrite H1 in Hm; try discr.
      (* Proving well-founded chain: need to prove two assumptions:
           [no_var_lhs R] and [rules_preserve_vars R]. *)
      apply WF_chain.
      (* No variable at the left hand side of the rules [R]. *)
      do 3 rewrite andb_eq in H. destruct H. apply H.
      (* Preserve variables of rules [R]. *)       
      rewrite andb_eq in H. destruct H.
      apply brules_preserve_vars_ok. apply H2.
      (* Preservation of termination by marking. *)        
      apply WF_duplicate_hd_int_red.        
      (* No variable on the left hand side of [dp R]. *)        
      do 3 rewrite andb_eq in H. do 3 destruct H. hyp.        
      (* No variable on the right hand side of [dp R]. *)
      do 3 rewrite andb_eq in H. do 3 destruct H. hyp.
      (* rs [=] dp rs. *)       
      unfold equiv_rules in H1. intuition. apply equiv_ok in H1.
      apply Fhd_red_mod_WF_fin with (HF:= HFSig_of_dup_Sig_eq (arity:=a)).
      apply dpProof_ok in Hm. rewrite <- H1. apply Hm.
      (* beq_rule *)        
      intros r1 r2. split.
      intros. apply ATrs.beq_rule_ok in H2. apply H2.
      intros. rewrite ATrs.beq_rule_ok. apply H2.
    Qed.

    (***********************************************************************)
    (** Conditions of DP transformation:
       - check that there is no variable on the left-hand side of R
       - check that there is no variable on the right-hand side of (dp R)
       - check that the variables in R is preserve. *)

    Definition conditions_dpTrans a (R: arules a):=
      forallb (@is_notvar_lhs (Sig a)) R      &&
      forallb (@is_notvar_lhs (Sig a)) (dp R) &&
      forallb (@is_notvar_rhs (Sig a)) (dp R) &&
      brules_preserve_vars R.

    (* REMOVE DP with/without marked symbols. *)

    Definition dpTrans a (R:arules a) (dps: rules) (b:bool)(p: cpf.dpProof):
      result unit :=
      if conditions_dpTrans R
      then
        if   b
        (* if b is set to [true] then it is a marked symbol. *)
        then dpTrans_mark R dps p
        (* if b is set to [false] then it is an unmarked symbol. *)
        else dpTrans_unmark R dps p
      else   Ko _ (Fail FDPTrans).

    (* Define conditions of string reverse *)

    Definition condition_string_reverse a (R: arules a) ls :=
      forallb (fun x : {f : symbol & nat} =>
                 let (f, s) := x in beq_nat 1 (a f)) ls.

    (* TODO: DP with/without marked symbols combination with string
    reverse *)

    Definition dpTrans_combine a (R:arules a) (dps: rules) (b:bool)
      (p: cpf.dpProof) : result unit :=
      Match map (color_unary a) dps With ls ===>
      if conditions_dpTrans R
      then
        if   b
        then if   condition_string_reverse R ls
             then dpTrans_mark_string (reverse_trs R) dps p (* string reveser *)
             else dpTrans_mark R dps p
        else   dpTrans_unmark R dps p
      else   Ko _ (Fail FDPTrans).
    
    (***********************************************************************)
    (** Correctness proof of DP transformation *)

    (* FIXME: change to proof dpTrans_combine *)

    Lemma dpTrans_ok : forall a (R: arules a) dps b p,
      dpTrans R dps b p = OK ->  WF (red R).

    Proof.
      intros a rs dps b p Hm. unfold dpTrans in Hm.
      case_eq (conditions_dpTrans rs); intro H; rewrite H in Hm;
      try discr.
      destruct b; try discr.
      (* Proving dependency pair where symbols are marked. *)       
      apply dpTrans_mark_ok with (dps:=dps)(p:=p).
      apply Hm.
      (* Prove conditions *)
      unfold conditions_dpTrans in H.
      apply H.
      (* Proving dependency pair where symbols are not marked. *)        
      apply dpTrans_unmark_ok with (dps:=dps)(p:=p).
      apply Hm.
      (* Prove conditions *)
      unfold conditions_dpTrans in H.
      do 3 rewrite andb_eq in H. rewrite andb_eq. intuition.
    Qed.

  End Top_Termination.

  (***********************************************************************)
  (** ** Check that [R] is a trivial proof by stating the set of rules
   [R] is empty valid termination proof for [red R]. *)
  (***********************************************************************)
    
  Definition rIsEmpty a (R: arules a) :=
    if is_empty R then OK else Ko _ (Error ErNotEmpty).
    
  Lemma rIsEmpty_ok : forall a (R: arules a), rIsEmpty R = OK -> WF (red R).
    
  Proof.
    intros a R. unfold rIsEmpty. destruct R; simpl; intro.
    apply WF_red_empty. discr.
  Qed.
    
  (***********************************************************************)
  (** ** Check that [R] is a trivial proof by stating the set of rules
      [R] is empty valid termination proof for [red R]. *)
  (***********************************************************************)
  
  Definition relTerminationProof_rIsEmpty a (D : arules a) :=
    if is_empty D then OK else Ko _ (Error ErNotEmptyrIsEmpty).
    
  Lemma relTerminationProof_rIsEmpty_ok : forall a (R D: arules a),
    relTerminationProof_rIsEmpty D = OK -> WF (red_mod R D).
    
  Proof.
    intros a R D. unfold relTerminationProof_rIsEmpty.
    destruct D; simpl; intro. apply WF_red_mod_empty. discr.
  Qed.

  (***********************************************************************)
  (** ** Check that [p] is a valid termination proof for [red R]
    - [rIsEmpty] : state that the TRS is terminating since it has no
     rules.
     - [ruleRemoval]: use a reduction pair where both the weak and the
     strict ordering are monotone. Delete all strictly decreasing
     rules. The remaining rules have to be given. If the ordering
     constraint proof is only an assumption, the
     orderingConstraints-element becomes mandatory.
     - [dpTrans]: switch to dependency pairs. The dependency pairs
     have to be given. If marked is true, then the whole dp-proof is
     using a notion of chain where rewriting with the rules is applied
     at arbitrary positions (including the root). Otherwise, rewriting
     with the rules is not allowed at the root.
     - [stringReversal]: reverse the strings in both TRSs R and S,
      i.e., replace f(g(h(x))) -&gt; f(x) by h(g(f(x))) -&gt; f(x).
      Note that the variable in a reversed rule should be same as the
      variable in the original rule.
     Proving string reversal require two assumptions: AReverse.v:
     [WF_red_rev_eq]
     - Variables are preserve [brules_preserve_vars]
     - A signature with unary symbols is true [bis_unary].*)

  Require Import AFlatCont.

  Open Scope nat_scope.

  Variable uni: nat.

  (* REMOVE Define conditions of string reverse *)

  Definition conditions_string_reverse a (R: arules a) ls :=
    brules_preserve_vars R &&
    forallb (fun x : {f : symbol & nat} =>
    let (f, s) := x in beq_nat 1 (a f)) ls.

  Fixpoint trsTerminationProof n a (R: arules a) p :=
    match n with
      | 0 => Ko _ (Fail FtrsTerminationProof_zerobound)
      | S m =>
        match p with
          | TrsTerminationProof_rIsEmpty => rIsEmpty R
          | TrsTerminationProof_ruleRemoval (Some _) _ _ _ =>
            Ko _ (Todo TTrsTerminationProof_ruleRemoval)
          | TrsTerminationProof_ruleRemoval None ocp rs p  =>
            Match color_rules a nat_of_string rs With rs' ===>
            Match ruleRemoval R ocp With R' ===>
            (* Check R' [=] rs and in the case of string reverse *)
            if   equiv_rules R' rs' || equiv_rules (reverse_trs R')
                 (reverse_trs rs')
            then trsTerminationProof m R' p
            else Ko _ (Todo Todo1)
          | TrsTerminationProof_dpTrans dps b dp =>
            (*dpTrans_combine uni R dps b dp*)
            dpTrans uni R dps b dp
             (*dpTrans uni (reverse_trs R) dps b dp*)
          | TrsTerminationProof_semlab _ _ _ _ => (* TODO *)
            Ko _ (Todo TTrsTerminationProof_semlab)
          | TrsTerminationProof_unlab rs p => (* TODO*)
            Ko _ (Todo TTrsTerminationProof_unlab)
          | TrsTerminationProof_stringReversal rs p =>
            string_reverse m R rs p
          | TrsTerminationProof_flatContextClosure cs r p => (* TODO *)
          (* Ko _ (Todo TTrsTerminationProof_flatContextClosure)*)
            flat_context m R r p
          | TrsTerminationProof_terminationAssumption _ =>
            Ko _ (Todo TTrsTerminationProof_terminationAssumption)
          | TrsTerminationProof_uncurry _ _ _ =>
            Ko _ (Todo TTrsTerminationProof_uncurry)
          | TrsTerminationProof_bounds _ _ _ _ =>
            Ko _ (Todo TTrsTerminationProof_bounds)
          | TrsTerminationProof_switchInnermost _ _ =>
            Ko _ (Todo TTrsTerminationProof_switchInnermost)
          | TrsTerminationProof_split _ _ _ =>
            Ko _ (Todo TTrsTerminationProof_split)
          | TrsTerminationProof_removeNonApplicableRules _ _ =>
            Ko _ (Todo TTrsTerminationProof_removeNonApplicableRules)
        end
    end

  (** String reverse: transform R into R^[-1] *)

  with string_reverse n a (R: arules a) rs p :=
         match n with
           | 0   => Ko _ (Fail FtrsTerminationProof_zerobound)
           | S m =>
             Match map (color_unary a) rs With ls ===>
             (* Check rs [=] reverse_trs R *)
             (*Match color_rules a nat_of_string rs With rs ===>*)
             if   conditions_string_reverse R ls
             then trsTerminationProof m (reverse_trs R) p
             else Ko _ (Fail Fstring_reverse)
         end

  (** Flat context *)

  with flat_context n a (R:arules a) rs p :=
         match n with
           | 0 => Ko _ (Fail FtrsTerminationProof_zerobound)
           | S m =>
             (* TODO condition (hyp : n >= maxvar_rules R).
                check the arguments *)
             let max_rules := maxvar_rules R in
             let ls :=  symbol_in_rules rs in
             trsTerminationProof m (@flat_rules (Sig a) max_rules ls R) p
         end.

  (***********************************************************************)
  (** Correctness proof of termination proof:
      - trs proof
      - string reverse 
      - flat context *)

  Lemma ruleRemoval_ok : forall a (R R': arules a) (ocp:  orderingConstraintProof),
                        ruleRemoval R ocp = Ok R' -> WF (red R') -> WF (red R).

   Proof.
     intros.
   Admitted.


  Lemma trsTerminationProof_ok : forall n a (R: arules a) t,
        trsTerminationProof n R t = OK -> WF (red R)
  with  string_reverse_ok : forall n a (R: arules a) rs p,
        string_reverse n R rs p = OK -> WF (red R)
  with  flat_context_ok : forall n a (R: arules a) rs p,
        flat_context n R rs p = OK -> WF (red R).

  Proof.
    induction n0; try discr; simpl in *.
    destruct t; try discr.
    (** 1. TRS is empty *)
    apply rIsEmpty_ok.
    (** 2. Rule removal *)
    destruct o; try discr.
    (* translate cpf rules into color rules *)
    case_eq (color_rules a nat_of_string t); intros rs H1; try discr.
    (* apply rule removal, remove all ordering [>=] in R *)
    intros Hm. unfold ruleRemoval in Hm.
    destruct o0; try discr. unfold redPair in Hm.
    (* difference methods of redpair *)
    destruct r; try discr.
    (* first case is apply interpretation methods *)
    revert Hm.
    case_eq (redPair_interpretation R t1 l); intros l0 H Hm; 
    try discr.
    (* testing rules equality *)
    case_eq (equiv_rules l0 rs || equiv_rules (reverse_trs l0) (reverse_trs rs));
      intro H2; rewrite H2 in Hm; try discr.
    (* apply correctness proof in the case of interpretation *)
    eapply redPair_interpretation_ok.
    apply H. eapply IHn0. apply Hm.  
    (** 3. Correctness proof of termination proof in the case of
          path ordering. *)
    revert Hm.
    case_eq (pathOrder R l o); intros l0 H Hm; try discr.
    case_eq (equiv_rules l0 rs || equiv_rules (reverse_trs l0) (reverse_trs rs));
      intro H2; rewrite H2 in Hm; try discr.
    (* apply correctness proof of path ordering *)
    eapply pathOrdering_ok. apply H. eapply IHn0. apply Hm.

    (** 4. Correctness proof of dependency pair transformation
          method with and without mark symbol. *)
    
    eapply dpTrans_ok.

    (* TODO section: string reverse and flat context closure *)

    (** TODO: 5. String reverse *)
    destruct n0; try discr; simpl in *.
    (*case_eq (brules_preserve_vars R && bis_unary (Sig a) (symbol_in_rules t));
      try discr; intros H H0.*)
    case_eq (map (color_unary a) t);
      intros ls H H1; simpl in *; try discr.
    revert H1.
    case_eq (conditions_string_reverse R ls); intros; try discr.
    (* Proof the wf of reverse trs *)
    apply WF_red_rev_eq.

    (* is_unary *)
    unfold is_unary. erewrite color_bis_unary_ok.
    Focus 2. unfold conditions_string_reverse in H0.
    rewrite andb_eq in H0. destruct H0.
    apply H2.
 
    (* TODO: need to formalize is_unary *)

    Focus 2.
    rewrite <- brules_preserve_vars_ok.
    unfold conditions_string_reverse in H0. rewrite andb_eq in H0.
    destruct H0. apply H0.
    Focus 2.
    eapply trsTerminationProof_ok in H1. hyp.

    (* TODO: 6: Flat context closure *)
    Focus 2.
    induction n0; try discr; simpl in *.
    intro H. rewrite WF_red_flat. apply trsTerminationProof_ok in H.
    apply H.

    (* FIXME *)

    (* TODO: correctness of proof the string reverse *)

    (*
    induction n0; try discr; simpl in *.
    intros a R rs p.
    case_eq (brules_preserve_vars R && bis_unary (Sig a) (symbol_in_rules rs));
      try discr; intros H H0.
    rewrite andb_eq in H. destruct H.
    apply WF_red_rev_eq.
    Focus 2. rewrite <- brules_preserve_vars_ok. apply H.
    Focus 2. eapply trsTerminationProof_ok in H0. apply H0.*)
    (* TODO proof the last case of is_unary *)

  Admitted.

    (***********************************************************************)
    (** ** Check that [p] is a valid non-termination proof for [red R]. *)
    (***********************************************************************)    
  
    (** Check that [R] is a violation of variable condition, it
     means there is a rule where the [lhs] is a variable, or the [rhs]
     contains variables not occuring in the [lhs] (it is in the
     definition of rewrite rule). 
     
     Definition: A pair [(l,r)] of terms is a rewrite rule if [l] is
     not a variable and [var(l) \subseteq var(r)]. *)
    
    Definition variableConditionViolated a (R : arules a) := 
      if   brules_preserve_vars R
      then Ko _ (Error ErNotVariableConditionViolated)
      else OK.

    Lemma variableConditionViolated_ok: forall a (R: arules a),
       variableConditionViolated R = OK -> EIS (red R).
    
    Proof.
      intros a R H.
      unfold variableConditionViolated in H.
      case_eq (brules_preserve_vars R);
        intros H1; rewrite H1 in H; try discr.
      apply var_cond.
      rewrite <- brules_preserve_vars_ok.
      rewrite <- false_not_true. apply H1.
    Qed.

    (***********************************************************************)
    (** Non termination proof: LOOP. *)
    
    Require Import ALoop.
    
    Import error_monad.

    (* FIXME *)

    Definition loop a (R: arules a) (lo: cpf.loop) : result unit :=
      let '((t, ls), _, c) := lo in
      Match color_term a nat_of_string t          With t  ===>
      Match color_rewriteSteps nat_of_string a ls With ds ===>
      let  pos := color_position_of_context c in
      if   is_loop R t ds pos
      then OK
      else Ko _ (Fail FtrsNonTerminationProof_loop).
    
    (***********************************************************************)
    (** Correctness proof of loop *)

    Lemma loop_ok: forall a (R: arules a) l, loop R l = OK -> EIS (red R).

    Proof.
      intros a R l Hm. unfold loop in Hm.
      destruct l; simpl; try discr.
      destruct p; simpl; try discr.
      destruct r; simpl; try discr.
      case_eq (color_term a nat_of_string t);
        intros t1 H; rewrite H in Hm; try discr.
      case_eq (color_rewriteSteps nat_of_string a l);
        intros ds H0; rewrite H0 in Hm; try discr.
      case_eq (is_loop R t1 ds (color_position_of_context c));
        intros H1; rewrite H1 in Hm; try discr.
      set (ps:= color_position_of_context c).
      apply is_loop_correct with (t:=t1)(ds:=ds)(p:=ps).
      apply H1.   
    Qed.

    (***********************************************************************)
    (** ** Non-Termination problems *)

    Definition trsNonTerminationProof a (R: arules a) p : result unit :=
      match p with
        | TrsNonterminationProof_variableConditionViolated  =>
          variableConditionViolated R
        | TrsNonterminationProof_ruleRemoval _ _            =>
          Ko _ (Todo TTrsNonterminationProof_ruleRemoval)
        | TrsNonterminationProof_stringReversal _ _         =>
          Ko _ (Todo TTrsNonterminationProof_stringReversal)
        | TrsNonterminationProof_loop (((_, nil), _), _)    =>
          Ko _ (Todo TTrsNonterminationProof_loop_nil)
        | TrsNonterminationProof_loop lo                    => loop R lo
        | TrsNonterminationProof_dpTrans _ _ _              =>
          Ko _ (Todo TTrsNonterminationProof_dpTrans)
        | TrsNonterminationProof_nonterminationAssumption _ =>
          Ko _ (Todo TTrsNonterminationProof_nonterminationAssumption)
        | TrsNonterminationProof_innermostLhssIncrease _ _  =>
          Ko _ (Todo TTrsNonterminationProof_innermostLhssIncrease)
        | TrsNonterminationProof_nonLoop _                  =>
          Ko _ (Todo TTrsNonterminationProof_nonLoop)
      end.
    
    (***********************************************************************)
    (** Correctness proof of Non-Termination problems *)

    Lemma trsNonTerminationProof_ok: forall a (R: arules a) l,
      trsNonTerminationProof R l = OK -> EIS (red R).
    
    Proof.
      intros a R l Hm. unfold trsNonTerminationProof in Hm.
      destruct l; simpl; try discr.
      (* Variable *)
      apply variableConditionViolated_ok. apply Hm.
      destruct l; simpl; try discr.
      destruct p; simpl; try discr.
      destruct r; simpl; try discr.
      destruct l; simpl; try discr.
      (* Loop *)
      eapply loop_ok. apply Hm.
    Qed.

End Top.