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
  cpf_util cpf2color AWFMInterpretation cpf Z_as_SR.

Section Top.

  (* Convert a string of [var] in cpf into a natural numbers. *)

  Variable nat_of_string : string -> nat.

  (* Assume the varibale [bb] of rpo. *)

  Variable rpo_n : nat.

  (* Extra argument for function [dpProof], decreasing argument in a
  Fixpoint. *)

  Variable n : nat.

  (**************************************************************************)

  Section S.

    (* Checking all symbols in a Signature. *)

    Variable arity : symbol -> nat.

    Notation aterm := (aterm arity).
    Notation arule := (arule arity).
    Notation arules := (arules arity).
    Notation abrule := (abrule arity).
    
    Implicit Type R : arules.
    
    (**************************************************************************)
    (** ** Check that [p] is a valid termination proof for [red R].           *)
    (**************************************************************************)
    
    Section Full_Termination.
            
      Notation Sig := (Sig arity).
      
      Section poly.
        
        (**********************************************************************)
        (** Polynomial interpretation over domain natural numbers.

         Conditions for polynomial interpretation over natural numbers
         to be monotone; such polynomials are weakly monotone
         (coefficients are natural numbers), to obtain strict
         monotonicity we must require that every variable occurs
         positively. This problem is undecidable in general. The
         comparision of polynomials amounts to the positiveness check
         where we consider: [Pn(x) - Qn(x) - 1]. It states that
         evaluation of a polynomial is always greater [resp. greater
         or equal] than [0] iff all of its coefficients are
         non-negative and the constanst factor is positive.
     
         To prove the termination of some rewrite system, the
         polynomial interpretation must satisfy two conditions:
     
         [1.] First, check that interprets can be translated into
         polynomials with a number of variables less than the arity of
         the corresponding function symbols.
     
         [2.] Second, check that coefficients are non-negative (=>
         polynomials are monontone). 

         Remark: this function use to test for full termination and
         relative termination. *)

        Import OSR_Notations.

        Definition poly_nat (is: list (symbol * cpf.arity * function)) :
          result ((aterm -> aterm -> bool) * (aterm -> aterm -> bool)) :=
          Match map_rev (@color_interpret arity coef_ring_Z) is With l ===>
           if forallb (fun x        =>
             match x with 
               existT f p           => bcoef_not_neg p
             end) l &&
               forallb (fun x       =>
                 match x with
                   existT f p       =>
                     forallb (fun x => or_bgt (coef (mxi (prf x)) p) 0)
                                      (mk_nat_lts (arity f))
                 end) l
            then
             let pi := fun f : Sig   => fun_of_pairs_list arity f l in
               Ok ((fun t u          => bcoef_not_neg
                    (@rulePoly_ge _ Sig pi (mkRule t u))), 
                  (fun t u           => bcoef_not_neg
                    (@rulePoly_gt _ Sig pi (mkRule t u))))
             else Ko _ (Error ENotMonotone).

      (************************************************************************)
      (** Correctness of polynomial interpretation of domain natural numbers.
       REMARK: use function [I] in APolyInt_MA1. *)

      Require Import APolyInt_MA2.

      Lemma poly_nat_ok : forall (R R': arules) is
        (h: match poly_nat is with
             | Ok (bsucc_ge, bsucc_gt) =>
               if   forallb (brule bsucc_ge) R
               then Ok (filter (brule (neg bsucc_gt)) R)
               else Ko arules (Error ERuleNotInLargeOrdering_poly)
             | Ko e                    => Ko arules e
            end = Ok R')
         (wf: WF (red R')), WF (red R).
      
      Proof.
        intros R R' is h wf.

        case_eq (poly_nat is); intros p H; rewrite H in h; try discr.

        (* Declare [bge bgt]. *)

        destruct p as [bge bgt].

        case_eq (forallb (brule bge) R); intro H0; rewrite H0 in h;
        try discr.

        (* bgt \in R = R' *)

        inversion h. subst R'. clear h.

        unfold poly_nat in H. revert H.

        case (map_rev (color_interpret arity) is); intros l H; try discr.

        (*COQ: case_eq (forallb (fun x : {H : symbol & poly (arity H)}
          => let (x0, p) := x in bcoef_pos p && forallb (fun x0 :
          nat_lt (arity f) => is_pos (coef (mxi (prf x0)) p))
          (mk_nat_lts (arity f))) l) does not work! *)

         gen H.

         set (b:= forallb (fun x : {f : symbol & poly (arity f)} => let
          (f, p) := x in bcoef_not_neg p) l && forallb (fun x : {f :
          symbol & poly (arity f)} => let (f, p) := x in forallb (fun
          x0 : nat_lt (arity f) => or_bgt (coef (mxi (prf x0)) p)
          sr_0) (mk_nat_lts (arity f))) l).

          case_eq b; intros H2 H3; subst b; try discr.

          inversion H3. clear H3.

          set (trsInt := fun f: symbol => fun_of_pairs_list arity f l).

          cut (forall f: symbol, pweak_monotone (trsInt f)).

          intro trsInt_wm.

          (** Proving [WF (red R)] by redPair interpretation *)

          rewrite andb_eq in H2. destruct H2.

          apply WF_rp_red with (WP := @WP _ _ l H1).

          (** A proof of [>] are closed by context: IR_context_closed. *)

          change (context_closed (IR (@I Sig _ (TPolyInt_poly arity l H1)) succ)).

          apply IR_context_closed. apply pi_monotone.

          simpl. intro f.

          (** Polynomial is strong monotone. *)

          apply trsInt_pw_poly. rewrite andb_eq. split. hyp. hyp.

          (** Check that all rules [R] are included in [>=]. *)

          simpl; unfold brule, bsucceq, bool_of_rel; simpl.

          rewrite forallb_forall. intros x Hx. subst bge.

          rewrite forallb_forall in H0. ded (H0 x Hx). destruct x as [t u].
          
          simpl in *.

          case_eq (succeq'_dec Sig (TPolyInt_poly arity l H1) t u);
            intros s Hs. auto.

          unfold brule in H3. unfold succeq' in s.

          rewrite bcoef_not_neg_ok in H3. contradiction.
        
          (** Remove all rules [R] are included in [>]. *)
        
          apply WF_incl with (S:=red (filter (brule (neg bgt))R)).

          unfold inclusion. intros t u H7. redtac. unfold red.

          exists l0. exists r. exists c. exists s. intuition.

          apply filter_In. apply filter_In in lr. intuition.

          unfold brule, neg. unfold brule, neg in H6. simpl in *.

          unfold bsucc, bool_of_rel in H6. simpl in *.

          destruct succ'_dec in H6. discr.

          unfold succ' in n0. rewrite <- bcoef_not_neg_ok in n0.

          apply eq_true_not_negb in n0.

          subst bgt. apply n0. hyp.

          (** Proving polynomial is weak monotone. *)
        
          intro f. apply trsInt_wm_poly. rewrite andb_eq in H2.

          destruct H2. hyp.
      Qed.

      (***********************************************************************)
      (** Polynomial interpretation over domain natural numbers.
   
       Given a positive real number [delta] \in R_>0, a well-founded and
       stable (strict) ordering [>_delta] on terms is defined as
       follows: for all [t, s \in T(F, V), t >_delta s] if and only if
       [[t] - [s] >=_R delta].
       
       - [delta > 0]
       - rulePoly_gtQ x y : P_x - P_y - delta >= 0. *)
      
      Require Import Q_as_R QArith APolyInt2.

      Open Scope Q_scope.

      Definition poly_rat (is: list (symbol * cpf.arity * function)) (del:Q) :
        result ((aterm -> aterm -> bool) * (aterm -> aterm -> bool)) :=
        Match map_rev (@color_interpret arity coef_ring_Q) is With l ===>
          if forallb (fun x       =>
            match x with
              existT f p          => bcoef_not_neg p
            end) l &&
             forallb (fun x       =>
               match x with
                 existT f p       =>
                   forallb (fun x => or_bgt (coef (mxi (prf x)) p)0)
                                     (mk_nat_lts (arity f))
               end) l
          then
           let pi := fun f : Sig => fun_of_pairs_list arity f l in
             Ok ((fun t u        => bcoef_not_neg
                 (@rulePoly_ge Q_as_OR Sig pi (mkRule t u))),
               (fun t u          => bcoef_not_neg
                 (@rulePoly_gtQ Q_as_OR Sig pi del (mkRule t u))))
          else Ko _ (Error ENotMonotone_rat).    

      (*******************************************************************)      
      (** Define polynomial interpretation over domain rational numbers. *)

      Definition type_poly_rationals del is :=
        match del with
          | Number_integer i      => poly_rat is (inject_Z i) (* i/1 *)
          | Number_rational i pos => let q := Qmake i pos in
                                     poly_rat is q
        end.
      
      (************************************************************************)
      (** Correctness proof of polynomial interpretation over domain
      rational numbers. *)

      (** This is a common proof for polynomial of type rational
      number. *)
      
      Lemma poly_rat_comm_ok : forall (R R' : arules) del is
        (h:match poly_rat is del with
             | Ok (bsucc_ge, bsucc_gt) =>
               if forallb (brule bsucc_ge) R
               then Ok (filter (brule (neg bsucc_gt)) R)
               else Ko arules (Error ERuleNotInLargeOrdering_poly)
             | Ko e                    => Ko arules e
           end = Ok R')(wf:WF (red R')), WF (red R).
    
      Proof.
        intros R R' del is h wf.

        case_eq (poly_rat is del);
          intros p H1; rewrite H1 in h; try discr.
        
        destruct p as [bge bgt].

        case_eq (forallb (brule bge) R); intro H2; rewrite H2 in h;
        try discr.

        inversion h. subst R'. clear h.

        unfold poly_rat in H1.

        case_eq (map_rev (color_interpret arity) is); intros l H3;
        rewrite H3 in H1; try discr.

        gen H1.

        set (b:= forallb
         (fun x : {f : symbol & poly (arity f)}    =>
          let (f, p) := x in
            bcoef_not_neg p) l &&
         forallb
           (fun x : {f : symbol & poly (arity f)}  =>
            let (f, p) := x in
            forallb
              (fun x0 : nat_lt (arity f)           =>
                @or_bgt Q_as_OR (coef (mxi (prf x0)) p) 0)
          (mk_nat_lts (arity f))) l).

        case_eq b; intros H4 H5; subst b; try discr.

        inversion H5. clear H5.

        set (trsInt:=fun f : symbol => fun_of_pairs_list arity f l).

        cut (forall f: Sig, pweak_monotone (trsInt f)).

        intro trsInt_wm.
        
        (** Proving polynomial is weak monotone. *)

        Focus 2. intro f. apply trsInt_wm_poly.

        rewrite andb_eq in H4. destruct H4. hyp.

        rewrite andb_eq in H4. destruct H4.

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

        rewrite forallb_forall in H2. ded (H2 x Hx). destruct x as [t u].

        simpl in *.

        case_eq (succeq'_dec Sig (TPolyInt_poly arity l H) t u);
          intros s Hs. auto.

        unfold brule in H0. unfold succeq' in s.

        rewrite bcoef_not_neg_ok in H0. contradiction.

        (** Remove all rules [R] are included in [>]. *)
        
        apply WF_incl with (S:=red (filter (brule (neg bgt))R)).

        unfold inclusion. intros t u H7. redtac. unfold red.

        exists l0. exists r. exists c. exists s. intuition.

        apply filter_In. apply filter_In in lr. intuition.

        unfold brule, neg. unfold brule, neg in H7. simpl in *.

        unfold bsucc, bool_of_rel in H7. simpl in *.

        destruct succQ'_dec in H7. discr.

        unfold succQ' in n0. rewrite <- bcoef_not_neg_ok in n0.

        apply eq_true_not_negb in n0.

        subst bgt. apply n0. hyp.
      Qed.

      (************************************************************************)
      (** 1.b. Correctness proof of polynomial interpretation over
      domain rational numbers. *)

      Lemma poly_rat_ok : forall n (R R': arules) is
       (h:  match type_poly_rationals n is with
              | Ok (bsucc_ge, bsucc_gt) =>
                if forallb (brule bsucc_ge) R
                then Ok (filter (brule (neg bsucc_gt)) R)
                else Ko arules (Error ERuleNotInLargeOrdering_poly)
              | Ko e                    => Ko arules e
            end = Ok R')(wf: WF (red R')), WF (red R).

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
          | Domain_integers               => Ko _ (Todo Ttype_polynomialDomain_integers)
          | Domain_rationals del          => type_poly_rationals del is
          | Domain_arctic dom'            => Ko _ (Todo Ttype_polynomialDomain_arctic)
          | Domain_tropical dom'          => Ko _ (Todo Ttype_polynomialDomain_tropical)
          | Domain_matrices dim sdim dom' => Ko _ (Todo Ttype_polynomialDomain_matrices)
        end.

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
          | Ok (bsucc_ge, bsucc_gt) =>
            if   forallb (ATrs.brule bsucc_ge) R
            then Ok (filter (ATrs.brule (neg bsucc_gt)) R)
            else Ko _ (Error ERuleNotInLargeOrdering_poly)
          | Ko e                    => Ko _ e
        end.

      (************************************************************************)
      (** Relative termination use polynomial interpretation over
          domain natural and rational numbers.
          Given a pair (>=, >) is a reduction pair.
          if the orders are weakly decreasing in R and D,
          then remove all strictly decreasing in R and D,
          otherwise return error message.
       *)

      Definition rel_polynomial_interpretation (R D: arules) is dom : result arules :=
        match type_polynomial is dom with
          | Ok (bsucc_ge, bsucc_gt) =>
            if   forallb (ATrs.brule bsucc_ge) R &&
                 forallb (ATrs.brule bsucc_ge) D
            then Ok (filter (ATrs.brule (neg bsucc_gt)) D) (*(R ++ D))*)
            (* TODO: filter R. *)
            else Ko _ (Error ERuleNotInLargeOrdering_poly)
          | Ko e                    => Ko _ e
        end.

    End poly.

    (**************************************************************************)
    (** ** Matrix interpretation over domain natural number *)

    (** Matrix interpretation over domain natural numbers:
       given a pairs of relations ([>], [>=]), such that [>] is
       well-founded, the orders are compatible.
       
       - For the interpretation [f] of a symbol [f \in Signature] of arity
       [n>=1] we choose [n] matrices [M1, M2,..., Mn] over [N], each of size
       [dxd], such that the upper left elements [Mi(1,1)] are positive for
       all [i=1,2,...,n] and a vector [c \in N^d].
       
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

      Require Import AMatrixBasedInt2 Matrix2 OrdSemiRing2 AMatrixInt2 Nat_as_OSR.     
      
      Open Scope nat_scope.

      Section matrix_nat.
        
        (************************************************************************)

        Section weakRedPair_matrix_nat.

          (* Declare dimension as a variable to be able to use it in the
          matrix_nat function. *)

          Variable dim : nat.
          Notation dim_pos := (dim_pos dim).
          Notation mint := (@matrixInt _ dim).
          
          Variable l: list {g: symbol & mint (arity g)}.
          
          Definition TMatrix_Mon_Nat    := @MonotoneAlgebra Sig dim
                                          (@TMatrix_Int arity dim coef_sring_N l).
          Definition WP_Matrix_Nat      := @WP_MonAlg Sig TMatrix_Mon_Nat.
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
            intros.
            unfold id_matrix in H0. unfold VecArith2.id_vec in H0.
          Admitted.
          
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
   
        (************************************************************************)
        (** Matrix interpretation of domain natural numbers. 
          REMARK: use relation [bgt]. *)

        Definition matrix_nat (is: list (symbol * cpf.arity * function))(dim: nat):
          result ((aterm -> aterm -> bool) * (aterm -> aterm -> bool)) :=
          Match map_rev (@color_interpret_matrix arity dim coef_sring_N) is With l ===>
            if forallb (fun x =>
              match x with
                existT f mi   => bVforall
                 (fun m       => bgt Nat_as_OSR (get_elem m (dim_pos dim) (dim_pos dim)) 0)
                                 (args mi)
              end) l
            then
              let Conf := TMatrix_Conf l in
                Ok (fun t u   => let (l, r) :=
                     @rule_mi _ _ dim Conf (mkRule t u) in bmint_ge l r,
                   (fun t u   => let (l, r) :=
                     @rule_mi _ _ dim Conf (mkRule t u) in bmint_gt_nat l r))
             else Ko _ (Error ENotMonotone_matrix_naturals).

      (*************************************************************************)
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
          | Domain_integers               => Ko _ (Todo Ttype_polynomialDomain_integers)
          | Domain_rationals delta        => Ko _ (Todo Ttype_polynomialDomain_rationals)
          | Domain_arctic dom'            => Ko _ (Todo Ttype_polynomialDomain_arctic)
          | Domain_tropical dom'          => Ko _ (Todo Ttype_polynomialDomain_tropical)
          | Domain_matrices dim sdim dom' => Ko _ (Todo Ttype_polynomialDomain_matrices)
        end.

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
       other technique for proving (relative) termination. *)
      
      Definition matrix_interpretation (R: arules) is dom dim: result arules :=
        match type_matrix is dom dim with
          | Ok (bsucc_ge, bsucc_gt) =>
            if   forallb (ATrs.brule bsucc_ge) R
            then Ok (filter (ATrs.brule (neg bsucc_gt)) R)
            else Ko _ (Error ERuleNotInLargeOrdering_matrix_naturals)
          | Ko e                    => Ko _ e
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

        case_eq (forallb (ATrs.brule bge) R); intro H0;
        rewrite H0 in h; try discr.

        inversion h. subst R'. clear h.

        unfold matrix_nat in H. revert H.

        case (map_rev (color_interpret_matrix arity (Pos.to_nat d)) is);
          intros l H1; try discr.

        gen H1.

        set (b:= forallb
         (fun x : {f : symbol & matrixInt (Pos.to_nat d) (arity f)} =>
          let (f, mi) := x in
          bVforall
            (fun m : matrix (Pos.to_nat d) (Pos.to_nat d) =>
             OrdSemiRing2.bgt Nat_as_OSR
               (get_elem m (dim_pos (Pos.to_nat d)) (dim_pos (Pos.to_nat d)))
               0) (args mi)) l).

        case_eq b; intros H2 H3; subst b; try discr.

        inversion H3. clear H3.
        
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

        destruct x as [t u]. simpl in *.

        destruct (succeq'_dec t u); intros; try discr; auto.

        unfold brule in H.

        unfold term_ge, term_ord, mint_ge in n.

        eapply bmint_ge_ok in H. simpl in *.

        unfold mint_ge in H. simpl in *. try contradiction.
        
        (** Remove all rules [>] in [R]. *)
      
        apply WF_incl with (S := red (filter (brule (neg bgt)) R)).

        unfold inclusion. intros t u H7. redtac. unfold red.

        exists l0. exists r. exists c. exists s. intuition.

        apply filter_In. apply filter_In in lr. intuition.

        unfold brule, neg. unfold brule, neg in H3. simpl in *.

        unfold bsucc, bool_of_rel in H3.

        destruct ma_succ'_dec in H3; try discr.

        simpl in *.

        unfold AMatrixInt2.term_gt, term_gt, term_ord in n0; simpl in *;
        auto.

        unfold mint_gt in n0.

        rewrite <- bmint_gt_ok in n0. apply eq_true_not_negb in n0.

        subst bgt. apply n0. hyp.
      Qed.

      (***********************************************************************)
      (** Relative termination use matrix interpretation over domain
       natural numbers. Relative termination has the same condition
       like full termination, where the relation [>] is closed by
       context and [>] is monotone. Use the [type_matrix_polynomial]
       of full termination for relative termination. *)

      Definition rel_matrix_interpretation (R D: arules) is dom dim := 
        match type_matrix is dom dim with
          | Ok (bsucc_ge, bsucc_gt) =>
            if   forallb (ATrs.brule bsucc_ge) D &&
                 forallb (ATrs.brule bsucc_ge) R
            then Ok (filter (ATrs.brule (neg bsucc_gt)) D) (* TODO: add the filter for R *)
            else Ko _ (Error ERuleNotInLargeOrdering_matrix_rel)
          | Ko e                    => Ko _ e
        end.
      
      Close Scope nat_scope.

      (*********************************************************************)
      (** ** Matrix interpretation over domain tropical. *)
      (* TODO: comments *)

      Require Import Tropical_as_OSR SemiRing ATropicalBasedInt2.

      Section matrix_tropical.

        (* TODO *)
        Section weakRedPair.

          Variable dim: nat.
          Notation dim_pos := (dim_pos dim).
          Notation mint := (@matrixInt _ dim).

          Variable l: list {g: symbol & mint (arity g)}.
         
          (* REMARK: this variable is an assumption in CoLoR. *)

          Variable A0_gt_A1:  0 >> 1.

          (** Definition of Class MatrixMethodConf. *)

          Definition TM_Conf_Trop := @Conf Sig _ dim
                                    (@TMatrix_Int arity dim coef_sring_tropical l) A0_gt_A1.

        End weakRedPair.

          (*
          (* TODO *)
          Require Import ATropicalInt1.

          Instance TTropicalInt_imp : TTropicalInt Sig dim.
          Proof.
            apply Build_TTropicalInt with (trop_int:= TM_Trop).         

          Definition TM_Mon_Trop := @MonotoneAlgebra_Trop Sig TM_Trop. 

          (* TODO: define in ATropical an instance for monotonealgebra *)
          
          Definition TM_Conf_Trop :=@Conf Sig _ TM_Trop.
          Definition WP_Matrix_Trop := @WP_MonAlg  _ TM_Mon_Trop. *)         
        
        (* TODO define an instance for tropical matrix *)
        
        Variable A0_gt_A1: 0 >> 1. (* TODO : this is an assumption of
        Tropical in CoLoR. *)

        Definition matrix_tropical (is: list (symbol * cpf.arity * function))(dim: nat):
          result ((aterm -> aterm -> bool) * (aterm -> aterm -> bool)) :=
          Match map_rev (@color_interpret_matrix arity dim coef_sring_tropical) is With l ===>
            if forallb (fun x =>
              match x with
                existT f mi   => bVexists
                  (fun m      =>
                     tropical_is_finite (get_elem m (dim_pos dim) (dim_pos dim)))(args mi)
                  || tropical_is_finite (Vnth (const mi) (dim_pos dim))
              end) l
           then
             let Conf := TM_Conf_Trop l A0_gt_A1 in
             Ok (fun t u      =>
                   let (l, r) :=
                     @rule_mi _ _ dim Conf (mkRule t u)
                   in bmint_ge l r,
                (fun t u      =>
                   let (l, r) :=
                     @rule_mi _ _ dim Conf (mkRule t u)
                   in bmint_gt l r))
            else Ko _ (Error ENotMonotone_matrix_tropical).

        (* TODO *)
        (** Type matrix interpretation over domain tropical. *)
        
        Definition type_matrix_tropical (is: list (symbol * cpf.arity * function))
          (dom: cpf.domain) (dim: nat) :
          result ((aterm -> aterm -> bool) * (aterm -> aterm -> bool)) :=
          match dom with
            | Domain_naturals               => Ko _ (Todo Ttype_polynomialDomain_naturals)
            | Domain_integers               => Ko _ (Todo Ttype_polynomialDomain_integers)
            | Domain_rationals delta        => Ko _ (Todo Ttype_polynomialDomain_rationals)
            | Domain_arctic dom'            => Ko _ (Todo Ttype_polynomialDomain_arctic)
            | Domain_tropical dom'          => Ko _ (Todo Ttype_polynomialDomain_tropical)
            (*matrix_tropical is dim *) (* TODO *)
            | Domain_matrices dim sdim dom' => Ko _ (Todo Ttype_polynomialDomain_matrices)
          end.
        
        (* TODO *)

        Definition matrix_int_tropical (R: arules) is dom dim: result arules :=
          match type_matrix_tropical is dom dim with
            | Ok (bsucc_ge, bsucc_gt) =>
              if   forallb (ATrs.brule bsucc_ge) R
              then Ok (filter (ATrs.brule (neg bsucc_gt)) R)
              else Ko _ (Error ERuleNotInLargeOrdering_matrix_tropical)
            | Ko e                    => Ko _ e
          end.

        (**********************************************************************)
      
        (* TODO *)
        (*
        Lemma matrix_interpretation_tropical_ok : forall (R R': arules) is d de
         (h:matrix_int_tropical R is (Domain_tropical de)(Pos.to_nat d) = Ok R')
         (wf: WF (red R')), WF (red R).

        Proof.
        Admitted.*)

        
        (**********************************************************************)
        (** [type_matrixInterpertation] type for matrix interpretation
         with different domain natural number. Where the elements are
         vectors. Example: if the domain is naturals, then the
         coefficients in front of variables have to be matrices and
         the constants should be vectors over the naturals. *)

        Definition type_matrix_interpretation (R: arules) is dom dim :=
          match dom with
            | Domain_naturals               => matrix_interpretation R is dom (nat_of_P dim)
            | Domain_integers               => Ko _ (Todo Ttype_polynomialDomain_integers)
            | Domain_rationals delta        => Ko _ (Todo Ttype_polynomialDomain_rationals)
            | Domain_tropical _             => Ko _ (Todo Ttype_polynomialDomain_tropical)
            (*matrix_int_tropical R is dom (nat_of_P dim)*)
            | Domain_arctic dom'            => Ko _ (Todo Ttype_polynomialDomain_arctic)
            | Domain_matrices dim sdim dom' => Ko _ (Todo Ttype_polynomialDomain_matrices)
          end.

        (**********************************************************************)
        (** [type_matrixInterpertation] of relative termination proof.
       REMARK: In domain arctic only occur at top termination and not
       in relative termination. Domain naturals. *)

        Definition rel_type_matrix_interpretation (R D: arules) is dom dim :=
          match dom with
            | Domain_naturals               => rel_matrix_interpretation R D is dom
                                               (nat_of_P dim)
            | Domain_integers               => Ko _ (Todo Ttype_polynomialDomain_integers)
            | Domain_rationals delta        => Ko _ (Todo Ttype_polynomialDomain_rationals)
            | Domain_tropical _             => Ko _ (Todo Ttype_polynomialDomain_tropical)
            (* TODO *)
            | Domain_arctic dom'            => Ko _ (Todo Ttype_polynomialDomain_arctic)
            | Domain_matrices dim sdim dom' => Ko _ (Todo Ttype_polynomialDomain_matrices)
          end.

      End matrix_tropical.

    End matrix_nat.

    (***********************************************************************)
    (** ** Reduction pair interpretation with polynomial and matrix
     interpretation in domain: natural numbers and rational numbers. *)

    Definition redPair_interpretation (R: arules) (t: type_t9) 
      (is: list (symbol * cpf.arity * function)): result arules :=
      match t with
        | Type_t9_polynomial dom degmax             =>
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

          b. Domain tropical numbers. *)

    Lemma redPair_interpretation_ok : forall (R R': arules) t is,
     redPair_interpretation R t is = Ok R' ->
     WF (red R') -> WF (red R).

    Proof.
      intros R R' t is h wf.

      destruct t as [d | de]; simpl in h; try discr.

      unfold polynomial_interpretation in h.

      destruct d; simpl in h; try discr.

      (** 1.a. Correctness proof of polynomial of domain natural
      numbers.*)

      eapply poly_nat_ok. apply h. apply wf.

      (** 1.b. Correctness proof of polynomial of domain rational
      numbers. *)

      eapply poly_rat_ok. apply h. apply wf.

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

    (***********************************************************************)
    (** ** Relative termination reduction pair interpretation with
     polynomial and matrix interpretation in domain: natural numbers
     and rational numbers. *)

    Definition rel_redPair_interpretation (R D: arules) (t: type_t9) 
      (is: list (symbol * cpf.arity * function)): result arules :=
      match t with
        | Type_t9_polynomial dom degmax             =>
            rel_polynomial_interpretation R D is dom
        | Type_t9_matrixInterpretation dom dim sdim =>
            rel_type_matrix_interpretation R D is dom dim
      end.

    (** Correctness proof of relation redPair interpretation.

      Proof structure:

       1. Correctness proof of polynomial interpretation.

          a. Domain natural numbers.

          b. Domain rational numbers
            - Coefficients are of domain integer.
            - Coefficients are of domain rationals
       2. Correctness proof of matrix interpretation.

          a. Domain natural numbers.

          b. Domain tropical numbers. *)
    
    Require Import APolyInt_MA2. Import OR_Notations.
    
    (* FIXME *)

    Lemma rel_poly_nat_ok : forall (R D D': arules) is
      (h:  match poly_nat is with
            | Ok (bsucc_ge, bsucc_gt) =>
             if   forallb (brule bsucc_ge) R &&
                  forallb (brule bsucc_ge) D
             then Ok (List.filter (brule (neg bsucc_gt)) D)
             else Ko arules (Error ERuleNotInLargeOrdering_poly)
            | Ko e                    => Ko arules e
           end = Ok D')
       (wf: WF (red_mod R D')), WF (red_mod R D).

    Proof.
      intros R D D' is h wf.

      case_eq (poly_nat is); intros p H; rewrite H in h; try discr.

      destruct p as [bge bgt].

      case_eq (forallb (brule bge) R && forallb (brule bge) D);
        intros H0; rewrite H0 in h; try discr.

      inversion h. subst D'. clear h. simpl in *.

      unfold poly_nat in H. revert H.

      destruct (map_rev (color_interpret arity) is); intros; try discr.

      gen H.

      set (b:= forallb
         (fun x : {f : symbol & poly (arity f)} =>
          let (f, p) := x in bcoef_not_neg p) l &&
       forallb
         (fun x : {f : symbol & poly (arity f)} =>
          let (f, p) := x in
          forallb
            (fun x0 : nat_lt (arity f)          =>
            or_bgt (coef (mxi (prf x0)) p) sr_0) (mk_nat_lts (arity f))) l).

      case_eq b; intros H2 H3; subst b; try discr.

      inversion H3. clear H3.

      set (trsInt := (fun f: symbol => fun_of_pairs_list arity f l)).

      cut (forall f: Sig, pweak_monotone (trsInt f)).

      intros trsInt_wm. Focus 2.

      (** Polynomial weak is monotone. *)

      intro f. apply trsInt_wm_poly.

      (** Proving wellfound of [red_mod]. *)

      rewrite andb_eq in H2. destruct H2. hyp.

      rewrite andb_eq in H2. destruct H2.

      apply WF_rp_red_mod with (WP:=@WP _ _ l H1).

      (** Relation [>] is closed by context. *)

      change (context_closed (IR (@I Sig  _ (TPolyInt_poly arity l H1)) succ)).

      apply IR_context_closed. apply pi_monotone.

      simpl. intro f.

      (** Polynomial is strong monotone. *)

      apply trsInt_pw_poly. rewrite andb_eq. split. hyp. hyp.

      (** Check that all rules [R] are included in [>=]. *)

      simpl; unfold brule, bsucceq, bool_of_rel; simpl.

      rewrite forallb_forall. intros x Hx. subst bge.

      rewrite andb_eq in H0. destruct H0.

      rewrite forallb_forall in H0.

      ded (H0 x Hx).

      destruct x as [t u]. simpl in *.

      destruct succeq'_dec; try discr; auto.

      unfold succeq' in n. unfold brule in H4.

      rewrite bcoef_not_neg_ok in H4. contradiction.

      (** All relation [>=] are including in rule [dp R = D]. *)

      simpl; unfold brule, bsucceq, bool_of_rel; simpl.

      rewrite forallb_forall. intros x Hx. subst bge.

      rewrite andb_eq in H0. destruct H0.

      rewrite forallb_forall in H3. ded (H3 x Hx).

      destruct x as [t u]. simpl in *.

      destruct succeq'_dec; auto.

      unfold brule in H4. rewrite bcoef_not_neg_ok in H4.

      unfold succeq' in n. contradiction.

      (** Remove all rules [D] that are included in [>]. *)

      apply WF_incl with (S:= red_mod (filter (brule (neg bgt)) R)
                                      (filter (brule (neg bgt)) D)).

      unfold inclusion. intros t u H7. redtac. unfold red_mod.

      unfold compose. exists t0. split. simpl in *.

      Focus 2.

      (* red (filter (brule (neg bgt)) D) t0 u *)

      unfold red. exists l0. exists r. exists c.

      exists s. intuition. apply filter_In.

      apply filter_In in lr. intuition.

      unfold brule, neg. unfold brule, neg in H7.

      simpl in *. unfold bsucc, bool_of_rel in H7.

      destruct ma_succ'_dec in H7; try discr.

      simpl in *. unfold succ' in n0.

      rewrite <- bcoef_not_neg_ok in n0.

      apply eq_true_not_negb in n0.

      subst bgt. apply n0.

      (* red (filter (brule (neg bgt)) R #) t t0 *)

      (* TODO *)
      Focus 2.    

    Admitted.
    
    (***************************************************************************)
    (** Correctness proof of termination relation [red_mod R D] of
    polynomial interpretation over rational numbers.  *)

    (* REMARK: open scope Q to be able to fold argument [b] in the
    proof. *)

    Open Scope Q_scope. 

    Lemma rel_poly_rationals_common_ok : forall del (R D D': arules) is
      (h : match poly_rat is del with
             | Ok (bsucc_ge, bsucc_gt) =>
               if   forallb (brule bsucc_ge) R && 
                    forallb (brule bsucc_ge) D
               then Ok (filter (brule (neg bsucc_gt)) D)
               else Ko arules (Error ERuleNotInLargeOrdering_poly)
             | Ko e                    => Ko arules e
           end = Ok D')
      (wf : WF (red_mod R D')), WF (red_mod R D).
    
    Proof.
      intros del R D D' is h wf.

      case_eq (poly_rat is del); intros p H; rewrite H in h;
      try discr.

      destruct p as [bge bgt].

      case_eq (forallb (brule bge) R && forallb (brule bge) D);
        intros H0; rewrite H0 in h; try discr.

      inversion h. subst D'. clear h.

      unfold poly_rat in H.

      case_eq (map_rev (color_interpret arity) is);
        intros l H1; rewrite H1 in H; try discr.

      gen H.

      set (b:= forallb
               (fun x : {f : symbol & poly (arity f)} =>
                let (f, p) := x in bcoef_not_neg p) l &&
               forallb
               (fun x : {f : symbol & poly (arity f)} =>
                let (f, p) := x in
               forallb
               (fun x0 : nat_lt (arity f) =>
                @or_bgt Q_as_OR (coef (mxi (prf x0)) p) 0)
               (mk_nat_lts (arity f))) l).

      case_eq b; intros H2 H3; subst b; try discr.

      inversion H3. clear H3.

      set (trsInt := (fun f: symbol => fun_of_pairs_list arity f l)).

      cut (forall f: symbol, pweak_monotone (trsInt f)).

      intros trsInt_wm. Focus 2.

      (** Polynomial weak is monotone. *)
      
      intro f. apply trsInt_wm_poly.
      
      (** Proving [WF (red_mod R D)]. *)

      rewrite andb_eq in H2. destruct H2. hyp.

      rewrite andb_eq in H2. destruct H2.

      apply WF_rp_red_mod with (WP:=@WP_Q _ _ l H2 del).
      
      (* A proof of [>] are closed by context: IR_context_closed. *)

      change (context_closed (IR (@I Sig _ (TPolyInt_poly arity l H2)) succ)).

      apply IR_context_closed. apply pi_monotone.

      simpl. intro f.
      
      (* Polynomial is strong monotone. *)

      apply trsInt_pw_poly. rewrite andb_eq. split. hyp. hyp.

      (* Check that all rules [R] are included in [>=]. *)

      simpl; unfold brule, bsucceq, bool_of_rel; simpl.

      rewrite forallb_forall. intros x Hx. subst bge.

      rewrite andb_eq in H0. destruct H0.

      rewrite forallb_forall in H0. ded (H0 x Hx). destruct x as [t u].

      simpl in *. 

      case_eq (succeq'_dec Sig (TPolyInt_poly arity l H2) t u);
        intros s Hs. auto.

      unfold brule in H5. unfold succeq' in s.

      rewrite bcoef_not_neg_ok in H5. contradiction.

      (** Proving the relation [>=] are in rules [D]. *)
      
      simpl. unfold brule, bsucceq, bool_of_rel; simpl.

      rewrite forallb_forall. intros x Hx. subst bge.

      rewrite andb_eq in H0. destruct H0.

      rewrite forallb_forall in H4. ded (H4 x Hx).

      destruct x as [t u]. simpl in *.

      case_eq (succeq'_dec Sig (TPolyInt_poly arity l H2) t u);
        intros s Hs. auto. unfold brule in H5.

      unfold succeq' in s.

      rewrite bcoef_not_neg_ok in H5. contradiction.

      (** Proving [red_mod] is well founded when remove all relation
      [>] in [R] and [D]. *)

      apply WF_incl with (S := red_mod (List.filter (brule (neg bgt)) R)
                                       (List.filter (brule (neg bgt)) D)).

      unfold inclusion. intros t u H7. redtac. unfold red_mod.

      unfold compose. exists t0. split. simpl in *.

      Focus 2.

      (* red (filter (brule (neg bgt)) D) t0 u *)

      unfold red. exists l0. exists r. exists c. exists s.

      intuition. apply filter_In.

      apply filter_In in lr. intuition.

      unfold brule, neg. unfold brule, neg in H8.

      simpl in *. unfold bsucc, bool_of_rel in H8.

      destruct ma_succ'_dec in H8; try discr.

      simpl in *. unfold succQ' in n0.

      rewrite <- bcoef_not_neg_ok in n0.

      apply eq_true_not_negb in n0.

      subst bgt. apply n0.

    (* red (filter (brule (neg bgt)) R #) t t0 *)

    (* TODO *) 
      
    Admitted.

    (**************************************************************************)
    (** Correctness proof of termination relation [red_mod R D] of
    polynomial interpretation over rational numbers.  *)

    Lemma rel_poly_rationals_ok: forall (R D D': arules) is n
      (h:  match type_poly_rationals n is with
             | Ok (bsucc_ge, bsucc_gt) =>
               if   forallb (brule bsucc_ge) R &&
                    forallb (brule bsucc_ge) D
               then Ok (List.filter (brule (neg bsucc_gt)) D)
               else Ko arules (Error ERuleNotInLargeOrdering_poly)
             | Ko e                    => Ko arules e
           end = Ok D')
      (wf: WF (red_mod R D')), WF (red_mod R D).

    Proof.
      intros R D D' is n0 h wf.

      unfold type_poly_rationals in h.

      destruct n0; simpl in h; try discr.

      set (del:= inject_Z i). fold del in h.

      (** In the case of rationals -> natural numbers, where it convert a
       natural number to rational number by divide by 1. *)
      
      apply rel_poly_rationals_common_ok with (del:=del)(D':=D')(is:=is).

      hyp. hyp.
      
      (** In the case of rationals -> rational numbers. *)
      
      set (t:= Qmake i p). fold t in h.

      apply rel_poly_rationals_common_ok with (del:=t)(D':=D')(is:=is).

      hyp. hyp.
    Qed.

    Close Scope Q_scope.

    (**************************************************************************)
    (** Correctness proof of termination relation [red_mod R D] of
    polynomial interpretation over rational numbers.  *)

    Lemma rel_polynomial_interpretation_ok: forall (R D D': arules) is (d:cpf.domain)
      (h: rel_polynomial_interpretation R D is d = Ok D')
      (wf : WF (red_mod R D')), WF (red_mod R D).

    Proof.
      intros R D D' is d h wf.

      unfold rel_polynomial_interpretation in h.

      unfold type_polynomial in h.

      destruct d; simpl in h; try discr.

      (** Domain naturals. *)

      apply rel_poly_nat_ok with (D':=D')(is:=is).
    (*
      hyp. hyp.

      (** Domain rationals. *)
      
      apply rel_poly_rationals_ok with (D':=D')(is:=is)(n:=n0).

      hyp. hyp.*)
    Admitted.

    (*************************************************************************)
    (** Correctness proof of termination relation [red_mod R D] of
    matrix interpretation of domain natural. *)

    Require Import ABterm OrdSemiRing2.

    Open Scope nat_scope.

    Lemma rel_matrix_interpretation_nat_ok : forall (R D D': arules) 
      (d:dimension) is
      (h: rel_matrix_interpretation R D is Domain_naturals (Pos.to_nat d) = Ok D')
      (wf : WF (red_mod R D')), WF (red_mod R D).

    Proof.
      intros R D D' d is h wf.

      unfold rel_matrix_interpretation in h.

      destruct Domain_naturals; simpl in h; try discr.

      case_eq (matrix_nat is (Pos.to_nat d));
        intros p H; rewrite H in h; try discr.

      destruct p as [bge bgt].

      case_eq (forallb (brule bge) D && forallb (brule bge) R);
        intro H0; rewrite H0 in h; try discr.

      inversion h. subst D'. clear h. unfold matrix_nat in H.

      revert H. 

      case (map_rev (color_interpret_matrix arity (Pos.to_nat d)) is);
        intros l H; try discr.

      (*COQ: case_eq (forallb (fun x : {H : symbol & poly (arity H)}
          => let (x0, p) := x in bcoef_pos p && forallb (fun x0 :
          nat_lt (arity f) => is_pos (coef (mxi (prf x0)) p))
          (mk_nat_lts (arity f))) l) does not work! *)
      
      gen H. simpl in *.
      
      set (b := forallb
                  (fun x : {f : symbol & matrixInt (Pos.to_nat d) (arity f)} =>
                     let (f, mi) := x in
                     bVforall
                       (fun m : matrix (Pos.to_nat d) (Pos.to_nat d) =>
                          OrdSemiRing2.bgt Nat_as_OSR
                           (get_elem m (dim_pos (Pos.to_nat d)) (dim_pos (Pos.to_nat d)))
                           0) (args mi)) l).

      case_eq b; intros H1 H3; subst b; try discr. inversion H3.

      clear H3.
      
      apply WF_rp_red_mod with (WP:=@WP_Matrix_Nat _ l).

      (** Context closed succ *)

      change (context_closed (IR (@AMatrixBasedInt2.I _ Sig _ _
                                (@mi_eval_ok _ _ (@TMatrix_Int arity _ coef_sring_N l)))
                                (@AMatrixInt2.succ _ _ (@TMatrix_Int _ _ coef_sring_N l)))).

      apply IR_context_closed. 
      apply AMatrixInt2.monotone_succ. simpl. intro f.
      apply trsInt_nat_mon. hyp.
      
      (** Check that rules R is included in succeq *)

      simpl; unfold brule, wr_bsucceq, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      rewrite forallb_forall in H2. ded (H2 x Hx).
      destruct x as [t u]. simpl in *.

      destruct (AMatrixBasedInt2.succeq'_dec t u); intros; try discr; auto.
      unfold brule in H.
      unfold term_ge, term_ord, mint_ge in n0.
      eapply bmint_ge_ok in H3. simpl in *.
      unfold mint_ge in H3. simpl in *. try contradiction.

      (** Check that rules D is included in succeq *)

      unfold brule, bsucceq, bool_of_rel; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H0. destruct H0.
      rewrite forallb_forall in H0.
      ded (H0 x Hx). destruct x as [t u]. simpl in *.
      unfold bsucceq, bool_of_rel.
      destruct ma_succeq'_dec; auto.
      unfold brule in H3. simpl in *.
      unfold succeq', AMatrixBasedInt2.succeq',
      term_ge, term_ord, mint_ge in n0.
      apply bmint_ge_ok in H3. try contradiction.

      (** Remove all rules D that are in succ. *)

      apply WF_incl with (S:= red_mod (filter (brule (neg bgt)) R)
                                      (filter (brule (neg bgt)) D)).

      unfold inclusion. intros t u H7. redtac. unfold red_mod.
      unfold compose. exists t0. split. simpl in *.
      Focus 2. 
      (* red (filter (brule (neg bgt)) D) t0 u *)
      unfold red. exists l0. exists r. exists c.
      exists s. intuition. apply filter_In.
      apply filter_In in lr. intuition.
      unfold brule, neg. unfold brule, neg in H6.
      simpl in *. unfold bsucc, bool_of_rel in H6.
      destruct ma_succ'_dec in H6; try discr.
      simpl in *. unfold AMatrixInt2.term_gt, AMatrixBasedInt2.term_gt,
                  term_ord in n0; simpl in *; auto.
      unfold AMatrixInt2.mint_gt in n0.
      rewrite <- AMatrixInt2.bmint_gt_ok in n0.
      apply eq_true_not_negb in n0.
      subst bgt. apply n0.

    (* red (filter (brule (neg bgt)) R #) t t0 *)
      
    (* FIXME: fixe the condition in the boolen function. *)
      
    (* TODO *)
    Admitted.

    (*************************************************************************)
    (** Correctness proof of termination relation [red_mod R D] of
    reduction pair interpretation. *)

    Lemma rel_redPair_interpretation_ok : forall (R D D': arules) t is,
      rel_redPair_interpretation R D t is = Ok D' ->
      WF (red_mod R D') -> WF (red_mod R D).
    
    Proof.
      intros R D D' t is h wf. destruct t; simpl in h; try discr.

      (** Polynomial interpretation over natural numbers and rational
    numbers. *)

      apply rel_polynomial_interpretation_ok with (D':=D')(is:=is)(d:=d).

      apply h. apply wf.

      (** Matrix interpretation over natural numbers. *)

      destruct d; simpl in h; try discr.

      apply rel_matrix_interpretation_nat_ok with (D':=D')(d:=d0)(is:=is).

      apply h. apply wf.

    (* REMARK: There is no arctic domain for relative termination. *)
    Qed.

    End Full_Termination.

    (***********************************************************************)
    (** ** Reduction pair path ordering is an ordering introduced by
     Dershowitz. It extends a well-founded order on the signature,
     called a precedence, to a reduction order on terms. We used the
     Coccinelle's library. 

    REMARK: do not define notation for [Sig] to be able to use
    [filter_arity] in [AFilterPerm.filter] later. *)

    (* TODO *)
    
    Section rpo.
      
      Require Import cpf_util rpo2 ordered_set rpo_extension Coccinelle2.
      
      (* FIXME: take a look at list reverse: it is not the reverse list. *)
      (* TEST: test the condition of bprec_eq_status_symb. *)

      (** Path ordering without argument filtering method. *)

      Definition pathOrder_term (l: list (symbol * cpf.arity * nonNegativeInteger * t10)) :
        cpf_util.result ((aterm -> aterm -> bool) * (aterm -> aterm -> bool)) :=
        if forallb (fun f => forallb (fun g => @bprec_eq_status_symb arity l f g)
                                     (list_sig l))(list_sig l)
        then
          Ok ((fun t u =>
                 let t' := @term_of_aterm (Sig arity) t in
                 let u' := @term_of_aterm (Sig arity) u in
                 match cpf2color.rpo_eval l rpo_n t' u' with
                   | Some Equivalent | Some Greater_than => true
                   | _                                   => false
                 end),
              (fun t u =>
                 let t' := @term_of_aterm (Sig arity) t in
                 let u' := @term_of_aterm (Sig arity) u in
                 match cpf2color.rpo_eval l rpo_n t' u' with
                   | Some Greater_than                  => true
                   | _                                  => false
                 end))
        else Ko _ (Error ENotpathOrder_term).

      (************************************************************************)
      (** Correctness proof of path ordering without argument filtering *)

      Lemma rpo_without_af_ok : forall (R R': arules) l
        (h: match pathOrder_term l with
              | Ok (bsucc_ge, bsucc_gt) =>
                if   forallb (brule bsucc_ge) R
                then Ok (List.filter (brule (neg bsucc_gt)) R)
                else Ko arules (Error ENotpathOrder)
              | Ko e                    => Ko arules e
            end = Ok R')
        (wf: WF (red R')), WF (red R).
      
      Proof.
        intros R R' l h wf.

        case_eq (pathOrder_term l);
          intros p H; rewrite H in h; try discr.

        destruct p as [bge bgt]; try discr.

        case_eq (forallb (brule bge) R); intro H1; rewrite H1 in h;
        try discr.

        inversion h. subst R'. clear h.

        unfold pathOrder_term in H. gen H.

        (* FIXME?: change the condition of boolean function. *)

        set (b:= forallb (fun f : symbol =>
                 forallb (fun g : symbol => bprec_eq_status_symb arity l f g)
                 (list_sig l)) (list_sig l)).

        case_eq b; intros H2 H3; subst b; try discr.

        inversion H3. clear H3.

        apply WF_rp_red with (WP:= @WP_RPO rpo_n (Sig arity)
                             (Precendence_Imp arity l rpo_n)).

       (** A proof of [>] are closed by context. *)
        
        apply cc_succ.

        (** Check that all rules [R] are included in [>=] *)
        
        simpl; unfold brule, bsucceq.

        rewrite forallb_forall.
        
        intros x Hx. subst bge.

        rewrite forallb_forall in H1.

        ded (H1 x Hx). destruct x as [t u]. simpl in *.

        unfold brule in H0. hyp.

        (** Remove all rules [R] are included in [>]. *)
        
        apply WF_incl with (S:= red (List.filter (brule (neg bgt))R)).

        unfold inclusion. intros u v H3. redtac.

        unfold red. exists l0. exists r. exists c. exists s.

        intuition.

        apply filter_In. apply filter_In in lr.

        intuition.

        unfold brule, neg. unfold brule, neg in H3. simpl in *.

        unfold bsucc in H3. simpl in *.

        subst bgt. hyp. hyp.
      Qed.

      (***********************************************************************)
      (** Path ordering with argument filtering method. *)

      Require Import AFilterPerm AProj.

      Open Scope nat_scope.
      
      (** Define function [pathOrder_rpo_proj_filter], where projection
       /filter's term embedded inside rpo's term. Argument filtering
       with projection only (collapsing) and non-collapsing. *)

      (* FIXME: conditions may lead to error *)

      (* Filter (Projection (RPO)) *)
      
      (* Use the filter in AFilter/proj *)

      (* FIXME *)
      Definition pathOrder_rpo_filter
                 (l: list (symbol * cpf.arity * nonNegativeInteger * t10))
                 (args : list (symbol * cpf.arity * t11)) :
        cpf_util.result ((aterm -> aterm -> bool) * (aterm -> aterm -> bool)) :=
           
        if forallb (fun f => forallb (fun g => @bprec_eq_status_symb arity l f g)
                             (list_sig l))(list_sig l) &&
          bnon_dup (Sig arity)(color_raw_pi_filter arity args)(list_split_triple args)
          && @bpermut  (Sig arity) (color_raw_pi_filter arity args) (list_sig l)
        then
          Ok ((fun t u =>
                 let sig := Sig (@ASignature.arity (Sig
                            (filter_arity (Sig arity)(color_build_pi_filter args)))) in
                 let t'  := @term_of_aterm sig
                            ((@color_filter arity args t))    in
                 let u'  := @term_of_aterm sig
                            ((@color_filter arity args u))    in
                 match cpf2color.rpo_eval l rpo_n t' u' with
                   | Some Equivalent | Some Greater_than => true
                   | _                                   => false
                 end),
              (fun t u =>
                 let sig := Sig (@ASignature.arity (Sig
                            (filter_arity (Sig arity)(color_build_pi_filter args )))) in
                 let t'  := @term_of_aterm sig
                            ((@color_filter arity args t))     in
                 let u'  := @term_of_aterm sig
                            ((@color_filter arity args u))     in
                 match cpf2color.rpo_eval l rpo_n t' u' with
                   | Some Greater_than                   => true
                   | _                                   => false
                 end))
        else Ko _ (Error EPrecedence_incompatible_statuses).

      (* Fixme *)
      Definition pathOrder_rpo_proj
                 (l: list (symbol * cpf.arity * nonNegativeInteger * t10))
                 (args : list (symbol * cpf.arity * t11)) :
        cpf_util.result ((aterm -> aterm -> bool) * (aterm -> aterm -> bool)) :=
        if forallb (fun f => forallb (fun g => @bprec_eq_status_symb arity l f g)
                             (list_sig l))(list_sig l) &&
                   @bvalid (Sig arity) (color_raw_pi args)(list_sig l)
        then
          Ok ((fun t u =>
                 let t'  := @term_of_aterm (Sig arity) (color_proj args t)    in
                 let u'  := @term_of_aterm (Sig arity) (color_proj args u)    in
                 match cpf2color.rpo_eval l rpo_n t' u' with
                   | Some Equivalent | Some Greater_than => true
                   | _                                   => false
                 end),
              (fun t u =>
                 let t'  := @term_of_aterm (Sig arity)
                            (color_proj args t)     in
                 let u'  := @term_of_aterm (Sig arity)
                            (color_proj args u)     in
                 match cpf2color.rpo_eval l rpo_n t' u' with
                   | Some Greater_than                   => true
                   | _                                   => false
                 end))
        else Ko _ (Error EPrecedence_incompatible_statuses).


      (* FIXME *)
      Definition pathOrder_rpo_proj_filter
                 (l: list (symbol * cpf.arity * nonNegativeInteger * t10))
                 (args : list (symbol * cpf.arity * t11)) :
        cpf_util.result ((aterm -> aterm -> bool) * (aterm -> aterm -> bool)) :=
        if forallb (fun f => forallb (fun g => @bprec_eq_status_symb arity l f g)
                             (list_sig l))(list_sig l)
        then
          Ok ((fun t u =>
                 let sig := Sig (@ASignature.arity (Sig
                            (filter_arity (Sig arity)(color_build_pi_filter args)))) in
                 let t'  := @term_of_aterm sig
                            (color_proj args (@color_filter arity args t))    in
                 let u'  := @term_of_aterm sig
                            (color_proj args (@color_filter arity args u))    in
                 match cpf2color.rpo_eval l rpo_n t' u' with
                   | Some Equivalent | Some Greater_than => true
                   | _                                   => false
                 end),
              (fun t u =>
                 let sig := Sig (@ASignature.arity (Sig
                            (filter_arity (Sig arity)(color_build_pi_filter args )))) in
                 let t'  := @term_of_aterm sig
                            (color_proj args (@color_filter arity args t))     in
                 let u'  := @term_of_aterm sig
                            (color_proj args (@color_filter arity args u))     in
                 match cpf2color.rpo_eval l rpo_n t' u' with
                   | Some Greater_than                   => true
                   | _                                   => false
                 end))
        else Ko _ (Error EPrecedence_incompatible_statuses).

      (***********************************************************************)
      (** Define a function checking each cases of argument filter.
       check if they used collapsing/non-collapsing then use the rpo +
       projection + perm, otherwise return [error].  *)

      Require Import List.

      Definition pathOrder_term_rpo_af 
                 (l: list (symbol * cpf.arity * nonNegativeInteger * t10))
                 (args : list (symbol * cpf.arity * t11)) :
        cpf_util.result ((aterm -> aterm -> bool) * (aterm -> aterm -> bool)) :=
        let fix aux args :=
        match args with
          | nil => Match pathOrder_rpo_filter l nil With
                         rpo_filter ===> Ok rpo_filter
          | (_, _, t) :: l' as args =>
            if is_collapsing t
            then   Match pathOrder_rpo_filter l args With
                         rpo_filter ===> Ok rpo_filter
            else if is_nonCollapsing t
                 then Match pathOrder_rpo_proj l args With
                            rpo_proj ===> Ok rpo_proj
                 (*else if is_col_noncol t
                      then Match pathOrder_rpo_proj_filter l args With
                                 rpo_filter_proj ===> Ok rpo_filter_proj*)
                      else aux l'
                         
        end in aux nil.


      (*
    Definition pathOrder_term_rpo_af
      (l: list (symbol * cpf.arity * nonNegativeInteger * t10))
      (args : list (symbol * cpf.arity * t11)) :
      cpf_util.result ((aterm -> aterm -> bool) * (aterm -> aterm -> bool)) :=
      match args with
        | (_, _, t) :: _ =>
          match is_col_noncol t with
            | true       =>   Match pathOrder_rpo_proj_filter l args With
                              rpo_filter_proj
                         ===> Ok rpo_filter_proj
            | false      =>   Ko _ EargumentFilter_false
          end
        | nil            =>   Ko _ EargumentFilter_nil
      end.*)
      
      (***********************************************************************)

      Lemma rpo_with_af_ok : forall (R R': arules) args l
        (h: match pathOrder_term_rpo_af l args with
              | Ok (bsucc_ge, bsucc_gt) =>
                if   forallb (brule bsucc_ge) R
                then Ok (List.filter (brule (neg bsucc_gt)) R)
                else Ko arules (Error ENotpathOrder_AF) (* FIXME: ERROR *)
              | Ko m                    => Ko arules m
            end = Ok R')
        (wf: WF (red R')), WF (red R).
      
      Proof.   
        intros R R' args l h wf.

        case_eq (pathOrder_term_rpo_af l args);
          intros p H; rewrite H in h; try discr.

        (*
        destruct p as [bge bgt]; try discr.

        case_eq (forallb (brule bge) R); intro H1; rewrite H1 in h;
        try discr.

        inversion h. subst R'. clear h.

        unfold pathOrder_term_rpo_af in H.

        destruct args; try discr.

        destruct p; try discr.

        destruct p; try discr.*)
        
        (** Argument filtering method. *)
        (*
        case_eq (is_empty ((s, a, t) :: args)); intro H2; rewrite H2 in H;
        try discr.
        set (ls:= (s, a, t):: args). fold ls in H.
        case_eq (pathOrder_rpo_proj_filter l ls);
          intros p H3; rewrite H3 in H; try discr.
        inversion H. subst p. clear H.
        unfold pathOrder_rpo_proj_filter in H3.
        gen H3.
        
        set (b:= forallb
         (fun f : symbol =>
          forallb (fun g : symbol => bprec_eq_status_symb arity l f g)
            (list_sig l)) (list_sig l)).

       case_eq b; intros; subst b; try discr.
       inversion H0. clear H0.

       (* Filter (RPO) *)
       
       apply WF_rp_red with (WP:= @WP_Perm       (Sig arity)
                                  (Perm_Imp arity ls)
                                  (@WP_RPO rpo_n (Sig (@ASignature.arity
                                                 (color_perm_Sig arity ls)))
                                  (Precendence_Imp (@ASignature.arity
                                  (color_perm_Sig arity ls)) l rpo_n))).*)
      
      (*
      apply WF_rp_red with (WP:= @WP_Perm (Sig arity)
      (Perm_Imp arity ls)
      (@WP_Proj (Sig (@ASignature.arity (color_perm_Sig arity ls)))
                (@Proj_Imp (@ASignature.arity (color_perm_Sig arity ls)) ls)
                (@WP_RPO bb (Sig (@ASignature.arity (color_perm_Sig arity ls)))
                         (Precendence_Imp (@ASignature.arity
                               (color_perm_Sig arity ls)) l bb)))).*)

      (* Proving [>] is closed by context in [rpo]. *)
       (*
       apply cc_succ. 

      (** Check that all rules [R] are included in [>=] *)

      simpl; unfold brule, bsucceq.
      rewrite forallb_forall. intros x Hx.
      subst bge. clear H3.
      rewrite forallb_forall in H1.
      ded (H1 x Hx). destruct x as [u v].
      simpl in *.
      unfold brule in H0. unfold color_filter in H0.
      unfold color_proj in H0. 
      simpl in *.
      unfold bsucceq. unfold cpf2color.rpo_eval in H0. simpl in *. 
      unfold cpf2color.empty_rpo_infos in H0.
      apply H0.

      (** Remove all rules [R] are included in [>]. *)
      
      apply WF_incl with (S:= red (List.filter (brule (neg bgt))R)).
      unfold inclusion. intros u v H4. redtac. unfold red.
      exists l0. exists r. exists c. exists s0. intuition.
      apply filter_In. apply filter_In in lr. intuition.
      unfold brule, neg. unfold brule, neg in H. simpl in *.
      unfold bsucc in H4. simpl in *.
      subst bgt. hyp. hyp.

      (*
      case_eq (is_col_noncol t); intro H2; rewrite H2 in H; try discr.
      set (ls:= (s, a, t):: args). fold ls in H.
      case_eq (pathOrder_rpo_filter l ls);
        intros p H3; rewrite H3 in H; try discr.
      inversion H. subst p. clear H.
      unfold pathOrder_rpo_filter in H3.
      gen H3.

      set (b:= forallb
         (fun f : symbol =>
          forallb (fun g : symbol => bprec_eq_status_symb arity l f g)
            (list_sig l)) (list_sig l) &&
       bnon_dup (Sig arity) (color_raw_pi_filter arity ls) (Fs arity ls) &&
       bpermut (Sig arity) (color_raw_pi_filter arity ls) (Fs arity ls)).

      case_eq b; intros; subst b; try discr.
      inversion H0. clear H0.

      (* Filter (RPO) *)

      apply WF_rp_red with (WP:= @WP_Perm (Sig arity)
      (Perm_Imp arity ls)
      (@WP_RPO bb (Sig (@ASignature.arity (color_perm_Sig arity ls)))
               (Precendence_Imp (@ASignature.arity
                                   (color_perm_Sig arity ls)) l bb))).
      
      (*
      apply WF_rp_red with (WP:= @WP_Perm (Sig arity)
      (Perm_Imp arity ls)
      (@WP_Proj (Sig (@ASignature.arity (color_perm_Sig arity ls)))
                (@Proj_Imp (@ASignature.arity (color_perm_Sig arity ls)) ls)
                (@WP_RPO bb (Sig (@ASignature.arity (color_perm_Sig arity ls)))
                         (Precendence_Imp (@ASignature.arity
                               (color_perm_Sig arity ls)) l bb)))).*)

      (* Proving context closed of [succ]. *)

      apply filter_strong_cont_closed.
      do 2 rewrite andb_eq in H. do 2 destruct H.

      (* Verifying arguments are non-duplication. *)

      simpl. unfold color_build_pi. rewrite <- bnon_dup_ok.
      apply H4.

      (* Verifying if arguments are permutations. *)

      do 2 rewrite andb_eq in H. do 2 destruct H.
      simpl. unfold color_build_pi. rewrite <- bpermut_ok.
      apply H0. simpl.

      (* Proving [>] is closed by context in [rpo]. *)

      apply cc_succ. 

      (** Check that all rules [R] are included in [>=] *)

      simpl; unfold brule, bsucceq.
      rewrite forallb_forall. intros x Hx.
      subst bge. clear H3.
      rewrite forallb_forall in H1.
      ded (H1 x Hx). destruct x as [u v].
      simpl in *.
      unfold brule in H0. unfold color_filter in H0.
      unfold color_proj in H0. 
      simpl in *.
      unfold bsucceq. unfold cpf2color.rpo_eval in H0. simpl in *. 
      unfold cpf2color.empty_rpo_infos in H0.
      apply H0.

      (** Remove all rules [R] are included in [>]. *)
      
      apply WF_incl with (S:= red (List.filter (brule (neg bgt))R)).
      unfold inclusion. intros u v H4. redtac. unfold red.
      exists l0. exists r. exists c. exists s0. intuition.
      apply filter_In. apply filter_In in lr. intuition.
      unfold brule, neg. unfold brule, neg in H. simpl in *.
      unfold bsucc in H4. simpl in *.
      subst bgt. hyp. hyp.
    Qed.*)*)
      Admitted.

      (***********************************************************************)
      (** Define a function that return a type [result arules]. The path
       order in combination with the argument filter or without the
       argument filter. *) 
      (** In the case RPO + AF: there are three cases:
       that embedded RPO's term to AF's term:
       - RPO's term + AF's project term, in the case of collapsing
       - RPO's term + AF's perm term, in the case of non collapsing
       - RPO's term + AP's project and perm term. *)

      (* FIXME *)
      Definition pathOrder (R: arules) sp (af: option argumentFilter):
        cpf_util.result arules :=
        match af with
          | Some af => (* Combination with argument filter *)
            match pathOrder_term_rpo_af sp af with
              | Ok (bsucc_ge, bsucc_gt) =>
                if   forallb (ATrs.brule bsucc_ge) R
                then Ok (List.filter (ATrs.brule (neg bsucc_gt)) R)
                else Ko _ (Error ENotpathOrder_AF) (* FIXME: ERROR *)
              | Ko e                    => Ko _ e
            end
          | None    =>
            (* Without argument filter *)
            match pathOrder_term sp with
              | Ok (bsucc_ge, bsucc_gt) =>
                if   forallb (ATrs.brule bsucc_ge) R
                then Ok (List.filter (ATrs.brule (neg bsucc_gt)) R)
                else Ko _ (Error ENotpathOrder)
              | Ko e                    => Ko _ e
            end
        end.

      (*Definition pathOrder (R: arules) sp (af: option argumentFilter):
        cpf_util.result arules :=
        match af with
          | Some af => (* Combination with argument filter *)
            match pathOrder_term_rpo_af sp af with
              | Ok (bsucc_ge, bsucc_gt) =>
                if   forallb (ATrs.brule bsucc_ge) R
                then Ok (List.filter (ATrs.brule (neg bsucc_gt)) R)
                else Ko _ (Error ENotpathOrder_AF) (* FIXME: ERROR *)
              | Ko e                    => Ko _ e
            end
          | None    => (* Without argument filter *)
            match pathOrder_term sp with
              | Ok (bsucc_ge, bsucc_gt) =>
                if   forallb (ATrs.brule bsucc_ge) R
                then Ok (List.filter (ATrs.brule (neg bsucc_gt)) R)
                else Ko _ (Error ENotpathOrder)
              | Ko e                    => Ko _ e
            end
        end.*)

      (***********************************************************************)
      (* Correctness proof of recursive path ordering. *)

      Lemma pathOrdering_ok : forall (R R': arules) l o,
        pathOrder R l o = Ok R' -> WF (red R') -> WF (red R).
      
      Proof.
        (*intros R R' l o h wf.

        unfold pathOrder in h.

        destruct o; try discr.

        (** RPO with argument filtering method. *)

        apply rpo_with_af_ok with (R':=R')(args:=a)(l:=l).

        apply h. apply wf.
        
        (** RPO without argument filtering method. *)
        
        apply rpo_without_af_ok with (R':=R')(l:=l).

        hyp. hyp.
      Qed.*)
      Admitted.

    End rpo.

    (***********************************************************************)
    (** Ordering constrainst proof with reduction pair interpretation.
     REMARK: the patten condition that is in comment belongt to the
     case when using CPF version 2.1x. *)

    Definition redPair (R:arules) (rp: redPair) : cpf_util.result arules :=
      match rp with
        | RedPair_interpretation t is    => redPair_interpretation R t is
        | RedPair_pathOrder sp oaf       => pathOrder R sp oaf
        | RedPair_knuthBendixOrder _ _ _ => Ko _ (Todo TRedPair_knuthBendixOrder)
        | RedPair_scnp _ _ _             => Ko _ (Todo TRedPair_scnp)
      end.

    Definition ruleRemoval (R: arules) ocp :=
      match ocp with
        | OrderingConstraintProof_redPair rp              => redPair R rp
        | OrderingConstraintProof_satisfiableAssumption _ =>
          Ko _ (Todo TOrderingConstraintProof_satisfiableAssumption)
      end.

    (***********************************************************************)
    (** Relative termination of ordering constrainst proof with
     reduction pair interpretation. Ordering constrainst proof with
     reduction pair interpretation of dependency pair
     transformation. Currently support interpretation only. *)
    
    Definition rel_orderingConstraintProof_redPair (R D:arules) rp
    : cpf_util.result arules :=
      match rp with
        | RedPair_interpretation t is    => rel_redPair_interpretation R D t is
        | RedPair_pathOrder sp oaf       => pathOrder R sp oaf
        | RedPair_knuthBendixOrder _ _ _ => Ko _ (Todo TRedPair_knuthBendixOrder)
        | RedPair_scnp _ _ _             => Ko _ (Todo TRedPair_scnp)
      end.

    Definition rel_trsTerminationProof_ruleRemoval (R D: arules) ocp :=
      match ocp with
        | OrderingConstraintProof_redPair rp              =>
          rel_orderingConstraintProof_redPair R D rp
        | OrderingConstraintProof_satisfiableAssumption _ =>
          Ko _ (Todo TOrderingConstraintProof_satisfiableAssumption)
      end.

  End S.

  (***********************************************************************)
  (** ** Termination by using dependency proof compatible reduction
    orderings.

    WARNING: the list of DPs is reversed since in CPF, all forward
    arcs are given while in Rainbow, there must be no forward arcs.      *)
  (***********************************************************************)

  Section Top_Termination.
    
    Section poly_dp.
      
      (* REMARK: rulePoly_ge and rulePoly_gt are functions from
         APolyInt1. *)
      
      Require Import APolyInt2 cpf_util ARedPair2.
      
      Import OR_Notations.
      
      Open Scope Z_scope.

      Definition poly_nat_dp a (is: list (symbol * cpf.arity * function)) :
        result ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)) :=
        Match map_rev (@color_interpret a coef_ring_Z) is With l ===>
              if forallb (fun x         =>
                            match x with
                            existT f p  => bcoef_not_neg p
                            end) l
              then
                let pi := fun f : Sig a => fun_of_pairs_list a f l in
                Ok ((fun t u            => bcoef_not_neg (rulePoly_ge pi (mkRule t u))), 
                    (fun t u            => bcoef_not_neg (rulePoly_gt pi (mkRule t u))))
              else Ko _ (Error ENotMonotone_dp).

      (***********************************************************************)

      Lemma poly_nat_dp_ok : forall a (R D D': arules a) is
        (h:  match poly_nat_dp a is with
               | Ok (bsucc_ge, bsucc_gt) =>
                 if   forallb (brule bsucc_ge) D &&
                      forallb (brule bsucc_ge) R
                 then Ok (filter (brule (neg bsucc_gt)) D)
                 else Ko (list (ATrs.rule (Sig a))) (Error ERuleNotInLargeOrdering_dp)
               | Ko e                    => Ko (list (ATrs.rule (Sig a))) e
             end = Ok D')
        (wf: WF (hd_red_mod R D')), WF (hd_red_mod R D).
      
      Proof.
        intros a R D D' is h wf.

        case_eq (poly_nat_dp a is);
          intros p H; rewrite H in h; try discr.

        destruct p as [bge bgt].

        case_eq (forallb (ATrs.brule bge) D && forallb (ATrs.brule bge) R);
          intros H0; rewrite H0 in h; try discr.

        inversion h. subst D'. clear h.

        unfold poly_nat_dp in H. revert H.

        case (map_rev (color_interpret a) is);
          intros l H1; try discr.

        gen H1.

        set (b:=  forallb
                    (fun x : {f : symbol & poly (a f)} =>
                       let (f, p) := x in bcoef_not_neg p) l).

        case_eq b; intros H2 H3; subst b; try discr.

        inversion H3. clear H3.

        set (trsInt := (fun f: (Sig a) => fun_of_pairs_list a f l)).

        cut (forall f: (Sig a), pweak_monotone (trsInt f)).

        intros trsInt_wm.

        Focus 2.

        intro f. apply trsInt_wm_poly. hyp.
        
        apply WF_wp_hd_red_mod with (WP :=@WP _ _ l H2).
        
        (** Check that all rules [R] are included in [>=]. *)
        
        simpl. unfold brule, bsucceq, bool_of_rel; simpl.

        rewrite forallb_forall. intros x Hx. subst bge.

        rewrite andb_eq in H0. destruct H0.

        rewrite forallb_forall in H0. ded (H0 x Hx).

        destruct x as [t u]. simpl in *.

        destruct succeq'_dec; auto.

        unfold abrule, brule in H3.

        unfold succeq' in n.
        
        rewrite bcoef_not_neg_ok in H3. contradiction.
        
        (** Check that all rules [D = dp R] are included in [>=]. *)
        
        simpl. unfold brule, bsucceq, bool_of_rel; simpl.

        rewrite forallb_forall. intros x Hx. subst bge.

        rewrite andb_eq in H0.

        destruct H0.

        rewrite forallb_forall in H. ded (H x Hx).

        destruct x as [t u]. simpl in *.

        destruct succeq'_dec; auto.

        unfold brule in H3. unfold succeq' in n.

        rewrite bcoef_not_neg_ok in H3. contradiction.
        
        (** Remove all rules [D] that are included in [>]. *)

        apply WF_incl with (S := hd_red_mod R (filter (abrule (neg bgt)) D)).

        unfold inclusion.

        intros t u H3. redtac. (* TODO do not use focus *)

        Focus 2.

        hyp.

        unfold hd_red_mod. unfold compose.

        exists t0.

        split. hyp.

        unfold hd_red.

        exists l0. exists r. exists s.

        intuition.

        apply filter_In. apply filter_In in lr.

        intuition.

        unfold brule, neg. unfold brule, neg in H6. simpl in *.

        unfold bsucc, bool_of_rel in H6. simpl in *.

        destruct succ'_dec in H6. discr.

        unfold succ' in n0.

        rewrite <- bcoef_not_neg_ok in n0.

        apply eq_true_not_negb in n0. subst bgt.

        apply n0.
      Qed.

      Close Scope Z_scope.

      (***********************************************************************)
      (** Formalization of DP on polynomial interpertation on domain rational 
       REMARK: rulePoly for rational number : P_x - P_y - del >= 0 *)

      Require Import Q_as_R QArith.

      Open Scope Q_scope.
      
      Definition poly_rat_dp a (is: list (symbol * cpf.arity * function)) (del:Q):
        result ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)) :=
        Match map_rev (@color_interpret a coef_ring_Q) is With l ===>
              if forallb (fun x         =>
                            match x with
                             existT f p => bcoef_not_neg p
                            end) l
              then
                let pi := fun f : Sig a => fun_of_pairs_list a f l in
                Ok ((fun t u            => bcoef_not_neg
                    (@rulePoly_ge Q_as_OR (Sig a) pi (mkRule t u))),
                    (fun t u            => bcoef_not_neg
                    (@rulePoly_gtQ Q_as_OR (Sig a) pi del (mkRule t u))))
              else Ko _ (Error ENotMonotone_rat_dp).

      Definition type_poly_rationals_dp a del is :=
        match del with
          | Number_integer i      => poly_rat_dp a is (inject_Z i) (* i/1 *)
          | Number_rational i pos => let q := Qmake i pos in
                                     poly_rat_dp a is q
        end.

      (***********************************************************************)
      (** Correctness proof of DP on PI of domain rational. Common proof. *)

      Lemma poly_rationals_dp_common_ok: forall a del (R D D': arules a) is
        (H: match poly_rat_dp a is del with
              | Ok (bsucc_ge, bsucc_gt) =>
                if   forallb (brule bsucc_ge) D &&
                     forallb (brule bsucc_ge) R
                then Ok (filter (brule (neg bsucc_gt)) D)
                else Ko (list (ATrs.rule (Sig a))) (Error ERuleNotInLargeOrdering_dp)
              | Ko e                    => Ko (list (ATrs.rule (Sig a))) e
            end = Ok D')
        (wf: WF (hd_red_mod R D')), WF (hd_red_mod R D).
      
      Proof.
        intros a del R D D' is h wf.

        case_eq (poly_rat_dp a is del);
          intros p H; rewrite H in h; try discr.

        destruct p as [bge bgt].

        case_eq (forallb (brule bge) D && forallb (brule bge) R);
          intros H0; rewrite H0 in h; try discr.

        inversion h. subst D'. clear h.

        unfold poly_rat_dp in H.

        case_eq (map_rev (color_interpret a) is);
          intros l H1; rewrite H1 in H; try discr.

        gen H.

        set (b:= forallb (fun x : {f : symbol & poly (a f)} =>
                            let (f, p) := x in bcoef_not_neg p) l).

        case_eq b; intros H2 H3; subst b; try discr.

        inversion H3. clear H3.

        set (trsInt := (fun f: (Sig a) => fun_of_pairs_list a f l)).

        cut (forall f: (Sig a), pweak_monotone (trsInt f)).

        intros trsInt_wm.

        Focus 2. (* TODO: do not use focus *)

        intro f. apply trsInt_wm_poly. hyp.

        apply WF_wp_hd_red_mod with (WP:=@WP_Q _ _ l H2 del).

        (** Check that all rules [R] are included in [>=]. *)
        
        simpl. unfold brule, bsucceq, bool_of_rel; simpl.

        rewrite forallb_forall. intros x Hx. subst bge.

        rewrite andb_eq in H0. destruct H0.

        rewrite forallb_forall in H3. ded (H3 x Hx).

        destruct x as [t u]. simpl in *.

        destruct succeq'_dec; auto.

        unfold brule in H4. unfold succeq' in n.

        rewrite bcoef_not_neg_ok in H4. contradiction.
        
        (** Check that all rules [D = dp R] are included in [>=]. *)
        
        simpl. unfold brule, bsucceq, bool_of_rel; simpl.

        rewrite forallb_forall. intros x Hx. subst bge.

        rewrite andb_eq in H0. destruct H0.

        rewrite forallb_forall in H0. ded (H0 x Hx).

        destruct x as [t u]. simpl in *.

        destruct succeq'_dec; auto.

        unfold brule in H4. unfold succeq' in n0.

        rewrite bcoef_not_neg_ok in H4. contradiction.
        
        (** Remove all rules [D] that are included in [>]. *)

        apply WF_incl with (S := hd_red_mod R (filter (abrule (neg bgt)) D)).

        unfold inclusion.

        intros t u H3. redtac.

        Focus 2.

        hyp.

        unfold hd_red_mod. unfold compose. exists t0.

        split. hyp.

        unfold hd_red. exists l0. exists r. exists s.

        intuition.

        apply filter_In. apply filter_In in lr.

        intuition.

        unfold brule, neg. unfold brule, neg in H7.

        simpl in *. unfold bsucc, bool_of_rel in H7.

        simpl in *. destruct succQ'_dec in H7.

        discr.

        unfold succQ' in n0.

        rewrite <- bcoef_not_neg_ok in n0.

        apply eq_true_not_negb in n0.

        subst bgt. apply n0.
      Qed.

      (***********************************************************************)
      (** Correctness proof of DP on PI of domain rational. *)

      Lemma poly_rationals_dp_ok: forall a n (R D D': arules a) is
        (h: match type_poly_rationals_dp a n is with
              | Ok (bsucc_ge, bsucc_gt) =>
                if   forallb (brule bsucc_ge) D &&
                     forallb (brule bsucc_ge) R
                then Ok (filter (brule (neg bsucc_gt)) D)
                else Ko (list (ATrs.rule (Sig a))) (Error ERuleNotInLargeOrdering_dp)
              | Ko e                    => Ko (list (ATrs.rule (Sig a))) e
            end = Ok D')
        (wf : WF (hd_red_mod R D')), WF (hd_red_mod R D).

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
          | Domain_naturals               => poly_nat_dp a is
          | Domain_integers               => Ko _ (Todo Ttype_polynomialDomain_integers)
          | Domain_rationals del          => type_poly_rationals_dp a del is
          | Domain_arctic dom'            => Ko _ (Todo Ttype_polynomialDomain_arctic)
          | Domain_tropical dom'          => Ko _ (Todo Ttype_polynomialDomain_tropical)
          | Domain_matrices dim sdim dom' => Ko _ (Todo Ttype_polynomialDomain_matrices)
        end.

      Definition polynomial_interpretation_dp a (R D: arules a) is dom:
        result (arules a) :=
        match type_polynomial_dp a is dom with
          | Ok (bsucc_ge, bsucc_gt) =>
            if   forallb (ATrs.brule bsucc_ge) D &&
                         forallb (ATrs.brule bsucc_ge) R
            then Ok (filter (ATrs.brule (neg bsucc_gt)) D)
            else Ko _ (Error ERuleNotInLargeOrdering_dp)
          | Ko e                    => Ko _ e
        end.

      (***********************************************************************)
      (** Correctness proof of DP on PI *)

      Lemma polynomial_interpretation_dp_ok: forall a (R D D': arules a) is (d:domain)
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

    End poly_dp.

    (***********************************************************************)
    (* Formalization of DP on matrix interpretation of domain natural
  numbers. *)

    Section matrix_nat_dp.
      
      (* REMARK: the relation is [bge], rule_mi need to give the
    paramater of Nat_as_OSR if not COQ will not compile *)

      Import OSR_Notations.

      Definition matrix_nat_dp a (is: list (symbol * cpf.arity * function)) (dim: nat):
        result ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)) :=
        Match map_rev (@color_interpret_matrix a dim coef_sring_N) is With l ===>
              if forallb (fun x =>
                            match x with
                              existT f mi   => bVforall (fun m =>
                              bge Nat_as_OSR (get_elem m (dim_pos dim) (dim_pos dim)) 0)
                              (args mi)
                            end) l
              then
                let Conf := @TMatrix_Conf a dim l in
                Ok (fun t u      => let (l, r) :=
                     @rule_mi _ _ dim Conf (mkRule t u) in bmint_ge l r,
                   (fun t u      => let (l, r) :=              
                     rule_mi (mkRule t u) in bmint_gt_nat l r))
              else Ko _ (Error ENotMonotone_matrix_naturals_dp).

      Definition type_matrix_dp a is dom dim :=
        match dom with
          | Domain_naturals               => matrix_nat_dp a is dim
          | Domain_integers               => Ko _ (Todo Ttype_polynomialDomain_integers)
          | Domain_rationals delta        => Ko _ (Todo Ttype_polynomialDomain_rationals)
          | Domain_arctic dom'            => Ko _ (Todo Ttype_polynomialDomain_arctic)
          | Domain_tropical dom'          => Ko _ (Todo Ttype_polynomialDomain_tropical)
          | Domain_matrices dim sdim dom' => Ko _ (Todo Ttype_polynomialDomain_matrices)
        end.

      Definition matrix_interpretation_dp a (R D: arules a) is dom dim:
        result (arules a) :=
        match type_matrix_dp a is dom dim with
          | Ok (bsucc_ge, bsucc_gt) =>
            if   forallb (abrule bsucc_ge) D &&
                         forallb (abrule bsucc_ge) R
            then Ok (filter (abrule (neg bsucc_gt)) D)
            else Ko _ (Error ERuleNotInLargeOrdering_matrix_nat_dp)
          | Ko e                    => Ko _ e
        end.

      (***********************************************************************)
      (** Correctness proof of matrix int of domain nat *)

      Require Import AMatrixInt2.

      Lemma matrix_interpretation_dp_ok : forall a (R D D': arules a)(d:dimension) is
        (h: matrix_interpretation_dp R D is Domain_naturals (Pos.to_nat d) = Ok D')
        (wf : WF (hd_red_mod R D')), WF (hd_red_mod R D).

      Proof.
        intros a R D D' d is h wf.

        unfold matrix_interpretation_dp in h.

        destruct Domain_naturals; simpl in h; try discr.

        case_eq (matrix_nat_dp a is (Pos.to_nat d));
          intros p H; rewrite H in h; try discr.

        destruct p as [bge bgt].

        case_eq (forallb (abrule bge) D && forallb (abrule bge) R);
          intro H0; rewrite H0 in h; try discr.

        inversion h. subst D'. clear h.

        unfold matrix_nat_dp in H.

        revert H.

        case (map_rev (color_interpret_matrix a (Pos.to_nat d)) is);
          intros l H1; try discr. gen H1.

        set (b:=  forallb
                    (fun x : {f : symbol & matrixInt (Pos.to_nat d) (a f)} =>
                       let (f, mi) := x in
                       bVforall
                         (fun m : matrix (Pos.to_nat d) (Pos.to_nat d) =>
                            OrdSemiRing2.bge Nat_as_OSR
                           (get_elem m (dim_pos (Pos.to_nat d)) (dim_pos (Pos.to_nat d)))
                           0) (args mi)) l).

        case_eq b; intros H2 H3; subst b; try discr.

        inversion H3. clear H3.

        apply WF_wp_hd_red_mod with (WP:=@WP_Matrix_Nat _ _ l).
        
        (** Check that rules [R] is included in [>=]. *)
        
        unfold brule, bsucceq, bool_of_rel; simpl.

        rewrite forallb_forall. intros x Hx. subst bge.

        rewrite andb_eq in H0. destruct H0. 

        rewrite forallb_forall in H0.

        ded (H0 x Hx). destruct x as [t u]. simpl in *.

        unfold bsucceq, bool_of_rel.

        destruct ma_succeq'_dec; auto.

        unfold abrule, brule in H3. simpl in *.

        unfold AMatrixBasedInt2.succeq', succeq', term_ge, term_ord, mint_ge in n0.

        apply bmint_ge_ok in H3. contradiction.
        
        (** Check that rules [D = dp R] is included in [>=]. *)
        
        unfold brule, bsucceq, bool_of_rel; simpl.

        rewrite forallb_forall. intros x Hx. subst bge.

        rewrite andb_eq in H0. destruct H0.

        rewrite forallb_forall in H.

        ded (H x Hx). destruct x as [t u]. simpl in *.

        unfold bsucceq, bool_of_rel.

        destruct ma_succeq'_dec; auto.

        unfold abrule, brule in H3.

        simpl in *.

        unfold AMatrixBasedInt2.succeq', succeq', term_ge, term_ord, mint_ge in n0.

        apply bmint_ge_ok in H3. contradiction.

        (** Remove all rules [>] in [D]. *)
        
        apply WF_incl with (S := hd_red_mod R (filter (abrule (neg bgt)) D)).

        unfold inclusion. intros t u H3. redtac.

        unfold hd_red_mod. unfold compose.

        exists t0. split. hyp.

        unfold hd_red.

        exists l0. exists r. exists s.

        intuition.

        apply filter_In. apply filter_In in lr.

        intuition.

        unfold abrule, brule, neg.

        unfold brule, neg in H6. simpl in *.

        unfold bsucc, bool_of_rel in H6.

        destruct ma_succ'_dec in H6; try discr. simpl in *.

        unfold term_gt, AMatrixBasedInt2.term_gt, term_ord in n0;
          simpl in *.

        unfold mint_gt in n0.

        rewrite <- bmint_gt_ok in n0.

        apply eq_true_not_negb in n0.

        subst bgt. apply n0. hyp.
      Qed.

    End matrix_nat_dp.

    (***********************************************************************)
    (** Matrix interpretation of domain arctic natural numbers. *)


    Section matrix_arctic_nat.

      (* REMARK: need to give the return type if not COQ will
    complain. *)

      (* TODO: define trsInt_matrix for arctic nat, MonotoneAlgebra,
    Conf, WP *)

      (* MOVE *)

      Require Import AArcticBasedInt2 Arctic_as_OSR AArcticInt2.

      Section weakRedPair.
        
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
          
          (*Definition of weakRedPair of matrix int *)
          
          Definition WP_Matrix_ArcNat := @WP_MonAlg (Sig arity) TM_Mon_ArcNat.

      End weakRedPair.

      Require Import AArcticBasedInt2 Arctic_as_OSR AArcticInt2.

      Definition matrix_arctic_nat a (is: list (symbol * cpf.arity * function)) (dim: nat) :
        result ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)):=
        Match map_rev (@color_interpret_matrix a dim coef_sring_arc_nat) is With l ===>
              if forallb (fun l =>
                            match l with
                                existT f mi   => bVexists (fun m =>
                                is_finite (get_elem m (dim_pos dim)(dim_pos dim))) (args mi)
                            ||  is_finite (Vnth (const mi) (dim_pos dim))
                            end) l
              then
                (* REMARK: need to define Conf here *)
                let Conf    := TM_Conf_ArcNat a l            in
                Ok (fun t u     =>
                      let (l, r)  := @rule_mi _ _ dim _ (mkRule t u) in
                      bmint_ge l r,
                      (fun t u     =>
                         let (l, r)  := rule_mi (mkRule t u)               in
                         bmint_gt l r))
              else Ko _ (Error ENotMonotone_matrix_arc_naturals).

      (* TODO: TTT10 generate the CPF file in the domain_matrices
     and in the arctic integer only *)
      
      Definition type_matrix_arctic a is dom dim :=
        match dom with
          | Domain_naturals               => matrix_arctic_nat a is dim
          | Domain_integers               => Ko _ (Todo Ttype_polynomialDomain_integers)
          | Domain_rationals delta        => Ko _ (Todo Ttype_polynomialDomain_rationals)
          | Domain_arctic dom'            => Ko _ (Todo Ttype_polynomialDomain_arctic)
          | Domain_tropical dom'          => Ko _ (Todo Ttype_polynomialDomain_tropical)
          | Domain_matrices dim sdim dom' => Ko _ (Todo Ttype_polynomialDomain_matrices)
        end.

      (** Given two orders [>], [>=], they are compatible. However
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

      Definition matrix_interpretation_arctic_nat a (R D: arules a) is dom dim :=
        match type_matrix_arctic a is dom dim with
          | Ok (bsucc_ge, bsucc_gt) =>
            if   forallb (abrule bsucc_ge) D &&
                         forallb (abrule bsucc_ge) R
            then Ok (filter (abrule (neg bsucc_gt)) D)
            else Ko _ (Error ERuleNotInLargeOrdering_matrix_arc_naturals)
          | Ko e                    => Ko _ e
        end.

      (***********************************************************************)
      (** Correctness proof for DP on MI on domain Arctic natural numbers. *)

      Require Import ARedPair2.

      Lemma matrix_interpretation_arctic_nat_ok : forall a (R D D': arules a)
        (d:dimension) is
        (h: matrix_interpretation_arctic_nat R D is Domain_naturals (Pos.to_nat d) = Ok D')
        (wf : WF (hd_red_mod R D')), WF (hd_red_mod R D).
      
      Proof.
        intros a R D D' d is h wf.

        unfold matrix_interpretation_arctic_nat in h.

        destruct Domain_naturals; simpl in h; try discr.

        case_eq (matrix_arctic_nat a is (Pos.to_nat d)); intros p H;
        rewrite H in h; try discr.

        destruct p as [bge bgt].

        case_eq (forallb (abrule bge) D && forallb (abrule bge) R);
          intro H0; rewrite H0 in h; try discr.

        inversion h. subst D'. clear h.

        unfold matrix_arctic_nat in H.

        case_eq (map_rev (color_interpret_matrix a (Pos.to_nat d)) is);
          intros l H1; rewrite H1 in H; try discr.

        gen H.

        set (b:= forallb
            (fun l0 : {f : symbol & matrixInt (Pos.to_nat d) (a f)} =>
             let (f, mi) := l0 in
             bVexists
             (fun m : matrix (Pos.to_nat d) (Pos.to_nat d) =>
              is_finite (@get_elem Arctic_as_OSR  (Pos.to_nat d) (Pos.to_nat d) m _ _
                        (dim_pos (Pos.to_nat d))(dim_pos (Pos.to_nat d))))
       (args mi) || is_finite (Vnth (const mi)(dim_pos (Pos.to_nat d)))) l).

        case_eq b; intros H2 H3; subst b; try discr.

        inversion H3. clear H3.

        apply WF_wp_hd_red_mod with (WP:=@WP_Matrix_ArcNat _ _ l).

        (** Check that rules [R] is included in [>=]. *)
        
        unfold brule, bsucceq, bool_of_rel; simpl.

        rewrite forallb_forall. intros x Hx. subst bge.

        rewrite andb_eq in H0. destruct H0.

        rewrite forallb_forall in H3.

        ded (H3 x Hx). destruct x as [t u]. simpl in *.

        unfold bsucceq, bool_of_rel.

        destruct ma_succeq'_dec; auto; try discr.

        unfold abrule, brule in H4. simpl in *.

        unfold succeq', AMatrixBasedInt2.succeq', term_ge, term_ord, mint_ge in n0.

        apply bmint_ge_ok in H4. try contradiction.
        
        (** Check that rules [D = dp R] is included in [>=]. *)
        
        unfold brule, bsucceq, bool_of_rel; simpl.

        rewrite forallb_forall. intros x Hx. subst bge.

        rewrite andb_eq in H0. destruct H0.

        rewrite forallb_forall in H0.

        ded (H0 x Hx). destruct x as [t u]. simpl in *.

        unfold bsucceq, bool_of_rel.

        destruct ma_succeq'_dec; auto.

        unfold abrule, brule in H4. simpl in *.

        unfold succeq', AMatrixBasedInt2.succeq', term_ge, term_ord, mint_ge in n0.

        apply bmint_ge_ok in H4. try contradiction.
        
        (** Remove all rules [>] in [D]. *)

        apply WF_incl with (S := hd_red_mod R (filter (abrule (neg bgt)) D)).

        unfold inclusion.

        intros t u H3. redtac.

        unfold hd_red_mod.
        unfold compose.

        exists t0. split. hyp.

        unfold hd_red.

        exists l0. exists r. exists s.

        intuition.

        apply filter_In. apply filter_In in lr.

        intuition.

        unfold brule, neg.

        unfold brule, neg in H7. simpl in *.

        unfold bsucc, bool_of_rel in H7.

        destruct ma_succ'_dec in H7; try discr.

        simpl in *.

        unfold term_gt, AMatrixBasedInt2.term_gt, term_ord, mint_gt in n0.

        simpl in *.

        rewrite <- bmint_gt_ok in n0.

        apply eq_true_not_negb in n0.

        subst bgt. apply n0. hyp.
      Qed.

    End matrix_arctic_nat.

    (***********************************************************************)
    (** Matrix interpretation of domain arctic integer numbers. *)

    Require Import ArcticBZ_as_OSR AArcticBZInt2.

    Section matrix_arctic_int.

      (* MOVE *)
      
      Section weakRedPair.
        
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
          
      End weakRedPair.
      
      (* REMARK: need to give the return type if not COQ will complain. *)

      Definition matrix_arctic_int a (is: list (symbol * cpf.arity * function)) (dim: nat) : 
        result ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)):=
        Match map_rev (@color_interpret_matrix a dim coef_sring_arc_int) is With l ===>
              if forallb (fun l =>
                match l with
                 existT f mi =>
                 is_above_zero (@Vnth ArcticBZDom dim (const mi) _ (dim_pos dim))
                end) l
              then
                (* REMARK: need to define Conf here. *)
                let Conf    := @TM_Conf_ArcInt a dim l         in
                Ok (fun t u     =>
                      let (l, r)  := @rule_mi _ _ dim Conf (mkRule t u) in
                      bmint_ge l r,
                      (fun t u =>
                         let (l, r)  := rule_mi (mkRule t u)            in
                         bmint_gt l r))
              else Ko _ (Error ENotMonotone_matrix_arc_naturals). 

      (* TODO: TTT10 generate the CPF file in the domain_matrices
       and in the arctic integer only *)
      
      Definition type_matrix_arctic_int a is dom dim :=
        match dom with
          | Domain_naturals               => Ko _ (Todo Ttype_polynomialDomain_naturals)
          | Domain_integers               => matrix_arctic_int a is dim
          | Domain_rationals delta        => Ko _ (Todo Ttype_polynomialDomain_rationals)
          | Domain_arctic dom'            => Ko _ (Todo Ttype_polynomialDomain_arctic)
          | Domain_tropical dom'          => Ko _ (Todo Ttype_polynomialDomain_tropical)
          | Domain_matrices dim sdim dom' => Ko _ (Todo Ttype_polynomialDomain_matrices)
        end.
      
      Definition matrix_interpretation_arctic_int a (R D: arules a) is dom dim:=
        match type_matrix_arctic_int a is dom dim with
          | Ok (bsucc_ge, bsucc_gt) =>
            if   forallb (abrule bsucc_ge) D &&
                         forallb (abrule bsucc_ge) R
            then Ok (filter (abrule (neg bsucc_gt)) D)
            else Ko _ (Error ERuleNotInLargeOrdering_matrix_arcbz_dp)
          | Ko e                    => Ko _ e
        end.

      (***********************************************************************)
      (** Correctness proof of matrix int of domain arctic integers. *)

      Require Import ArcticBZ_as_OSR SemiRing.

      Lemma matrix_interpretation_arctic_int_ok : forall a (R D D': arules a)
        (d: dimension) is
        (h: matrix_interpretation_arctic_int R D is Domain_integers (Pos.to_nat d) = Ok D')
        (wf: WF (hd_red_mod R D')), WF (hd_red_mod R D).
      
      Proof.
        intros a R D D' d is h wf.

        unfold matrix_interpretation_arctic_int in h.

        destruct Domain_integers; simpl in h; try discr.

        case_eq (matrix_arctic_int a is (Pos.to_nat d));
          intros p H; rewrite H in h; try discr.

        destruct p as [bge bgt].

        case_eq (forallb (abrule bge) D && forallb (abrule bge) R);
          intro H0; rewrite H0 in h; try discr.

        inversion h. subst D'. clear h.

        unfold matrix_arctic_int in H.

        case_eq (map_rev (color_interpret_matrix a (Pos.to_nat d)) is);
          intros l H1; rewrite H1 in H; try discr.
       
        gen H.

        set (b:=forallb
         (fun l0 : {f : symbol & matrixInt (Pos.to_nat d) (a f)} =>
          let (f, mi) := l0 in
          is_above_zero (@Vnth ArcticBZDom _ (@const ArcticBZ_as_OSR _ _ mi) _
          (dim_pos (Pos.to_nat d)))) l).

        case_eq b; intros H2 H3; subst b; try discr.

        inversion H3. clear H3.

        apply WF_wp_hd_red_mod with (WP:=@WP_Matrix_ArcInt _ _ l).

        (** Check that rules [R] is included in [>=]. *)

        unfold brule, bsucceq, bool_of_rel; simpl.

        rewrite forallb_forall. intros x Hx. subst bge.
     
        rewrite andb_eq in H0. destruct H0.

        rewrite forallb_forall in H3.

        ded (H3 x Hx). destruct x as [t u]. simpl in *.

        unfold bsucceq, bool_of_rel.

        destruct ma_succeq'_dec; auto; try discr.

        unfold abrule, brule in H4. 

        simpl in *.

        unfold succeq', AMatrixBasedInt2.succeq', term_ge, term_ord, mint_ge in n0.

        apply bmint_ge_ok in H4. try contradiction.
        
        (** Check that rules [D = dp R] is included in [>=]. *)
        
        unfold brule, bsucceq, bool_of_rel; simpl.

        rewrite forallb_forall. intros x Hx. subst bge.

        rewrite andb_eq in H0. destruct H0.

        rewrite forallb_forall in H0.

        ded (H0 x Hx). destruct x as [t u]. simpl in *.

        unfold bsucceq, bool_of_rel.

        destruct ma_succeq'_dec; auto.

        unfold abrule, brule in H4.

        simpl in *.

        unfold succeq', AMatrixBasedInt2.succeq', term_ge, term_ord, mint_ge in n0.

        apply bmint_ge_ok in H4. try contradiction.
        
        (** Remove all rules [>] in [D]. *)

        apply WF_incl with (S := hd_red_mod R (filter (abrule (neg bgt)) D)).

        unfold inclusion. intros t u H3. redtac.

        unfold hd_red_mod. unfold compose.

        exists t0. split. hyp.

        unfold hd_red.

        exists l0. exists r. exists s.

        intuition.

        apply filter_In. apply filter_In in lr.

        intuition.

        unfold brule, neg.

        unfold brule, neg in H7. simpl in *.

        unfold bsucc, bool_of_rel in H7.

        destruct ma_succ'_dec in H7; try discr.

        simpl in *.

        unfold term_gt, AMatrixBasedInt2.term_gt, term_ord, mint_gt in n0.

        simpl in *.

        rewrite <- bmint_gt_ok in n0.

        apply eq_true_not_negb in n0.

        subst bgt. apply n0. hyp.
      Qed.

    End matrix_arctic_int.

    (***********************************************************************)
    (** Matrix interpretation on different domains of arctic. *)

    Definition matrix_interpretation_arctic a (R D: arules a) dom dim is :=
      match dom with
        | Domain_naturals       =>
          matrix_interpretation_arctic_nat R D is dom (nat_of_P dim)
        | Domain_integers       =>
          matrix_interpretation_arctic_int R D is dom (nat_of_P dim)
        | Domain_rationals _    => Ko _ (Todo Ttype_polynomialDomain_rationals)
        | Domain_arctic _       => Ko _ (Todo Ttype_polynomialDomain_arctic)
        | Domain_tropical _     => Ko _ (Todo Ttype_polynomialDomain_tropical)
        | Domain_matrices _ _ _ => Ko _ (Todo Ttype_polynomialDomain_matrices)
      end.

    Definition type_matrix_interpretation_dp a (R D: arules a) is dom dim :=
      match dom with
        | Domain_naturals               => matrix_interpretation_dp R D is dom (nat_of_P dim)
        | Domain_integers               => Ko _ (Todo Ttype_polynomialDomain_integers)
        | Domain_rationals delta        => Ko _ (Todo Ttype_polynomialDomain_rationals)
        | Domain_tropical _             => Ko _ (Todo Ttype_polynomialDomain_tropical)
        | Domain_arctic dom'            => matrix_interpretation_arctic R D dom' dim is
        | Domain_matrices dim sdim dom' => Ko _ (Todo Ttype_polynomialDomain_matrices)
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

       c. Domain Arctic integer numbers.
     *)

    Lemma redPair_interpretation_dp_ok : forall a (R D D' : arules a) t is,
      redPair_interpretation_dp R D t is = Ok D' ->
      WF (hd_red_mod R D') -> WF (hd_red_mod R D).

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
    
    (***********************************************************************)
    (** ** Reduction pair path ordering is an ordering introduced by
  Dershowitz. It extends a well-founded order on the signature, called
  a precedence, to a reduction order on terms. We used the
  Coccinelle's library. *)

    Require Import ordered_set Coccinelle2 Coccinelle rpo2.

    Section rpo_dp.
      
      (** Path ordering without argument filtering method. The ordering
        (>=, >) is taken from [bsucceq and bsucc] in
        [Coccinelle2.v]. *)

      (* FIXME: take a look at list reverse: it is not the reverse list. *)

      Definition pathOrder_term_dp a
                 (l: list (symbol * cpf.arity * nonNegativeInteger * t10)) :
        cpf_util.result ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)) :=
        if forallb (fun f => forallb (fun g =>
                             @cpf2color.bprec_eq_status_symb a l f g) (list_sig l))(list_sig l)
        then
          Ok ((fun t u =>
                 let t' := @term_of_aterm (Sig a) t     in
                 let u' := @term_of_aterm (Sig a) u     in
                 match cpf2color.rpo_eval l rpo_n t' u' with
                   | Some Equivalent | Some Greater_than => true
                   | _                                   => false
                 end),     
              (fun t u =>
                 let t' := @term_of_aterm (Sig a) t     in
                 let u' := @term_of_aterm (Sig a) u     in
                 match cpf2color.rpo_eval l rpo_n t' u' with
                   | Some Greater_than                   => true
                   | _                                   => false
                 end))
        else Ko _ (Error ENotpathOrder_term).

      (***********************************************************************)
      (** RPO without Argument filtering method. *)

      Lemma rpo_without_af_dp_ok: forall a (R D D': arules a) l
        (h: match pathOrder_term_dp a l with
              | Ok (bsucc_ge, bsucc_gt) =>
                if   forallb (abrule bsucc_ge) D &&
                     forallb (abrule bsucc_ge) R
                then Ok (filter (abrule (neg bsucc_gt)) D)
                else Ko (arules a) (Error ENotpathOrder_dp)
              | Ko e                   => Ko (arules a) e
            end = Ok D')
        (wf : WF(hd_red_mod R D')), WF(hd_red_mod R D).
      
      Proof.
        intros a R D D' l h wf.

        case_eq (pathOrder_term_dp a l); intros p H;
        rewrite H in h; try discr.

        destruct p as [bge bgt].

        case_eq (forallb (abrule bge) D && forallb (abrule bge) R);
          intros H1; rewrite H1 in h; try discr.

        inversion h. subst D'. clear h.

        unfold pathOrder_term_dp in H.

        gen H.

        set (b:= forallb (fun f : symbol =>
                 forallb (fun g : symbol => cpf2color.bprec_eq_status_symb a l f g)
                         (list_sig l)) (list_sig l)).

        case_eq b; intros; subst b; try discr.

        inversion H2. clear H2.
        
        apply WF_wp_hd_red_mod with (WP:= @WP_RPO rpo_n (Sig a)
                                    (Precendence_Imp a l rpo_n)).

        (** Check that all rules [R] are included in [>=] *)

        simpl. unfold brule, bsucceq; simpl.

        rewrite forallb_forall. intros x Hx. subst bge.

        rewrite andb_eq in H1. destruct H1.

        rewrite forallb_forall in H2.

        ded (H2 x Hx).

        destruct x as [t u]. simpl in *.

        unfold abrule in H3. apply H3.

        (** Check that all rules in [D = dp R] are included in [>=]. *)
        
        simpl. unfold brule, bsucceq; simpl.

        rewrite forallb_forall. intros x Hx. subst bge.

        rewrite andb_eq in H1. destruct H1.

        rewrite forallb_forall in H1.

        ded (H1 x Hx).

        destruct x as [t u]. simpl in *.

        unfold abrule, brule in H3. apply H3.

        (** Remove all rules [D] that are included in [>]. *)

        apply WF_incl with (S:= hd_red_mod R (filter (brule (neg bgt)) D)).

        unfold inclusion. intros t u H3. redtac.

        unfold hd_red_mod. unfold compose.

        exists t0. split. hyp.

        unfold hd_red.

        exists l0. exists r. exists s.

        intuition.

        apply filter_In. apply filter_In in lr.

        intuition.

        unfold brule, neg.

        unfold brule, neg in H6.

        simpl in *. subst bgt.

        apply H6. hyp.
      Qed.

      (**************************************************************************)
      (** Path ordering with argument filtering method. *)

      Open Scope nat_scope. 

      (* FIXME *)
      (** Define a function checking each cases of argument filter.
       check if they used collapsing/non-collapsing then use the rpo +
       projection + perm, otherwise return [error]. *)

      (* FIXME *)
      Definition pathOrder_rpo_proj_filter_dp a
                 (l: list (symbol * cpf.arity * nonNegativeInteger * t10))
                 (args : list (symbol * cpf.arity * t11)):
        cpf_util.result ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)) :=
        if forallb (fun f => forallb (fun g =>
           @cpf2color.bprec_eq_status_symb a l f g)(list_sig l))(list_sig l)
        then
          Ok ((fun t u =>
                 let sig := Sig (@ASignature.arity (
                            Sig (filter_arity (Sig a) (color_build_pi_filter args))))  in
                 let t'  := @term_of_aterm sig
                            ((@color_filter a args t))          in
                 let u'  := @term_of_aterm sig
                            ((@color_filter a args u))          in
                 match cpf2color.rpo_eval l rpo_n t' u' with
                   | Some Equivalent | Some Greater_than => true
                   | _                                   => false
                 end),
              (fun t u =>
                 let sig := Sig (@ASignature.arity (
                            Sig (filter_arity (Sig a) (color_build_pi_filter args))))  in
                 let t'  := @term_of_aterm sig
                            ((@color_filter a args t))          in
                 let u'  := @term_of_aterm sig
                            ((@color_filter a args u))          in
                 match cpf2color.rpo_eval l rpo_n t' u' with
                   | Some Greater_than                   => true
                   | _                                   => false
                 end))
        else Ko _ (Error EPrecedence_incompatible_statuses_dp).

      (***********************************************************************)
      (** Define a function checking each cases of argument filter.
       Check if it is a collapsing case then use the rpo + projection,
       otherwise check if it is a non collapsing then use the rpo +
       perm, check if they used both cases then use the rpo +
       projection + perm, otherwise return [error].  *)

      (* FIXME: do I need to add any boolean condition ? *)

      (* If it is an empty list then return an error message, if it is a
    list then use the path ordering. *)

      Definition pathOrder_term_rpo_af_dp a
                 (l: list (symbol * cpf.arity * nonNegativeInteger * t10))
                 (args : list (symbol * cpf.arity * t11)) :
        cpf_util.result ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)) :=
        if   is_empty args
        then Ko _ (Error EargumentFilter_nil)
        else Match pathOrder_rpo_proj_filter_dp a l args With
                   rpo_filter_proj ===> Ok rpo_filter_proj.

      (*Definition pathOrder_term_rpo_af_dp a
      (l: list (symbol * cpf.arity * nonNegativeInteger * t10))
      (args : list (symbol * cpf.arity * t11)) :
      cpf_util.result ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)) :=
      match args with
        | (_, _, t) :: _ =>
          match is_col_noncol t with
            | true       =>   Match pathOrder_rpo_proj_filter_dp a l args With
                              rpo_filter_proj
                         ===> Ok rpo_filter_proj
            | false      =>   Ko _ EargumentFilter_false
          end
        | nil            => Ko _ EargumentFilter_nil
      end.*)

      (***********************************************************************)
      (** RPO with argument filtering method. *)

      Lemma rpo_with_af_dp_ok: forall a (R D D': arules a) l o
        (h: match pathOrder_term_rpo_af_dp a l o with
              | Ok (bsucc_ge, bsucc_gt) =>
                if   forallb (abrule bsucc_ge) D &&
                     forallb (abrule bsucc_ge) R
                then Ok (List.filter (abrule (neg bsucc_gt)) D)
                else Ko (arules a) (Error ENotpathOrder_AF_dp) (* FIXME: ERROR *)
              | Ko e                    => Ko (arules a) e
            end = Ok D')
        (wf: WF (hd_red_mod R D')), WF (hd_red_mod R D).

      Proof.
        intros a R D D' l oaf h wf.

        case_eq (pathOrder_term_rpo_af_dp a l oaf);
          intros p H; rewrite H in h; try discr.

        destruct p as [bge bgt].

        case_eq (forallb (abrule bge) D && (forallb (abrule bge) R));
          intros H1; rewrite H1 in h; try discr.

        inversion h. subst D'. clear h.

        unfold pathOrder_term_rpo_af_dp in H.

        destruct oaf; try discr.
        
        destruct p; try discr.

        destruct p; try discr.

      (*
      case_eq (is_collapsing t); intros H2; rewrite H2 in H; try discr.

      Focus 2.

      case_eq (is_nonCollapsing t); intros H3; rewrite H3 in H; try discr.

      Focus 2.*)
        
      (* TODO *)
      (** Argument filtering method. *)
        
      (*
      case_eq (is_col_noncol t); intros H2; rewrite H2 in H; try discr.
      set (ls:=(s,a0,t)::oaf). fold ls in H.
      case_eq (pathOrder_rpo_proj_filter_dp a l ls); intros p H3;
      rewrite H3 in H; try discr.
      inversion H. clear H. subst p.
      unfold pathOrder_rpo_proj_filter_dp in H3.
      gen H3.
      set (b:= forallb
         (fun f : symbol =>
          forallb (fun g : symbol => cpf2color.bprec_eq_status_symb a l f g)
            (list_sig l)) (list_sig l)).
      case_eq b; intros; subst b; try discr.
      inversion H0. clear H0.
      
      apply WF_wp_hd_red_mod with (WP:= @WP_Perm (Sig a)
      (Perm_Imp a ls)
      (@WP_Proj (Sig (@ASignature.arity (color_perm_Sig a ls)))
                (@Proj_Imp (@ASignature.arity (color_perm_Sig a ls)) ls)
                (@WP_RPO rpo_n (Sig (@ASignature.arity (color_perm_Sig a ls)))
                         (Precendence_Imp (@ASignature.arity
                                             (color_perm_Sig a ls)) l rpo_n)))).

      (** Check that all rules [R] are included in [>=] *)

      simpl. unfold brule, bsucceq; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H1. destruct H1.
      rewrite forallb_forall in H1.
      ded (H1 x Hx).
      destruct x as [u v]. simpl in *.
      unfold abrule in H4. apply H4.

      (** Check that all rules in [D = dp R] are included in [>=]. *)
      
      simpl. unfold brule, bsucceq; simpl.
      rewrite forallb_forall. intros x Hx. subst bge.
      rewrite andb_eq in H1. destruct H1.
      rewrite forallb_forall in H0.
      ded (H0 x Hx).
      destruct x as [u v].
      simpl in *.
      unfold brule in H4. apply H4.
      
      (** Remove all rules [D] that are included in [>]. *)

      apply WF_incl with (S:= hd_red_mod R (List.filter (brule (neg bgt)) D)).
      unfold inclusion. intros u v H7. redtac.
      unfold hd_red_mod. unfold compose.
      exists t0. split. hyp.
      unfold hd_red. exists l0. exists r.
      exists s0. intuition.
      apply filter_In. apply filter_In in lr. intuition.
      unfold brule, neg. unfold brule, neg in H7.
      simpl in *. subst bgt.
      apply H7. hyp.
    Qed.*)
      Admitted.

      (***********************************************************************)
      (** Define a function that return a type [result arules]. The path
       order in combination with the argument filter or without the
       argument filter. *)

      (** In the case RPO + AF: there are three cases:
       that embedded RPO's term to AF's term:
       - RPO's term + AF's project term, in the case of collapsing
       - RPO's term + AF's perm term, in the case of non collapsing
       - RPO's term + AP's project and perm term. *)

      (* FIXME: do I need to add boolean function here? *)

      Definition pathOrder_dp a (R D: arules a) sp (af: option argumentFilter)
      : cpf_util.result (arules a) :=
        match af with
          | Some af => (* Combination with argument filter *)
            match pathOrder_term_rpo_af_dp a sp af with
              | Ok (bsucc_ge, bsucc_gt) =>
                if   forallb (abrule bsucc_ge) D &&
                             forallb (abrule bsucc_ge) R
                then Ok (List.filter (abrule (neg bsucc_gt)) D)
                else Ko _ (Error ENotpathOrder_AF_dp) (* FIXME: ERROR *)
              | Ko e                    => Ko _ e
            end
          | None   => (* Without argument filter *)
            match pathOrder_term_dp a sp with
              | Ok (bsucc_ge, bsucc_gt) =>
                if   forallb (abrule bsucc_ge) D &&
                             forallb (abrule bsucc_ge) R
                then Ok (List.filter (abrule (neg bsucc_gt)) D)
                else Ko _ (Error ENotpathOrder_dp) 
              | Ko e                    => Ko _ e
            end
        end.
      
      (***********************************************************************)
      (** Correctness proof of [pathOrder_dp] *)

      Lemma pathOrder_dp_ok : forall a (R D D': arules a) l o,
                                pathOrder_dp R D l o = Ok D' ->
                                WF (hd_red_mod R D') -> WF (hd_red_mod R D).

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

    End rpo_dp.

    (***********************************************************************)
    (** Ordering constrainst proof with reduction pair interpretation of
   dependency pair transformation. Currently support interpretation
   and path ordering. *)
    
    Definition redPair_dp a (R D:arules a) rp
    : cpf_util.result (arules a) :=
      match rp with
        | RedPair_interpretation t is    => redPair_interpretation_dp R D t is
        | RedPair_pathOrder sp oaf       => pathOrder_dp R D sp oaf
        | RedPair_knuthBendixOrder _ _ _ => Ko _ (Todo TRedPair_knuthBendixOrder)
        | RedPair_scnp _ _ _             => Ko _ (Todo TRedPair_scnp)
      end.
    
    Definition ruleRemoval_dp a (R D: arules a) ocp :=
      match ocp with
        | OrderingConstraintProof_redPair rp              => redPair_dp R D rp
        | OrderingConstraintProof_satisfiableAssumption _ =>
          Ko _ (Todo TOrderingConstraintProof_satisfiableAssumption)
      end.

    (***********************************************************************)
    (** ** Check that [p] is a valid termination proof for [hd_red_mod R
  D]. *)

    Section dp_proof.
      
      (***********************************************************************)
      (** Check that [D = dp R] is a trivial proof by stating the set
     of DPs is empty valid termination proof for [hd_red_mod R D]. *)
      
      Definition pIsEmpty a (D: arules a) :=
        if   is_empty D
        then OK
        else Ko _ (Error ErDPNotEmpty).

      Lemma pIsEmpty_ok : forall a (R D: arules a),
        pIsEmpty D = OK -> WF (hd_red_mod R D).
      
      Proof.
        intros a R D.

        unfold pIsEmpty.

        destruct D; simpl; intro.

        apply WF_hd_red_mod_empty. discr.
      Qed.
      
      (***********************************************************************)
      (** Decomposition of an over DP graph of dependency pair proof for
       [hd_red_mod R D].

       - A decomposition of a list of rules is a list of list of
         rules.

       WARNING: the list of DPs is reversed since in CPF, all forward
        arcs are given while in Rainbow, there must be no forward arcs.
        (reverse component list.)
       *)

      Definition decomp_aux a
        (ci: cpf.dps*boolean*option (list positiveInteger)*option cpf.dpProof) :=
        match ci with
          | (dps, b, f, p) => 
            Match map_rev (color_rule a nat_of_string) dps (* FIXME: map_rev?*)
            With dps'      ===> Ok (dps', b, f, p)
        end.

      Definition decomp a cs := map_rev (decomp_aux a) cs.

      (***********************************************************************)
      (** ** Check that [p] is a valid termination proof for [hd_red_mod
       R D].    

       [dpProof] represents proof trees for DP problems.

       A). [pIsEmpty]: is the most basic technique which demands that the set
       of [D] is empty. (trivial proof by stating that the set of DPs is
       empty).     

       B). [depGraphProc] Dependency graph: split the current set of
       DPs into several smaller subproblems by using some DP-graph
       estimation. Note that all components of the graph have to be
       specified, including singleton nodes which do not form an SCC
       on their own. The list of components has to be given in
       topological order, where the components with no incoming
       edges are listed first.

       [REMARK]: the list of DPs is reversed since in CPF, all forward [arcs]
       are given while in Rainbow, there must be no forward [arc].

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
       given.  (* handled like redPairProc *)

       (* TODO *)
       - [DpProof_argumentFilterProc]: just apply an argument filter and
       continue on the filtered DP problem.
       ref : [arg] to realize permutations for lex. comparisons, one has to
       use an argument filter, which can just permute. Eg. right-to-left
       precendence of f (x,y,z), where the second argument is dropped, is
       done by argument filter [f > (3,1)].
       (* TODO *)       
       just apply an argument filter and continue on the filtered DP problem
       is dpProof_argumentFilterProc similar to trsTerminationProof_dpTrans?
       Match dpProof_argumentFilterProc R D arg With D' ==>
       dpProof m R D' p
       trsTerminationProof_dpTrans R dps b dp
       Match dpProof_argumentFilterProc R D arg With D' ==>
       where D' is the [proj_rules pi] E/R
       dpProof m R D' p *)

      Open Scope nat_scope.
      
      Require Import AFilterPerm AProj cpf_util List.

      Fixpoint dpProof (n: nat) a (R D: arules a) p {struct n} : result unit :=
        match n with
          | 0   => Ko _ (Fail FDpProof_zerobound) (* FIXME: Todo or error ? *)
          | S m =>
            match p with
              | DpProof_pIsEmpty                              =>
                pIsEmpty D
              | DpProof_depGraphProc cs                       =>
                depGraphProc m R D cs
              | DpProof_redPairProc (Some _) _ _ _            =>
                Ko _ (Todo TDpProof_redPairProc)
              | DpProof_redPairProc None ocp dps p            =>
                Match ruleRemoval_dp R D ocp With D'        ===>
                      dpProof m R D' p
              | DpProof_redPairUrProc oc ocp dps usr p =>
                Ko _ (Todo TDpProof_redPairUrProc)
              | DpProof_monoRedPairProc (Some _) _ _ _ _      =>
                Ko _ (Todo TDpProof_monoRedPairProc)
              | DpProof_monoRedPairProc None ocp dps rs p     =>
                Match ruleRemoval_dp R D ocp With D'        ===>
                      dpProof m R D' p
              | DpProof_monoRedPairUrProc oc ocp dps rs usr p =>
                Ko _ (Todo TDpProof_monoRedPairUrProc )
              | DpProof_subtermProc _ _ _ _                   =>
                Ko _ (Todo TDpProof_subtermProc)
              | DpProof_argumentFilterProc args dps rs p      =>
                argumentFilterProc m R D args p
              | DpProof_semlabProc _ _ _ _ _                  =>
                Ko _ (Todo TDpProof_semlabProc)
              | DpProof_unlabProc _ _ _                       =>
                Ko _ (Todo TDpProof_unlabProc)
              | DpProof_sizeChangeProc _ _                    =>
                Ko _ (Todo TDpProof_sizeChangeProc)
              | DpProof_flatContextClosureProc _ _ _ _ _      =>
                Ko _ (Todo TDpProof_flatContextClosureProc)
              | DpProof_uncurryProc _ _ _ _ _                 =>
                Ko _ (Todo TDpProof_flatContextClosureProc)
              | DpProof_finitenessAssumption _                =>
                Ko _ (Todo TDpProof_finitenessAssumption)
              | DpProof_usableRulesProc _ _                   =>
                Ko _ (Todo TDpProof_usableRulesProc)
              | DpProof_innermostLhssRemovalProc _ _          =>
                Ko _ (Todo TDpProof_innermostLhssRemovalProc)
              | DpProof_switchInnermostProc _ _               =>
                Ko _ (Todo TDpProof_switchInnermostProc)
              | DpProof_rewritingProc _ _ _ _ _               =>
                Ko _ (Todo TDpProof_rewritingProc)
              | DpProof_instantiationProc _ _ _               =>
                Ko _ (Todo TDpProof_instantiationProc)
              | DpProof_forwardInstantiationProc _ _ _ _      =>
                Ko _ (Todo TDpProof_forwardInstantiationProc)
              | DpProof_narrowingProc _ _ _ _                 =>
                Ko _ (Todo TDpProof_narrowingProc)
              | DpProof_splitProc _ _ _ _                     =>
                Ko _ (Todo TDpProof_splitProc)
              | DpProof_generalRedPairProc _ _ _ _ _ _ _      =>
                Ko _ (Todo TDpProof_generalRedPairProc)
            end
        end

      (* translate rules to proj_rules in the case of AProj and in the
       case of Filter translate rules to filter_rules *)

      with argumentFilterProc n a (R D: arules a) args p {struct n} :=
             match n with
               | 0   => Ko _ (Fail FDpProof_zerobound) (*FIXME todo or error?*)
               | S m =>
                 match args with
                   | (f, _, t) :: l' => (* Projection *)
                     if is_collapsing t
                     then
                       let pR := color_proj_rules args R in
                       let pD := color_proj_rules args D in
                       dpProof m pR pD p
                     else (* Filter *) (* This function need [bnon_dup] and
                                     [color_build_pi]. *)
                       if is_nonCollapsing t &&
                          bnon_dup (Sig a)(color_raw_pi_filter a args)(list_split_triple args)
                       then
                         let fR := color_filter_rules (color_build_pi_filter args) R in 
                         let fD := color_filter_rules (color_build_pi_filter args) D in
                         dpProof m fR fD p
                       else argumentFilterProc m R D l' p
                   | nil             => Ko _ (Error Edp_argumentfilter)
                 end
             end

      (* Each SCC terminates whether if SCC is truly a SCC then check it
       WF; if SCC is not a SCC then test co_scc = true (means there is
       no edge from i -> j (j > i) *)

      with depGraphProc (n : nat) a (R D : arules a) cs {struct n} :=
             match n with
               | 0   => Ko _ (Fail FDpProof_zerobound) (* FIXME *)
               | S m =>
                 if   forallb (@is_notvar_lhs (Sig a)) R &&
                      forallb (undefined_rhs R) D        &&
                      brules_preserve_vars D
                 then Match decomp a cs With cs' ===>
                            let ls                          := split_list cs'   in
                            if equiv_rules (flat ls) D
                            then let approx               := dpg_unif_N n R D in
                                 if valid_decomp approx ls
                                 then
                                   if forallb (fun ci        =>
                                   let '(dps, b, _, op)    := ci               in
                                     match b, op with
                                       | true, Some pi       =>
                                         bool_of_result (dpProof m R dps pi)
                                       | false, _            =>
                                         co_scc approx dps
                                       | _, _                => false
                                                 end) cs'
                                   then OK
                                   else Ko _ (Fail FDecomp)
                                 (* FIXME: give specified message or it could be a failure *)
                                 else   Ko _ (Todo Todo1)
                            else     Ko _ (Error ENotDepPairs_graph)
                 else       Ko _ (Todo TdepGraphProc)
             end.

      Close Scope nat_scope.

      Lemma unit_ok : forall u, Ok u = OK.
      
      Proof.
        induction u. unfold OK. unfold Zero. refl.
      Qed.

      (***********************************************************************)
      (** Structure proof of DPProof.

      1. DP is empty.

      2. Rule removal of DP.

      3. Path ordering.

      4. Decomposition graph.

      5. Argument filtering.    *)

      Lemma dpProof_ok : forall n a (R D: arules a) dps,
            dpProof n R D dps = OK -> WF (hd_red_mod R D)
      with  argumentFilterProc_ok : forall n a (R D : arules a) a0 dps,
            argumentFilterProc n R D a0 dps = OK -> WF (hd_red_mod R D)           
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
        
        Focus 2.

        destruct o; simpl in *; try discr.

        unfold ruleRemoval_dp.

        destruct o0; simpl in *; try discr.

        unfold redPair_dp.

        destruct r; simpl in *; try discr.

        case_eq (redPair_interpretation_dp R D t l);
          intros l0 H1 H2; try discr.

        apply redPair_interpretation_dp_ok in H1. hyp.

        eapply dpProof_ok. apply H2.
        
        (** 3. Correctness proof of path ordering. *)
        
        case_eq (pathOrder_dp R D l o); intros l0 H1 H2; try discr.
        
        apply pathOrder_dp_ok in H1. hyp.

        eapply dpProof_ok. apply H2.
        
        (** 4. Decomposition graph. *)
        
        destruct n0; try discr; simpl in *.

        case_eq (forallb (is_notvar_lhs (Sig:=Sig a)) R &&
                         forallb (undefined_rhs R) D            &&
                         brules_preserve_vars D); intros H1; try discr.

        case_eq (decomp a l); intros l0 H2; try discr.

        set (l1:= split_list l0). 

        case_eq (equiv_rules (flat l1) D); intros H4; try discr.

        set (approx:= dpg_unif_N (S n0) R D).

        case_eq (valid_decomp approx l1); intros H5; try discr.

        case_eq (forallb (fun ci : arules a * bool * option (list positiveInteger)
                                   * option cpf.dpProof =>
                            match ci with
                              | (dps, true, _, Some pi) => bool_of_result (dpProof n0 R dps pi)
                              | (dps, true, _, None)    => false
                              | (dps, false, _, _)      => co_scc approx dps
                            end) l0); intros H6 H7; try discr. 
        
        eapply WF_decomp_co_scc with (approx:=approx)(cs:=l1).
        
        (** Over graph using a finite number of unification steps. *)
        
        apply dpg_unif_N_correct.
        
        (** [hypR: forallb (@is_notvar_lhs Sig) R = true]. *)
        
        do 2 rewrite andb_eq in H1. intuition.
        
        (** [hypD: forallb (undefined_rhs R) D = true]. *)
        
        do 2 rewrite andb_eq in H1. intuition.
        
        (** [hypD: rules_preserve_vars D]. *)
        
        do 2 rewrite andb_eq in H1. intuition.

        apply brules_preserve_vars_ok. hyp.
        
        (** [hyp4: D [= flat cs]. *)
        
        unfold equiv_rules in H4.

        rewrite equiv_ok in H4. apply H4.

        intros r1 r2. split. intros.

        rewrite ATrs.beq_rule_ok in H. hyp.

        intros. apply ATrs.beq_rule_ok. hyp.
        
        (** [hyp1: flat cs [= D] *)
        
        unfold equiv_rules in H4.

        apply equiv_ok in H4. apply H4.

        intros r1 r2. split. intros.

        rewrite ATrs.beq_rule_ok in H. hyp.

        intros. apply ATrs.beq_rule_ok. hyp.
        
        (** [hyp2 : valid_decomp cs = true] *)
        
        hyp.
        
        (** [hyp3 : lforall (fun ci => co_scc ci = true \/ WF (hd_red_Mod S ci)) cs] *)
        
        clear H2 H4 H5 H7.

        induction l0; simpl in *; try auto.

        split.

        Focus 2.

        apply IHl0.

        rewrite andb_eq in H6.

        destruct H6.

        apply H0. rewrite andb_eq in H6.

        destruct H6.

        destruct a0; try discr; simpl in *.

        do 2 destruct p; try discr. destruct b; try discr.

        destruct o; try discr. right.

        unfold bool_of_result in H.

        case_eq (dpProof n0 R l2 d); intros u Hdp; rewrite Hdp in H; try discr.

        eapply dpProof_ok.

        erewrite <- unit_ok.

        apply Hdp.

        left. apply H.
        
        (** Correctness of depGraphProc. *)
        
        Focus 4.
        
        induction n0; simpl in *; try discr; auto.

        intros a R D cs.

        case_eq (forallb (is_notvar_lhs (Sig:=Sig a)) R &&
                         forallb (undefined_rhs R) D            &&
                         brules_preserve_vars D); intros H0; try discr.

        case_eq (decomp a cs); intros l1 H2; try discr.

        case_eq (equiv_rules (flat (split_list l1)) D); intros H3; try discr.

        case_eq (valid_decomp (dpg_unif_N (S n0) R D) (split_list l1));
          intros H4; try discr.

        case_eq (forallb
                (fun ci : arules a * bool * option (list positiveInteger)
                          * option cpf.dpProof =>
                      match ci with
                        | (dps, true, _, Some pi) => bool_of_result (dpProof n0 R dps pi)
                        | (dps, true, _, None)    => false
                        | (dps, false, _, _)      => co_scc (dpg_unif_N (S n0) R D) dps
                      end) l1); intros H5 H6; try discr.
        clear H6.
        
        eapply WF_decomp_co_scc.
        
        (** Over graph using a finite number of unification steps. *)
        
        apply dpg_unif_N_correct.
        
        (** [hypR: forallb (@is_notvar_lhs Sig) R = true] *)
        
        do 2 rewrite andb_eq in H0. intuition.
        
        (** [hypD: forallb (undefined_rhs R) D = true] *)
        
        do 2 rewrite andb_eq in H0. intuition.
        
        (** [hypD: rules_preserve_vars D] *)
        
        do 2 rewrite andb_eq in H0. intuition.

        apply brules_preserve_vars_ok. hyp.
        
        (** [hyp4: D [= flat cs] *)
        
        unfold equiv_rules in H3.

        rewrite equiv_ok in H3. apply H3.

        intros r1 r2. split. intros.

        rewrite ATrs.beq_rule_ok in H. hyp.

        intros.

        apply ATrs.beq_rule_ok. hyp.
        
        (** [hyp1: flat cs [= D] *)
        
        unfold equiv_rules in H3.

        apply equiv_ok in H3. apply H3.

        intros r1 r2.

        split.
        
        intros.

        rewrite ATrs.beq_rule_ok in H. hyp.

        intros. apply ATrs.beq_rule_ok. hyp.
        
        (** [hyp2 : valid_decomp cs = true] *)
        
        try apply H4.
        
        (** [hyp3 : lforall (fun ci => co_scc ci = true 
       \/ WF (hd_red_Mod S ci)) cs] *)
        
        clear H2 H3 H4.

        induction l1; simpl in *; try auto.

        split.

        Focus 2.

        apply IHl1.

        rewrite andb_eq in H5.

        destruct H5. apply H1.

        rewrite andb_eq in H5.

        destruct H5.

        destruct a0; try discr.

        do 2 destruct p; try discr.

        destruct b; try discr.

        destruct o; try discr.

        right.

        unfold bool_of_result in H.

        case_eq (dpProof n0 R l d); intros u Hdp;
        rewrite Hdp in H; try discr.

        eapply dpProof_ok.

        erewrite <- unit_ok.

        apply Hdp.

        left.

        apply H.
        
        (** monoRedPairProc *)
        
        destruct o; simpl in *; try discr.

        unfold ruleRemoval_dp.

        destruct o0; simpl in *; try discr.

        unfold redPair_dp.

        destruct r; simpl in *; try discr.
        
        (** Reduction pair interpretation in DP. *)
        
        case_eq (redPair_interpretation_dp R D t0 l);
          intros l0 H1 H2; try discr.

        apply redPair_interpretation_dp_ok in H1. hyp.

        eapply dpProof_ok. apply H2.
        
        (** Path ordering in DP. *)

        case_eq (pathOrder_dp R D l o); intros l0 H1 H2; try discr.

        apply pathOrder_dp_ok in H1. hyp.

        eapply dpProof_ok. apply H2. 
        
        (** 5. Argument filtering in dependency pair. *)
        
        destruct n0; try discr; simpl in *.

        destruct a0; try discr.

        destruct p; try discr.

        destruct p; try discr.
        
        (** In the case it is a collapsing. *)
        
        case_eq (is_collapsing t0); intros H H0; try discr.

        eapply WF_hd_red_mod_proj.

        apply dpProof_ok in H0.

        unfold color_proj_rules, color_build_pi in H0.

        apply H0.
        
        (** In the case it is not a collapsing. *)

        revert H0.

        case_eq (is_nonCollapsing t0 && bnon_dup (Sig a)
                                  (color_raw_pi_filter a ((s, a1, t0) :: a0))
                                  (list_split_triple ((s, a1, t0) :: a0)));
          intros H1 H0; try discr.

        rewrite andb_eq in H1. destruct H1.

        apply dpProof_ok in H0.

        unfold color_filter_rules, color_filter_rule, color_build_pi in H0.

        eapply WF_hd_red_mod_filter.

        rewrite bnon_dup_ok in H2.

        apply H2. apply H0.

        eapply argumentFilterProc_ok. apply H0.
        
        (* Correctness proof of AF. *)
        
        induction n0; simpl in *; try discr.

        intros a R D af dps.

        destruct af; try discr.

        destruct p; try discr.

        destruct p; try discr.
        
        (* Collapsing is true *)
        
        case_eq (is_collapsing t); intros H H0; try discr.

        eapply WF_hd_red_mod_proj.

        apply dpProof_ok in H0.

        unfold color_proj_rules, color_build_pi in H0. 

        apply H0.
        
        (* Non-collapsing is true. *)
        
        revert H0.

        case_eq (is_nonCollapsing t && bnon_dup (Sig a)
                                  (color_raw_pi_filter a ((s, a0, t) :: af))
                                  (list_split_triple ((s, a0, t) :: af)));
          intros H1 H0; try discr.

        rewrite andb_eq in H1. destruct H1.

        apply dpProof_ok in H0.

        unfold color_filter_rules, color_filter_rule, color_build_pi in H0.

        eapply WF_hd_red_mod_filter.

        rewrite bnon_dup_ok in H2. 

        apply H2. apply H0.

        eapply argumentFilterProc_ok. apply H0.
      Qed. (* REMARK: it takes long time at QED. *)
      
      (***********************************************************************)
      (** ** Dependency pair transformation:

       - Without mark symbols: rewriting with the rules is not allowed
         at the root.

       - With mark symbols: the whole dp-proof is using the notion of
       chain where rewriting with the rules is applied at arbitrary
       positions (including the root). *)
      
      (* TODO: string reverse on [unmark] and [mark] dpTrans.*)

      (** Dependency pair transformation without marked symbols. There
    are nothing but check that the rules given is indeed a dependency
    pair defined in Color. If yes then call to the DP proof with those
    rules. Otherwise, return an error message. *)

      Definition dpTrans_unmark a (R:arules a) (dps: rules) (p: cpf.dpProof):
        result unit :=
        Match color_rules a nat_of_string dps With D ===>
              if   equiv_rules D (dp R)
              then dpProof n R D p
              else Ko _ (Error EDPTransUnmark).

      (** Correctness proof of DP transformation without marked
    symbol. If the definition above is accepted then conclude that it
    is terminating. *)
      
      Lemma dpTrans_unmark_ok : forall a rs dps p
        (Hm: dpTrans_unmark rs dps p = OK)
        (H : forallb (is_notvar_lhs (Sig:=Sig a)) rs &&
             brules_preserve_vars rs = true), WF (red rs).

      Proof.
        intros a rs dps p Hm H.

        unfold dpTrans_unmark in Hm.

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

        intro.

        apply ATrs.beq_rule_ok; hyp.
      Qed.

      (***********************************************************************)
      (* Dependency pair with marked symbols, where the arity are
    changed. By using the signature morphism defined in the Color
    library, checking that if the rules after mapping is equivalence
    then apply these rules to the DP proof. *)

      Definition dpTrans_mark a (R:arules a) (dps: rules) (p:cpf.dpProof):
        result unit :=
        Match color_rules (dp_arity a) nat_of_string dps With D' ===>
              let rs  := Fl (HFSig_of_dup_Sig_eq (arity := a)) (dup_int_rules R)     in
              let rs' := Fl (HFSig_of_dup_Sig_eq (arity := a)) (dup_hd_rules (dp R)) in
              if         equiv_rules D' rs'
              then       dpProof n rs D' p
              else       Ko _ (Error EDPTransMark).

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
        
        do 3 rewrite andb_eq in H. do 3 destruct H.
        hyp.
        
        (* No variable on the right hand side of [dp R]. *)
        
        do 3 rewrite andb_eq in H. do 3 destruct H.
        hyp.

        (* rs [=] dp rs. *)
        
        unfold equiv_rules in H1.

        intuition.

        apply equiv_ok in H1.

        apply Fhd_red_mod_WF_fin with (HF:= HFSig_of_dup_Sig_eq (arity:=a)).
        
        apply dpProof_ok in Hm.

        rewrite <- H1. apply Hm.

        (* beq_rule *)
        
        intros r1 r2.

        split.

        intros. apply ATrs.beq_rule_ok in H2. apply H2.

        intros. rewrite ATrs.beq_rule_ok. apply H2.
      Qed.

      (***********************************************************************)
      (* TODO : string reverse *)
      (*
    Definition str_dpTrans_unmark a (R:arules a) (dps: rules) (p: cpf.dpProof)
      : result unit :=
      Match color_rules (ar (SSig_of_ASig (Sig a))) nat_of_string dps
      With D ===> if equiv_rules D (dp (reverse_trs R)) then
      str_dpProof n (reverse_trs R) (reverse_trs D) p else Ko _
      EDPTransUnmark.

    Definition str_dpTrans_mark a (R:arules a) (dps: rules) (p:cpf.dpProof):
      result unit :=
      Match color_rules (dp_arity (ar (SSig_of_ASig (Sig a))))
      nat_of_string dps With D' ===>
      let rs := Fl (HFSig_of_dup_Sig_eq (arity := ar (SSig_of_ASig (Sig a))))
        (dup_int_rules (reverse_trs R)) in
        let rs' := Fl (HFSig_of_dup_Sig_eq (arity := ar (SSig_of_ASig (Sig a))))
          (dup_hd_rules (dp (reverse_trs R))) in
          if equiv_rules D' rs' then
            str_dpProof n rs D' p else  Ko _ Todo. (* TEST *)

    Definition str_trsTerminationProof_dpTrans a (R:arules a) (dps:
    rules) (b:bool) (p: cpf.dpProof): result unit :=
      if forallb (@is_notvar_lhs (Sig a)) R && brules_preserve_vars R then
        if b then str_dpTrans_mark R dps p
          else str_dpTrans_unmark R dps p
        else Ko _ EDPTrans.*)
      

      (***********************************************************************)
      (** Termination proof with dependency pair transformation with
       mark and unmark symbols where the left hand side rules has no
       variable and the variables are preserve. *)

      Definition dpTrans a (R:arules a) (dps: rules) (b:bool)(p: cpf.dpProof):
        result unit :=
        if forallb (@is_notvar_lhs (Sig a)) R      &&  
                   forallb (@is_notvar_lhs (Sig a)) (dp R) && 
                   forallb (@is_notvar_rhs (Sig a)) (dp R) &&
                   brules_preserve_vars R
        then
          if   b
          then dpTrans_mark R dps p
          else dpTrans_unmark R dps p
        else   Ko _ (Error EDPTrans).

      Lemma dpTrans_ok : forall a (R: arules a) dps b p,
        dpTrans R dps b p = OK ->  WF (red R).

      Proof.

        intros a rs dps b p Hm.

        unfold dpTrans in Hm.

        case_eq (forallb (is_notvar_lhs (Sig:=Sig a)) rs      &&
                         forallb (is_notvar_lhs (Sig:=Sig a)) (dp rs) &&
                         forallb (is_notvar_rhs (Sig:=Sig a)) (dp rs) &&
                         brules_preserve_vars rs); intro H;
        rewrite H in Hm; try discr.

        destruct b; try discr.

        (* Proving dependency pair where symbols are marked. *)
        
        apply dpTrans_mark_ok with (dps:=dps)(p:=p).

        apply Hm. apply H.

        (* Proving dependency pair where symbols are not marked. *)
        
        apply dpTrans_unmark_ok with (dps:=dps)(p:=p).

        apply Hm.

        do 3 rewrite andb_eq in H.

        rewrite andb_eq. intuition.
      Qed.

    End dp_proof.

  End Top_Termination.

  (***********************************************************************)
  (* Main check function *)
  (***********************************************************************)

  Section Termination.

    (***********************************************************************)
    (** Check that [R] is a trivial proof by stating the set of rules
    [R] is empty valid termination proof for [red R]. *)
    
    Definition rIsEmpty a (R: arules a) :=
      if   is_empty R
      then OK
      else Ko _ (Error ErNotEmpty).
    
    Lemma rIsEmpty_ok : forall a (R: arules a),
      rIsEmpty R = OK -> WF (red R).
    
    Proof.
      intros a R. unfold rIsEmpty.

      destruct R; simpl; intro.

      apply WF_red_empty. discr.

    Qed.
    
    (***********************************************************************)
    (** Check that [R] is a trivial proof by stating the set of rules
       [R] is empty valid termination proof for [red R]. *)
    
    Definition relTerminationProof_rIsEmpty a (D : arules a) :=
      if   is_empty D
      then OK
      else Ko _ (Error ErNotEmptyrIsEmpty).
    
    Lemma relTerminationProof_rIsEmpty_ok : forall a (R D: arules a),
      relTerminationProof_rIsEmpty D = OK -> WF (red_mod R D).
    
    Proof.
      intros a R D. unfold relTerminationProof_rIsEmpty.

      destruct D; simpl; intro.

      apply WF_red_mod_empty. discr.
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

    (*Variable nat_of_string : string -> nat.*)

    (** [n: nat] is an artificial extra argument which purpose is to
     make the function [dpProof] structually recursive with respect to
     this argument. *)

    (* TODO *)

    (* Define a function for ruleRemoval *)

    Require Import AReverse AUnary cpf_util ATerm_of_String
            String_of_ATerm.

    Fixpoint trsTerminationProof a (R: arules a) p :=
      match p with
        | TrsTerminationProof_rIsEmpty                   =>   rIsEmpty R
        | TrsTerminationProof_ruleRemoval (Some _) _ _ _ =>
          Ko _ (Todo TTrsTerminationProof_ruleRemoval)
        | TrsTerminationProof_ruleRemoval None ocp rs p  =>
          Match ruleRemoval R ocp With R'                ===>
                trsTerminationProof R' p
        | TrsTerminationProof_dpTrans dps b dp           =>  
          dpTrans R dps b dp
        (* TODO : string reverse *)
        (*if brules_preserve_vars R &&
          @bis_unary (Sig a) (symbol_in_rules dps) then
            let sR := reverse_trs R in
              str_trsTerminationProof_dpTrans rpo_n nat_of_string n sR dps b dp
          else
        trsTerminationProof_dpTrans rpo_n nat_of_string n R dps b dp*)
        | TrsTerminationProof_semlab _ _ _ _               =>
          Ko _ (Todo TTrsTerminationProof_semlab)
        | TrsTerminationProof_unlab rs p                   =>
          Ko _ (Todo TTrsTerminationProof_unlab)
        | TrsTerminationProof_stringReversal rs p          => (* FIXME *)
          if   brules_preserve_vars R &&
              @bis_unary (Sig a) (symbol_in_rules rs)
          then trsTerminationProof (reverse_trs R) p
          else Ko _ (Todo TTrsTerminationProof_stringReversal)
        | TrsTerminationProof_flatContextClosure _ _ _     =>
          Ko _ (Todo TTrsTerminationProof_flatContextClosure)
        | TrsTerminationProof_terminationAssumption _      =>
          Ko _ (Todo TTrsTerminationProof_terminationAssumption)
        | TrsTerminationProof_uncurry _ _ _                =>
          Ko _ (Todo TTrsTerminationProof_uncurry)
        | TrsTerminationProof_bounds _ _ _ _               =>
          Ko _ (Todo TTrsTerminationProof_bounds)
        | TrsTerminationProof_switchInnermost _ _          =>
          Ko _ (Todo TTrsTerminationProof_switchInnermost)
        | TrsTerminationProof_split _ _ _                  =>
          Ko _ (Todo TTrsTerminationProof_split)
        | TrsTerminationProof_removeNonApplicableRules _ _ =>
          Ko _ (Todo TTrsTerminationProof_removeNonApplicableRules)
      end.

    (***********************************************************************)
    (* Correctness proof of string reverse *)

    (* TODO *)
    (*
    Lemma string_reverse_ok :
      forall a t (rs: arules a) trs
             (Hm : trsTerminationProof  (reverse_trs rs) t = OK)
             (H : brules_preserve_vars rs = true)
             (H0 : bis_unary (Sig a) (symbol_in_rules trs) = true),
        WF (red rs).

    Proof.
      intros a t rs trs Hm H H0.
      apply WF_red_rev_eq.
      
      (* is_unary *)
      
      rewrite <- bis_unary_ok. apply H0.

      (* Proof : f in a list of trs *)

      Focus 2.

      (** Proof that rule_preserve_vars in rs. *)

      rewrite <- brules_preserve_vars_ok. apply H.

      Focus 2.
      
      (** Proof that rule_preserve_vars in R. *)
      
      apply trsTerminationProof_ok in Hm. p.
      rewrite <- brules_preserve_vars_ok. apply H.
      
      Focus 2.
      
    (* TODO *)
    (* Proof [red_mod (reverse_trs R) (reverse_trs D)] is well-founded *)
      
    Admitted.*)
    
    (***********************************************************************)
    (** Structure proof of TRS termination proof

       1. TRS is empty.

       2. Rule removal

       3. Path ordering.

       4. Dependence pair transformation.

       5. String reverse. *)

    Lemma trsTerminationProof_ok : forall a R t i,
       sys_of_input a nat_of_string i = Ok (Red R) ->
       trsTerminationProof R t        = OK         -> WF (red R).
    
    Proof.
      intros a r t i H Hs.

      revert r H Hs. intros rs Hs.

      clear Hs i.

      revert t rs.

      induction t; intros rs Hm; simpl in Hm; try discr.
      
      (** 1. Correctness proof when termination proof is empty. *)
      
      apply rIsEmpty_ok. hyp.

      (** 2. Correctness proof of termination proof in the case of
          rule removal. *)
      
      destruct o; try discr.

      unfold ruleRemoval in Hm.

      destruct o0; try discr.

      unfold redPair in Hm.

      destruct r; try discr.

      revert Hm.

      case_eq (redPair_interpretation rs t1 l); intros l0 H Hm; try discr.

      eapply redPair_interpretation_ok.

      apply H. eapply IHt. hyp.

      (** 3. Correctness proof of termination proof in the case of
          path ordering. *)

      revert Hm. case_eq (pathOrder rs l o); intros l0 H Hm; try discr.

      eapply pathOrdering_ok.

      apply H. eapply IHt. hyp.
      
      (** 4. Correctness proof of dependency pair transformation
          method with and without mark symbol. *)
      
      eapply dpTrans_ok. apply Hm.

      (** 5. String reversal *)

      case_eq (brules_preserve_vars rs &&
                                    bis_unary (Sig a) (symbol_in_rules t));
        intros H1; rewrite H1 in Hm; simpl in *; try discr.  
      
      rewrite andb_eq in H1. destruct H1.

      apply WF_red_rev_eq.

      (* is_unary *)

      rewrite <- bis_unary_ok. apply H0.

      (* f in the list of t *)

      Focus 2.

      rewrite <- brules_preserve_vars_ok. apply H.

      Focus 2. 

    (* TODO *)
    Admitted.

    (***********************************************************************)
    (** ** Check that [p] is a valid non-termination proof for [red R].
     
     - [variableConditionViolated]: There is a rule where the lhs is a
     variable, or the rhs contains variables not occuring in the lhs.
     
     - [loop]: a loop is given by a (non-empty) rewrite-sequence t0 ->+
     tn where additional tn = C[t0 sigma]. *)

    (** ** Check that [R] is a violation of variable condition, it
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
    (* Non termination proof: LOOP. *)

    Require Import ALoop.

    (* FIXME *)

    Definition loop a (R: arules a) (lo: cpf.loop) : result unit :=
      let '((t, ls), _, c) := lo in
      Match color_term a nat_of_string t          With t  ===>
            Match color_rewriteSteps nat_of_string a ls With ds ===>
            let  pos := color_position_of_context c in
            if   is_loop R t ds pos
            then OK
            else Ko _ (Error ErtrsNonTerminationProof_loop).
    
    (***********************************************************************)

    Lemma loop_ok: forall a (R: arules a) l, loop R l = OK -> EIS (red R).

    Proof.

      intros a R l Hm.

      unfold loop in Hm.

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

    Definition trsNonTerminationProof a (R: arules a) p : result unit :=
      match p with
        | TrsNonterminationProof_variableConditionViolated  => variableConditionViolated R
        | TrsNonterminationProof_ruleRemoval _ _            =>
          Ko _ (Todo TTrsNonterminationProof_ruleRemoval)
        | TrsNonterminationProof_stringReversal _ _         =>
          Ko _ (Todo TTrsNonterminationProof_stringReversal)
        | TrsNonterminationProof_loop (((_, nil), _), _)    => (* including nil inside *)
          Ko _ (Todo TTrsNonterminationProof_loop_nil)
        | TrsNonterminationProof_loop lo                    => (* FIXME *) loop R lo
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
    
    Lemma trsNonTerminationProof_ok: forall a (R: arules a) l,
      trsNonTerminationProof R l = OK -> EIS (red R).
    
    Proof.
      intros a R l Hm.

      unfold trsNonTerminationProof in Hm.

      destruct l; simpl; try discr.

      (* Variable *)

      apply variableConditionViolated_ok.

      apply Hm.

      destruct l; simpl; try discr.

      destruct p; simpl; try discr.

      destruct r; simpl; try discr.

      destruct l; simpl; try discr.

      (* Loop *)

      eapply loop_ok. apply Hm.
    Qed.

    (***********************************************************************)
    (** Check that [p] is a valid termination proof for [red_mod R D].
     - [rIsEmpty] [sIsEmpty]: state that the relative termination is
       terminating since it has no rules.
     - [ruleRemoval]: use a reduction pair where both the weak and the
     strict ordering are monotone. Delete all strictly decreasing
     rules. The remaining rules have to be given. If the ordering
     constraint proof is only an assumption, the
     orderingConstraints-element becomes mandatory.
     - [stringReversal]: reverse the strings in both R and S, i.e., replace
      f(g(h(x))) -&gt; f(x) by h(g(f(x))) -&gt; f(x).  Note that the
      variable in a reversed rule should be same as the variable in the
      original rule.*)

    Fixpoint relTerminationProof a (R D: arules a) p : result unit :=
      match p with
        | RelativeTerminationProof_rIsEmpty
        | RelativeTerminationProof_sIsEmpty _                       =>
          relTerminationProof_rIsEmpty D
        | RelativeTerminationProof_ruleRemoval (Some _) _ _ _ _     =>
          Ko _  (Todo TTrsTerminationProof_ruleRemoval)
        | RelativeTerminationProof_ruleRemoval None ocp rs trs p =>
          Match rel_trsTerminationProof_ruleRemoval R D ocp With D' ===>
                relTerminationProof R D' p
        | RelativeTerminationProof_semlab _ _ _ _                   =>
          Ko _ (Todo TTrsTerminationProof_semlab)
        | RelativeTerminationProof_unlab _ _ _                      =>
          Ko _ (Todo TTrsTerminationProof_unlab)
        | RelativeTerminationProof_stringReversal rs rs2 dp         =>
          if   brules_preserve_vars R &&
               brules_preserve_vars D &&
              @bis_unary (Sig a) (symbol_in_rules rs)
          then relTerminationProof (reverse_trs R) (reverse_trs D) dp
          else Ko _ (Todo TTrsTerminationProof_stringReversal)
        | RelativeTerminationProof_relativeTerminationAssumption _ =>
          Ko _ (Todo TTrsTerminationProof_terminationAssumption)
        | _                                                        => Ko _ (Todo Todo1)
      end.

    (***********************************************************************)
    (** Structure proof of relation TRS:
       1. relation TRS is empty.
       2. Rule removal.  *)

    Lemma rel_TerminationProof_ok : forall a R D t i,
       sys_of_input a nat_of_string i = Ok (Red_mod R D) ->
       relTerminationProof R D t      = OK               -> WF (red_mod R D).
    
    Proof.
      intros a R D t i H Hs.

      revert R D H Hs. intros R D Hs.

      clear Hs i.

      revert t R D.

      induction t; intros R D Hm; simpl in Hm; try discr.

      (** Correctness proof when termination proof is empty. *)
      
      apply relTerminationProof_rIsEmpty_ok. apply Hm.

      apply relTerminationProof_rIsEmpty_ok. apply Hm.
      
      (** Correctness proof of relative termination proof in the case of
       rule removal. *)

      destruct o; try discr.

      unfold rel_trsTerminationProof_ruleRemoval in Hm.

      destruct o0; try discr.

      unfold rel_orderingConstraintProof_redPair in Hm.

      destruct r; try discr.

      revert Hm.

      case_eq (rel_redPair_interpretation R D t2 l); intros l0 H Hm; try discr.

      eapply rel_redPair_interpretation_ok. apply H.

      apply IHt. apply Hm.
      
    (* TODO 
      (** Correctness proof of string reverse. *)
      
      case_eq (brules_preserve_vars R && brules_preserve_vars D &&
      bis_unary (Sig a) (symbol_in_rules t)); intros H; rewrite H in
      Hm; try discr.  do 2 rewrite andb_eq in H. do 2 destruct H.
      
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
     *)

    Admitted.

    (***********************************************************************)
    (* TODO: relative non termination Loop *)

    (***********************************************************************)
    (** ** Check that [R] is a violation of variable condition for
    [red_mod R D] *)

    Definition relativeNonTerminationProof_variableConditionViolated a (R D: arules a) :=
      if   brules_preserve_vars D
      then Ko _ (Error ErNotVariableConditionViolated)
      else OK.

    Lemma relativeNonTerminationProof_variableConditionViolated_ok: forall a (R D: arules a),
      relativeNonTerminationProof_variableConditionViolated R D = OK -> EIS (red_mod R D).
    
    Proof.
      intros a R D Hm.

      unfold relativeNonTerminationProof_variableConditionViolated in Hm.

      case_eq (brules_preserve_vars D); intros H; rewrite H in Hm; try discr.
      
      apply var_cond_mod.

      rewrite <- brules_preserve_vars_ok.

      rewrite <- false_not_true.

      apply H.
    Qed.
        
    (***********************************************************************)
     (** ** Check that [p] is a valid non-termination proof for [red_mod
       R D]. Checking that there is a loop in a TRS. *)
   
   Require Import AModLoop.

    Definition relativeNonTerminationProof_loop a (R D: arules a) (lo:
    cpf.loop) : result unit :=
      let '((t, ls), _, c) := lo in
        Match color_term a nat_of_string t With t ===>
        (* FIXME: (ls: nil) == list (list rewriteSequence) *)
        Match color_list_mod_data nat_of_string a (ls::nil) With mds ===>
        Match color_rewriteSteps nat_of_string  a  ls       With ds ===>
        let pos := color_position_of_context c in
          if   is_mod_loop R D t mds ds pos
          then OK
          else Ko _ (Error ErrelativeNonTerminationProof_loop).

    Lemma relativeNonTerminationProof_loop_ok: forall a (R D : arules a) l,
       relativeNonTerminationProof_loop R D l = OK -> EIS (red_mod R D).

    Proof.
      intros a R D l Hm.
      unfold relativeNonTerminationProof_loop in Hm.
      destruct l; simpl; try discr.
      destruct p; simpl; try discr.
      destruct r; simpl; try discr.
      case_eq (color_term a nat_of_string t);
        intros t1 H1; rewrite H1 in Hm; try discr.
      case_eq (color_rewriteSteps nat_of_string a l);
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

    (***********************************************************************)
    (** ** Check that [p] is a valid termination proof for [red_mod R D] 

       [variableConditionViolated]: There is a rule where the lhs is a
       variable, or the rhs contains variables not occuring in the lhs.
       
       [loop]: a loop is given by a (non-empty) rewrite-sequence t0 ->+
       tn where additional tn = C[t0 sigma]. *)
    
    Definition relativeNonterminationProof a (R D: arules a)
               (p: relativeNonterminationProof) : result unit :=
      match p with
        | RelativeNonterminationProof_loop lo                   =>
            relativeNonTerminationProof_loop R D lo
        | RelativeNonterminationProof_trsNonterminationProof _  =>
            Ko _ (Todo TRelativeNonterminationProof_trsNonterminationProof)
        | RelativeNonterminationProof_variableConditionViolated =>
            relativeNonTerminationProof_variableConditionViolated R D
        | RelativeNonterminationProof_ruleRemoval _ _ _          =>
            Ko _ (Todo TRelativeNonterminationProof_ruleRemoval)
        | RelativeNonterminationProof_nonterminationAssumption _ =>
            Ko _ (Todo TRelativeNonterminationProof_nonterminationAssumption)
      end.

    (***********************************************************************)
    (** ** Check that [p] is a valid termination proof for:
      - Termination proof: [red R]
      - Dependency pair proof: [hd_red_mod R D]. 
      Also check that [p] is a valid non-termination proof for:
      - Non-termination proof: [red R]
      - Relative non-termination proof: [red_mod R D]. *)

      Definition proof a (s:system a) p :=
      match s, p with
        | Red R, Proof_trsTerminationProof p               => trsTerminationProof R p
        | Red R, Proof_trsNonterminationProof p            => trsNonTerminationProof R p
        | Red_mod E R, Proof_relativeTerminationProof p    => relTerminationProof E R p 
        (* FIXME *)
        | Red_mod E R, Proof_relativeNonterminationProof p => relativeNonterminationProof E R p 
        (* TODO *)
        | Hd_red_mod E R, Proof_dpProof p                  => dpProof n E R p
        | Hd_red_mod E R, Proof_dpNonterminationProof _    =>
          (* TODO: dp_counter example loop? *)
            Ko _ (Todo TProof_dpNonterminationProof)
        | _, Proof_orderingConstraintProof _               =>
            Ko _ (Todo TProof_orderingConstraintProof)
        | _, _                                             =>
            Ko _ (Error EinputProofIncompatible)
      end.

      Definition check a (c: certificationProblem) :=
      match c with
        | (_, _, p, _) =>   Match sys_of_pb a nat_of_string c With s
                       ===> proof s p
      end.
    
    (* how to express the correctness of main ? *)  
    
    Definition not_if (b : bool) P := if b then ~P else P.
    
    (** Define a function for non-termination proof and termination
     proof. At [trsNonterminationProof] change to [false] to be able
     to proof the case of non-termination proof. *)
    
    Definition is_nt_proof p :=
      match p with
        | Proof_trsTerminationProof _         => true
        | Proof_trsNonterminationProof _      => false
        | Proof_relativeTerminationProof _    => true (* CHECK *)
        | Proof_relativeNonterminationProof _ => false (* CHECK *)
        | Proof_dpProof _                     => true
        | Proof_dpNonterminationProof _       => true (* TODO? *)
        | Proof_orderingConstraintProof _     => true
        | Proof_wcrProof _                    => false
        | Proof_crProof _                     => false
        | Proof_crDisproof _                  => false
        | Proof_completionProof _             => false
        | Proof_equationalProof _             => false
        | Proof_equationalDisproof _          => false
        | Proof_complexityProof _             => false
        | Proof_quasiReductiveProof _         => false
      end.
    
    (** Define a function for non-termination proof and termination
     proof. If it is [true] then it is a termination proof else
     it is a non-termination proof. *)
    
    Definition is_nontermin_proof (c: certificationProblem) :=
      match c with
        | (_, _, p, _) => is_nt_proof p
      end.

    (***********************************************************************)
    (** Structure proof of main 

        1. Proof of [red R].

        2. Proof of non termination [red R].

        3. Proof of [red_mod R D].

        4. Proof of non termination [red_mod R D].

        5. Proof of [hd_red_mod R D]. *)

    Lemma main_ok : forall c,
      let a := arity_in_pb c in
      forall s, sys_of_pb a nat_of_string c = Ok s ->
                check a c                   = OK   ->
                not_if (is_nontermin_proof c) (EIS (rel_of_sys s)).

    Proof.
      intros cp a s Hs Hm.

      unfold check in Hm. rewrite Hs in Hm.

      destruct cp as [[[i st] p] o].

      simpl arity_in_pb in *. simpl sys_of_pb in *. simpl is_nontermin_proof.

      unfold proof in Hm.

      destruct s; destruct p; try discr; simpl.

      apply WF_notEIS.

      (** 1. Correctness proof of termination problem for [red R]. *)
      
      apply trsTerminationProof_ok with (t:=t)(i:=i).

      hyp. hyp.
      
      (** 2. Correctness proof of non-termination problem for [red R]. *)
      
      apply trsNonTerminationProof_ok with (l:=t). hyp.
           
      (** 3. Correctness proof of termination problem for [red_mod R
      D]. *)

      apply WF_notEIS.

      apply rel_TerminationProof_ok with (t:=r)(i:=i).

      hyp. apply Hm.

      (** 4. Correctness proof of non-termination problem for [red_mod
      R D]. *)

      unfold relativeNonterminationProof in Hm.

      destruct r; simpl; try discr.

      (** Correctness proof of non-termination proof for [red_mod R D]
       in the case of loop. *)

      apply relativeNonTerminationProof_loop_ok in Hm. apply Hm.

      (** Correctness proof of non-termination proof for [red_mod R D] in
       the case of variable condition violated. *)
      
      apply relativeNonTerminationProof_variableConditionViolated_ok.

      apply Hm.
     
      (** 5. Correctness proof of termination for top termination
       problems (dpProof). [hd_red_mod R (dp R)] *)
     
      apply WF_notEIS. eapply dpProof_ok. apply Hm.
     
      (* TODO : other cases *)
    Qed.
    
End Termination.

End Top.