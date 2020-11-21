(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2011-04-06

* CPF correctness checker

*)

Set Implicit Arguments.

Require Import ATrs SN ZArith EqUtil String List ListDec ListForall
  ListUtil ZUtil LogicUtil BoolUtil VecUtil Polynom NArith APolyInt
  MonotonePolynom PositivePolynom RelUtil RelMidex AMannaNess
  ARedPair2 ARelation NatUtil ADP ADuplicateSymb AMorphism ADecomp
  ADPUnif ACalls cpf2color poly cpf color_matrix_nat SemiRing2
  ATropicalInt2 AArcticBZInt2 OrdSemiRing2 Matrix2 AMatrixInt2
  AMatrixBasedInt2_Nat cpf2color_interpret NewPositivePolynom2
  OrdRingType2 NewAPolyInt2 ListExtras poly_rat NewPolynom2 cpf_util
  RelUtil AVarCond QArith_base.

(***********************************************************************)
(** ** Termination by using dependency proof compatible reduction
   orderings. *)

(* WARNING: the list of DPs is reversed since in CPF, all forward arcs
are given while in Rainbow, there must be no forward arcs. *)

Section Top_Termination.
  
  (** Polynomial interpretation using depedency proof in different
  domains. *)

  Section poly_dp.
  
    (** Domain natural numbers:
       
       Condition for check the termination by rule elimination
       with reduction pairs [ARedPair.v] Lemma [WF_wp_hd_red_mod]:
       
       Manna-Ness theorem in the case of dependency pair transformation:
       
       - Given an artity [a], list of rules [R] and the list of dependent rules
       [D = dp(R)] depends on arity a.
       
       - A reduction pair (bsucc_ge, bsucc_gt), if [R] is included in
     [bsucc_ge] and [D] is included in [bsucc_ge] then all rules [D]
     included in [bsucc_gt] can be removed.
     
     - Define a new [type_poly_naturals_dp] where allows [0] as
     coefficient. *)
   
    Definition polynomial_naturals_dp a
      (is: list (symbol * cpf.arity * function)):=
      Match map_rev (color_interpret_poly a) is With l ===>
      if forallb (fun x =>
        match x with
          existT f p => bcoef_pos p end) l then
      let pi := fun f : Sig a => fun_of_pairs_list a f l in
        Ok ((fun t u => bcoef_pos (rulePoly_ge pi (mkRule t u))),
          (fun t u => bcoef_pos (rulePoly_gt pi (mkRule t u))))
        else Ko _ ENotMonotone_dp.
    
    (** Domain rational numbers:
     
       When using the dependency pairs method, we can prove
       termination by showing that the lhs and rhs of each rule of the
       TRS are comparable by using [>=] whereas the components of each
       dependency pair are comparable by using [>]. Note that
       monotonicity is not required for [>].
       
       Given a polynomial interpreattion and [delta > 0], we have [>=
       . >_delta \subseteq >_delta] (if there is [u] such that: [[t] -
       [u] >= 0] and [[u] - [s] >= delta], then [[t] - [u] -[s] = [t]
       -[s] >= 0 + delta = delta].
       
       Thus [(>=, >_delta)] is a reduction pair. *)
    
    Definition polynomial_rationals_dp a
      (is: list (symbol * cpf.arity * function)) (del: Q) :=
      Match map_rev (color_interpret_polyQ a) is With l ===>
      if forallb (fun x =>
        match x with
          existT f p => bcoef_not_neg p end) l then
      let pi := fun f : Sig a => fun_of_pairs_list_q a f l in
        Ok ((fun t u => bcoef_not_neg (rulePoly_geQ pi (mkRule t u))),
          (fun t u => bcoef_not_neg (rulePoly_gtQ pi del (mkRule t u))))
        else Ko _ ENotMonotone_rat_dp.

    Definition type_poly_rationals_dp a del is :=
      match del with
        | Number_integer i =>
          polynomial_rationals_dp a is (inject_Z i)
        | Number_rational i pos =>
          let q := Qmake i pos in
            polynomial_rationals_dp a is q
      end.

    Definition type_polynomial_dp a is dom :=
      match dom with
        | Domain_naturals => polynomial_naturals_dp a is
        | Domain_integers => Ko _ Ttype_polynomialDomain_integers
        | Domain_rationals del => type_poly_rationals_dp a del is
        | Domain_arctic dom' => Ko _ Ttype_polynomialDomain_arctic
        | Domain_tropical dom' =>
          Ko _ Ttype_polynomialDomain_tropical (* TODO *)
        | Domain_matrices dim sdim dom' =>
          Ko _ Ttype_polynomialDomain_matrices
      end.
   
    Definition polynomial_interpretation_dp a (R D: arules a) is dom :=
      match type_polynomial_dp a is dom with
        | Ok (bsucc_ge, bsucc_gt) =>
          if forallb (ATrs.brule bsucc_ge) D 
            && forallb (ATrs.brule bsucc_ge) R then
              Ok (filter (ATrs.brule (neg bsucc_gt)) D)
            else Ko _ ERuleNotInLargeOrdering_dp
        | Ko e => Ko _ e
      end.

  End poly_dp.

  (**********************************************************************************)
  (** ** Dependency proof of matrix interpretation over different domain. *)

  Section matrix_dp.

  (** Domain natural numbers:
     
     REMARK: the condition for matrix interpretation in [dp] that they are
     not require the restriction of positiveness of the upper left element
     anymore. *)

    (* TODO: comment about the condition. *)
    
    (* REMARK: the condition for matrix interpretation with dependency
    pairs consider the relation [>=](bge_nat). *)

    Definition type_matrix_naturals_dp a
      (is: list (symbol * cpf.arity * function)) dim :=
      Match map_rev (color_interpret_matrix a dim) is With ls ===>
      if forallb (fun x =>
        match x with
          existT f mi => bVforall
          (fun m => bge_nat (get_elem m (dim_pos dim) (dim_pos dim)) 0)(args mi)
        end) ls then
      let ma := TMatrixInt a ls in
        Ok (fun t u  => let (l, r) := rule_mi ma (mkRule t u) in bmint_ge l r,
          (fun t u => let (l, r) := rule_mi ma (mkRule t u) in bmint_gt l r))
        else Ko _ ENotMonotone_matrix_naturals_dp.
    
    Definition type_matrix_dp a is dom dim :=
      match dom with
        | Domain_naturals => type_matrix_naturals_dp a is dim
        | Domain_integers => Ko _ Ttype_polynomialDomain_integers
        | Domain_rationals delta => Ko _ Ttype_polynomialDomain_rationals
        | Domain_arctic dom' => Ko _ Ttype_polynomialDomain_arctic
        | Domain_tropical dom' => Ko _ Ttype_polynomialDomain_tropical
        | Domain_matrices dim sdim dom' =>
          Ko _ Ttype_polynomialDomain_matrices
      end.
    
    Definition matrix_interpretation_dp a (R D: arules a) is dom dim :=
      match type_matrix_dp a is dom dim with
        | Ok (bsucc_ge, bsucc_gt) =>
          if forallb (abrule bsucc_ge) D 
            && forallb (abrule bsucc_ge) R then
              Ok (filter (abrule (neg bsucc_gt)) D)
            else Ko _ ERuleNotInLargeOrdering_matrix_nat_dp
        | Ko e => Ko _ e
      end.

    (** Domain arctic natural numbers:
       
       There is no strictly monotone, linear arctic functions of more
       than one argument. Therefore we cannot apply this domain on
       full termination we change it to top termination problems,
       where only weak monotonicity is required.
       
       - Condition for an artic interperetation to be valid (finite):
       restrict first components of vectors to finite elements (i.e.,
       elements different than [-00] (infinite). An [n-ary] artic
       linear function over [A(N)] is called somewhere finite if
       [c(1)] is finite or [Mi[1,1]] is finite for some [1 <= i <=
       n]).
       
       - [i] is finite when [i <> -00]. *)

    Require Import color_matrix_arctic_nat AMatrixBasedInt2_ArcticNat.
    
    Definition type_matrix_arc_naturals_dp a
      (is: list (symbol * cpf.arity * function)) (dim: nat) :=
      Match map_rev (color_matrix_arc_interpret a dim) is With ls ===>
      if forallb (fun l =>
        match l with
          existT f mi => bVexists (fun m => is_finite (get_elem_arcnat m
            (dim_pos dim) (dim_pos dim))) (args_arcnat mi)
          || is_finite (Vnth (const_arcnat mi) (dim_pos dim)) end) ls then
      let ma_arcnat := TMatrixInt_arcnat a ls in
        Ok (fun t u => let (l, r) := rule_mi_arcnat ma_arcnat (mkRule t u) 
          in bmint_arc_ge l r,
          (fun t u => let (l, r) := rule_mi_arcnat ma_arcnat (mkRule t u)
            in bmint_arc_gt l r))
        else Ko _ ENotMonotone_matrix_arc_naturals.
    
    (* TODO: TTT2 generate the CPF file in the domain_matrices
     and in the arctic integer only *)
    
    Definition type_matrix_arc_polynomial_dp a is dom dim :=
      match dom with
        | Domain_naturals => type_matrix_arc_naturals_dp a is dim
        | Domain_integers => Ko _ Ttype_polynomialDomain_integers
        | Domain_rationals delta => Ko _ Ttype_polynomialDomain_rationals
        | Domain_arctic dom' => Ko _ Ttype_polynomialDomain_arctic
        | Domain_tropical dom' => Ko _ Ttype_polynomialDomain_tropical
        | Domain_matrices dim sdim dom' =>
          Ko _ Ttype_polynomialDomain_matrices
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

    Definition matrix_arc_interpretation_dp a (R D: arules a) is dom dim :=
      match type_matrix_arc_polynomial_dp a is dom dim with
        | Ok (bsucc_ge, bsucc_gt) =>
          if forallb (abrule bsucc_ge) D
            && forallb (abrule bsucc_ge) R then
              Ok (filter (abrule (neg bsucc_gt)) D)
            else Ko _ ERuleNotInLargeOrdering_matrix_arc_naturals
        | Ko e => Ko _ e
      end.

    (** Domain arctic integer numbers (below zero):

       The relation [>>] on vectors of arctic integers is "not"
       well-founded in general. To obtain that by restricting the first
       component of the vectors in is finite which restores
       well-foundedness. There is one exception: arctic addition is
       obvisously strict (>) if one argument is arctic zero i.e.,
       -oo. This is the motivation for introducing the following relation:
       [ a >> b <=> (a > b) \/ (a = b = -oo) ].
       - We need to make sure that we do not go outside of the domain, i.e.,
       the first vector component needs to be positive. An n-ary arctic
       linear function over A[Z] is called absolutely positive if (vector
       [c[1]]) is positive.
       - REMARK: the relation [>>] on vectors of arctic integers is not
       well-founded.
       - [is_above_zero] : [>= 0].
       - This method just happend at the top termination. (DP) *)
    
    Require Import color_matrix_arctic_below_zero AMatrixBasedInt2_ArcticBZ.
    
    Definition type_matrix_arcbz_integers_dp a 
      (is: list (symbol * cpf.arity * function)) dim :=
      Match map_rev (color_matrix_arcbz_interpret a dim) is With ls ===>
      if forallb (fun x =>
        match x with
          existT f mi => is_above_zero (Vnth (const_arcbz mi) (dim_pos dim))
        end) ls then
      let ma_arcbz := TMatrixInt_arcbz a ls in
        Ok (fun t u => let (l, r) := rule_mi_arcbz ma_arcbz (mkRule t u) in
          bmint_arc_bz_ge l r,
          (fun t u => let (l, r) := rule_mi_arcbz ma_arcbz (mkRule t u) in
            bmint_arc_bz_gt l r))
        else Ko _ ENotMonotone_matrix_arc_bz.
    
    (* TODO: TTT2 generate the CPF file in the domain_matrices
       and in the arctic integer only *)
    
    Definition type_matrix_arcbz_polynomial_dp a is dom dim :=
      match dom with
        | Domain_naturals => Ko _  Ttype_polynomialDomain_naturals
        | Domain_integers => type_matrix_arcbz_integers_dp a is dim
        | Domain_rationals delta => Ko _  Ttype_polynomialDomain_rationals
        | Domain_arctic dom' => Ko _ Ttype_polynomialDomain_arctic
        | Domain_tropical dom' => Ko _ Ttype_polynomialDomain_tropical
        | Domain_matrices dim sdim dom' =>
          Ko _ Ttype_polynomialDomain_matrices
      end.
  
    Definition matrix_arcbz_interpretation_dp a (R D: arules a) is dom dim:=
      match type_matrix_arcbz_polynomial_dp a is dom dim with
        | Ok (bsucc_ge, bsucc_gt) =>
          if forallb (abrule bsucc_ge) D
            && forallb (abrule bsucc_ge) R then
              Ok (filter (abrule (neg bsucc_gt)) D)
            else Ko _ ERuleNotInLargeOrdering_matrix_arcbz_dp
        | Ko e => Ko _ e
      end.
    
  End matrix_dp.

  (***********************************************************************)
  (** ** Standard polynomial orders with "dependency pairs method"
  over a specified domain (a semiring or something else): Polynomial
  interpretation over domain natural numbers, matrix interpretation
  over domain natural numbers, over domain arctic natural numbers and
  arctic integer numbers. *)

  (* REMARK: [dim] in matrix_interpretation has type [positiveInteger], in
  Coq positive starting from [1]. Natural numbers starting from [0]. *)

  (* Matrix interpretation on different domains of arctic. *)

  Definition matrix_interpretation_arctic_dp a (R D: arules a) dom dim is :=
    match dom with
      | Domain_naturals =>
        matrix_arc_interpretation_dp R D is dom (nat_of_P dim)
      | Domain_integers =>
        matrix_arcbz_interpretation_dp R D is dom (nat_of_P dim)
      | _ => Ko _ Todo (* FIXME: add error *)
    end.

  (* Reduction pair of matrix interpretation on domain: naturals and arctic. *)

  Definition redPair_matrixInt a (R D: arules a) dom dim is :=
    match dom with
      | Domain_naturals =>
        matrix_interpretation_dp R D is dom (nat_of_P dim)
      | Domain_integers => Ko _ Ttype_polynomialDomain_integers
      | Domain_rationals delta => Ko _ Ttype_polynomialDomain_rationals
      | Domain_arctic dom' => matrix_interpretation_arctic_dp R D dom' dim is
      | Domain_tropical dom' =>
        Ko _ Ttype_polynomialDomain_tropical (* TODO *)
      | Domain_matrices dim sdim dom' =>
        Ko _ Ttype_polynomialDomain_matrices
    end.

  (** Reduction pair interpretation: polynomial interpretation and
  matrix interpretation. *)

  Definition redPair_interpretation_dp a (R D : arules a) t is :=
    match t with
      | Type_polynomial dom degmax =>
        polynomial_interpretation_dp R D is dom
      | Type_matrixInterpretation dom dim sdim =>
        redPair_matrixInt R D dom dim is
    end.

  (***********************************************************************)
  (** ** Reduction pair path ordering is an ordering introduced by
     Dershowitz. It extends a well-founded order on the signature,
     called a precedence, to a reduction order on terms. *)

  Section rpo_dp.

    Require Import Coccinelle2 ordered_set rpo_extension2
      cpf2color_rpo rainbow_full_termin AFilterPerm AProj
      cpf2color_argfilter.

    (* Assume the varibale number [bb] of rpo. *)

    Variable bb: nat.
    
    (** Path ordering without argument filtering method *)

    (* FIXME: take a look at list reverse: it is not the reverse list. *)

    Definition pathOrder_term_dp a
      (l: list (symbol * cpf.arity * nonNegativeInteger * t2)) :
      cpf_util.result ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)) :=
      if forallb (fun f => forallb (fun g => @bprec_eq_status_symb a l f g)
        (list_sig l))(list_sig l) then
      Ok ((fun t u =>
        let t' := @term_of_aterm (Sig a) t in
          let u' := @term_of_aterm (Sig a) u in
            match rpo_eval l bb t' u' with
              | Some Equivalent | Some Greater_than => true
              | _ => false
            end),     
          (fun t u =>
        let t' := @term_of_aterm (Sig a) t in
          let u' := @term_of_aterm (Sig a) u in
            match rpo_eval l bb t' u' with
              | Some Greater_than => true
              | _ => false
            end))
        else Ko _ ENotpathOrder_term.
    
    (** Path ordering with argument filtering method. *)

    Open Scope nat_scope. 

    (** Define a function checking each cases of argument filter.
       check if they used collapsing/non-collapsing then use the rpo +
       projection + perm, otherwise return [error]. *)
    
    Definition pathOrder_rpo_proj_filter_dp a
      (l: list (symbol * cpf.arity * nonNegativeInteger * t2))
      (args : list (symbol * cpf.arity * t3))
      : cpf_util.result ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)) :=
      if forallb (fun f => forallb (fun g => @bprec_eq_status_symb a l f g)
        (list_sig l))(list_sig l) then
      Ok ((fun t u =>
        let sig := Sig (@ASignature.arity (Sig (filter_arity (Sig a)
          (color_pi_filter args a)))) in
        let t' := @term_of_aterm sig (color_proj args (@color_filter args a t)) in
          let u' := @term_of_aterm sig (color_proj args (@color_filter args a u)) in
        match rpo_eval l bb t' u' with
          | Some Equivalent | Some Greater_than => true
          | _ => false
        end),
      (fun t u =>
        let sig := Sig (@ASignature.arity (Sig (filter_arity (Sig a)
          (color_pi_filter args a)))) in
        let t' := @term_of_aterm sig (color_proj args (@color_filter args a t)) in
          let u' := @term_of_aterm sig (color_proj args (@color_filter args a u)) in
        match rpo_eval l bb t' u' with
          | Some Greater_than => true
          | _ => false
        end))
      else Ko _ EPrecedence_incompatible_statuses_dp.

    (** Define a function checking each cases of argument filter.
       Check if it is a collapsing case then use the rpo + projection,
       otherwise check if it is a non collapsing then use the rpo +
       perm, check if they used both cases then use the rpo +
       projection + perm, otherwise return [error].  *)

    Definition pathOrder_term_rpo_af_dp a
      (l: list (symbol * cpf.arity * nonNegativeInteger * t2))
      (args : list (symbol * cpf.arity * t3))
      : cpf_util.result ((aterm a -> aterm a -> bool) * (aterm a -> aterm a -> bool)) :=
      match args with
        | (_, _, t) :: _ =>
          match is_col_noncol t with
            | true => 
              Match pathOrder_rpo_proj_filter_dp a l args With rpo_proj_filter ===>
              Ok rpo_proj_filter
            | false => Ko _ EargumentFilter_false
          end
        | nil => Ko _ EargumentFilter_nil
      end.

    (** Define a function that return a type [result arules]. The path
       order in combination with the argument filter or without the
       argument filter. *)

    (** In the case RPO + AF: there are three cases:
       that embedded RPO's term to AF's term:
       - RPO's term + AF's project term, in the case of collapsing
       - RPO's term + AF's perm term, in the case of non collapsing
       - RPO's term + AP's project and perm term. *)

    Definition pathOrder_dp a (R D: arules a) sp (af: option argumentFilter)
      : cpf_util.result (arules a) :=
      match af with
        | Some af => (* combination with argument filter *)
          match pathOrder_term_rpo_af_dp a sp af with
            | Ok (bsucc_ge, bsucc_gt) =>
             if forallb (abrule bsucc_ge) D (* all [>=] in D*)
               && forallb (abrule bsucc_ge) R then (* all [>=] in R *)
                 Ok (List.filter (abrule (neg bsucc_gt)) D) (* remove all [>] in D *)
               else Ko _ ENotpathOrder_AF_dp
            | Ko e => Ko _ e
          end
        | None => (* without argument filter *)
          match pathOrder_term_dp a sp with
            | Ok (bsucc_ge, bsucc_gt) =>
             if forallb (abrule bsucc_ge) D (* all [>=] in D*)
               && forallb (abrule bsucc_ge) R then (* all [>=] in R *)
                 Ok (List.filter (abrule (neg bsucc_gt)) D) (* remove all [>] in D *)
               else Ko _ ENotpathOrder_dp
            | Ko e => Ko _ e
          end
      end.

  End rpo_dp.

  (***********************************************************************)
  (** Ordering constrainst proof with reduction pair interpretation of
   dependency pair transformation. Currently support interpretation
   and path ordering. *)
  
  Variable bb: nat.

  Definition orderingConstraintProof_redPair_dp a (R D: arules a) rp :=
    match rp with
      | RedPair_interpretation t is => redPair_interpretation_dp R D t is
      | RedPair_pathOrder sp oaf => pathOrder_dp bb R D sp oaf
      (*| RedPair_knuthBendixOrder _ _ _ =>
        Ko _ TorderingConstraintProof_redPair_knuthBendixOrder
      | RedPair_scnp _ _ _ => Ko _ TorderingConstraintProof_redPair_scnp*)
    end.
  
  Definition trsTerminationProof_ruleRemoval_dp a (R D: arules a) ocp :=
    match ocp with
      | OrderingConstraintProof_redPair rp =>
        orderingConstraintProof_redPair_dp R D rp
      | OrderingConstraintProof_satisfiableAssumption _ =>
        Ko _ TOrderingConstraintProof_satisfiableAssumption
    end.

  (***********************************************************************)
  (** ** Check that [D = dp R] is a trivial proof by stating the set
  of DPs is empty valid termination proof for [hd_red_mod R D]. *)

  Section dp_proof.
  
    (** [nat_of_string]: convert variable map to natural number. *)

    Variable nat_of_string : string -> nat.
 
    Definition dpProof_pIsEmpty a (D: arules a) :=
      if is_empty D then OK else Ko _ ErDPNotEmpty.

    (** Decomposition of an over DP graph of dependency pair proof for
       [hd_red_mod R D].

       - A decomposition of a list of rules is a list of list of
         rules. *)

    (* WARNING: the list of DPs is reversed since in CPF, all forward
    arcs are given while in Rainbow, there must be no forward arcs. *)

    Definition decomp_aux a
      (ci: cpf.dps*boolean*option (list positiveInteger)*option cpf.dpProof) :=
      match ci with
        | (dps, b, f, p) =>
          Match map_rev (color_rule a nat_of_string) dps With dps'
          ===> Ok (dps', b, f, p)
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

    Require Import AReverse AUnary cpf2color_argfilter.

    Fixpoint dpProof (n: nat) a (R D: arules a) p {struct n} : result unit :=
      match n with
        | 0 => Ko _ TDpProof_zerobound
        | S m =>
          match p with
            | DpProof_pIsEmpty => dpProof_pIsEmpty D
            | DpProof_depGraphProc cs =>
              depGraphProc m R D cs
            | DpProof_redPairProc (Some _) _ _ _ => Ko _ TDpProof_redPairProc
            | DpProof_redPairProc None ocp dps p =>
              Match trsTerminationProof_ruleRemoval_dp R D ocp With D' ===>
                 dpProof m R D' p
            | DpProof_redPairUrProc oc ocp dps usr p =>
              Ko _ TDpProof_redPairUrProc
            | DpProof_monoRedPairProc (Some _) _ _ _ _ =>
              Ko _ TDpProof_monoRedPairProc
            | DpProof_monoRedPairProc None ocp dps rs p =>
              Match trsTerminationProof_ruleRemoval_dp R D ocp With D' ===>
                dpProof m R D' p
            | DpProof_monoRedPairUrProc oc ocp dps rs usr p =>
              Ko _ TDpProof_monoRedPairUrProc 
            | DpProof_subtermProc _ _ _ _ => Ko _ TDpProof_subtermProc
            | DpProof_semlabProc _ _ _ _ => Ko _ TDpProof_semlabProc
            | DpProof_unlabProc dps rs p => Ko _ TDpProof_unlabProc
            | DpProof_sizeChangeProc t1 l => Ko _ TDpProof_sizeChangeProc
            | DpProof_flatContextClosureProc s cs dps rs p =>
              Ko _ TDpProof_flatContextClosureProc
            | DpProof_argumentFilterProc args dps rs p =>
              AF_dp m R D args p
            | DpProof_finitenessAssumption i =>
              Ko _ TDpProof_finitenessAssumption
            (*| DpProof_usableRulesProc _ _ =>
              Ko _ TDpProof_usableRulesProc
            | DpProof_innermostLhssRemovalProc _ _ =>
              Ko _ TDpProof_innermostLhssRemovalProc
            | DpProof_switchInnermostProc _ _ =>
              Ko _ TDpProof_switchInnermostProc
            | DpProof_rewritingProc _ _ _ _ _ =>
              Ko _ TDpProof_rewritingProc
            | DpProof_instantiationProc _ _ _ =>
              Ko _ TDpProof_instantiationProc
            | DpProof_forwardInstantiationProc _ _ _ _ =>
              Ko _ TDpProof_forwardInstantiationProc
            | DpProof_narrowingProc _ _ _ _ =>
              Ko _ TDpProof_narrowingProc
            | DpProof_splitProc _ _ _ _ =>
              Ko _ TDpProof_splitProc
            | DpProof_generalRedPairProc _ _ _ _ _ _ _ =>
              Ko _ TDpProof_generalRedPairProc
            | _ => Ko _ TdpProof*)
          end
      end
 
    (* translate rules to proj_rules in the case of AProj
       and in the case of Filter translate rules to filter_rules *)

    with AF_dp n a (R D: arules a) args p {struct n}:=
      match n with
        | 0 => Ko _ TDpProof_zerobound
        | S m =>
          match args with
            | (f, _, t) :: l' => (* Projection *)
              if is_collapsing t then
                let pR := color_proj_rules args R in
                  let pD := color_proj_rules args D in
                    dpProof m pR pD p
                else (* Filter *) (* This function need [bnon_dup] and [color_build_pi]. *)
                  if is_noncollapsing t
                  && bnon_dup (Sig a)(color_raw_pi_filter a args) (list_split_triple args)
                  then
                    let fR := color_filter_rules (color_build_pi args) R in 
                      let fD := color_filter_rules (color_build_pi args) D in
                      dpProof m fR fD p
                    else AF_dp m R D l' p
            | nil => Ko _ Edp_argumentfilter
          end
      end

    (* Each SCC terminates whether if SCC is truly a SCC then check it
       WF; if SCC is not a SCC then test co_scc = true (means there is
       no edge from i -> j (j > i) *)

    with depGraphProc (n : nat) a (R D : arules a) cs {struct n} :=
      match n with
        | 0 => Ko _ TDpProof_zerobound
        | S m =>
          if forallb (@is_notvar_lhs (Sig a)) R && forallb (undefined_rhs R) D &&
            brules_preserve_vars D then
              Match decomp a cs With cs' ===>
              let ls := split_list cs' in
                if equiv_rules (flat ls) D then
                  let approx := dpg_unif_N n R D in (* n = 20 *)
                    if valid_decomp approx ls then
                      if forallb (fun ci =>
                        let '(dps, b, _, op) := ci in
                          match b, op with
                            | true, Some pi => bool_of_result (dpProof m R dps pi)
                            | false, _ => co_scc approx dps
                            | _, _ => false
                          end) cs' then OK
                        else Ko _ Todo
                      else Ko _ Todo
                  else Ko _ ENotDepPairs_graph
            else Ko _ TdepGraphProc
      end.

    Close Scope nat_scope.

    (***********************************************************************)
    (** ** Dependency pair transformation:
       - Without mark symbols: rewriting with the rules is not allowed
         at the root.
       - With mark symbols: the whole dp-proof is using the notion of
       chain where rewriting with the rules is applied at arbitrary
       positions (including the root). *)
    
    Variable n : nat.
    
    Definition dpTrans_unmark a (R:arules a) (dps: rules) (p: cpf.dpProof)
      : result unit :=
      Match color_rules a nat_of_string dps With D ===>
      if equiv_rules D (dp R)
        then dpProof n R D p
        else Ko _ EDPTransUnmark.

    Require Import AReverse AUnary cpf2color ATerm_of_String.

    Definition dpTrans_mark a (R:arules a) (dps: rules) (p:cpf.dpProof):
      result unit :=
      Match color_rules (dp_arity a) nat_of_string dps With D' ===>
      let rs := Fl (HFSig_of_dup_Sig_eq (arity := a))
        (dup_int_rules R) in
        let rs' := Fl (HFSig_of_dup_Sig_eq (arity := a))
          (dup_hd_rules (dp R)) in
          if equiv_rules D' rs' then
            dpProof n rs D' p else  Ko _ EDPTransMark.
    
    (** Termination proof with dependency pair transformation with
       mark and unmark symbols where the left hand side rules has no
       variable and the variables are preserve. *)
    (* If trs in the case of string reverse, then translate
       rule into reverse_trs, otherwise keep rules. *)

    (* FIXME: Four conditions: no_lhs_var (R), no_lhs_var (dp R), and
       no_rhs_var (dp R) and rule_preserve_var R *)

    Definition trsTerminationProof_dpTrans a (R:arules a) (dps: rules) (b:bool)
      (p: cpf.dpProof): result unit :=
      if forallb (@is_notvar_lhs (Sig a)) R &&  
        forallb (@is_notvar_lhs (Sig a)) (dp R) && 
         forallb (@is_notvar_rhs (Sig a)) (dp R) &&
         brules_preserve_vars R then
        if b then dpTrans_mark R dps p
          else dpTrans_unmark R dps p
        else Ko _ EDPTrans.

  End dp_proof. 

End Top_Termination.
