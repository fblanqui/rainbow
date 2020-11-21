(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-25 (setoid)
- Adam Koprowski and Johannes Waldmann, 2008-01
*)

Set Implicit Arguments.

Require Import AMonAlg2 OrdSemiRing2 ATrs LogicUtil RelUtil NatUtil
  AWFMInterpretation Max VecEq Setoid VecOrd Matrix2 VecUtil
  VecArith2.

(***********************************************************************)
(** * Matrix interpretation over domain arctic integer numbers-below
zero. *)

Section MatrixLinearFunction_arcbz.
  
  Variables (matrix_arcbz : nat -> nat -> Type) (dim argCnt : nat).
  
  (** [const_arcbz] being a constant vector of the interpretation of
     size [dim] and [args_arcbz] representing coefficients for the
     arguments with a [dim x dim] matrix per argument. *)
  
  Record matrixInt_arcbz : Type := mkMatrixInt_arcbz {
    const_arcbz : vector Arbz dim;
    args_arcbz : vector (matrix_arcbz dim dim) argCnt
  }.
  
End MatrixLinearFunction_arcbz.

Implicit Arguments mkMatrixInt_arcbz [matrix_arcbz dim argCnt].

Section S.
  
  Variable Sig: Signature.
  Variable dim : nat.
  Parameter dim_pos : dim > 0.

  (** Matrix based int over domain arctic integer numbers - below zero *)
  
  Section Arctic_int.
    
    Section Conf.
      
      Notation matrixInt := (matrixInt_arcbz matrix_arcbz).
      
      (* TODO: missing trsInt_Ok *)
      Record MatrixMethodConf_arcbz : Type := mkMatrixMethodConf_arcbz
        { trsInt_arcbz : forall f : Sig, matrixInt dim
          (ASignature.arity f) }.
      
      Notation vec := (vector Arbz dim).

      Definition vec_at0_arcbz (v: vec) := Vnth v dim_pos .
      
      Notation "x >>= y" := (gerbz x y) (at level 70).
      
      Definition vec_invariant_arcbz (v : vec) := vec_at0_arcbz v >>=
        A1rbz.
      
      Lemma inv_id_matrix_arcbz : vec_invariant_arcbz (Vreplace
        (Vconst A0rbz dim) dim_pos A1rbz).

      Proof.
        unfold vec_invariant_arcbz, vec_at0_arcbz.
        rewrite Vnth_replace. apply ge_reflrbz.
      Qed.
      
    End Conf.
    
    Section MatrixBasedInt_arcbz.
      
      Notation A := Arbz.
      Notation A0 := A0rbz.
      Notation A1 := A1rbz.
      Notation eqA := eqArbz.
      Notation sid_theoryA := sid_theoryArbz.
      Notation ge := gerbz.
      Notation ge_refl := ge_reflrbz.
      Notation ge_trans := ge_transrbz.
      
      (* Define Morphism [vector_plus_mor] to be able to use [rewrite]
       at the Lemma [mint_eval_var_aux] later. *)
      Add Parametric Morphism n : (@vector_plus_arcbz n) with
        signature (@eq_vec_arcbz n) ==> (@eq_vec_arcbz n) ==>
        (@eq_vec_arcbz n) as vector_plus_mor_arcbz.

      Proof.
        intros. apply Vforall2n_intro. intros. unfold vector_plus_arcbz.
        repeat rewrite Vnth_map2.
        (*FIXME: rewrite H does not work even if Vnth is declared as morphism *)
        apply Aplus_morrbz; apply (Vnth_mor eqArbz); hyp.
      Qed.
      
      (* Add new setoid to be able to use [sym] at [eqA] use later in
      some lemma. *)

      Add Setoid A eqA sid_theoryA as A_Setoid_arcbz.
      
      (* Define [ge] relation to be able to use [trans] for morphism
      of [vec_ge_mor]. *)

      Add Relation A ge reflexivity proved by ge_refl transitivity
        proved by ge_trans as ge_rel_arcbz.

      (* Define morphism to be able to rewrite [vec_ge_mor] later. *)
      Add Parametric Morphism n : (@vec_ge_arcbz n) with signature
        (@eq_vec_arcbz n) ==> (@eq_vec_arcbz n) ==> iff as
          vec_ge_mor_arcbzarcbz.

      Proof.
        unfold vec_ge_arcbz. intros. apply (Vforall2n_mor sid_theoryArbz).
        intuition.
        trans a1. apply eq_ge_compatrbz. sym. hyp.
        trans a2. hyp. apply eq_ge_compatrbz. hyp.
        trans a1'. apply eq_ge_compatrbz. hyp.
        trans a2'. hyp. apply eq_ge_compatrbz. sym. hyp.
        hyp. hyp.
      Qed.
      
      Implicit Arguments vec_ge_mor_arcbz [n x y x0 y0].
      
      (* Define this relation on [vec_eq] to be able to use
         [symm], etc. *)
      Add Parametric Relation n : (vector Arbz n) (@eq_vec_arcbz n)
        reflexivity proved by (@eq_vec_refl A eqA sid_theoryA n)
        symmetry proved by (@eq_vec_sym A eqA sid_theoryA n)
          transitivity proved by (@eq_vec_trans A eqA sid_theoryA n) as
            eq_vec_rel_arcbz.

      (* Add these relations and morphisms to be able to use it rewriting
         and [trans], etc later for matrix.
         Add [mat_eqA] to be able to use rewrite [mat_mult_id_l] *)
      Add Parametric Relation m n : (matrix_arcbz m n) (@mat_eqA_arcbz
        m n) reflexivity proved by (@mat_eqA_refl_arcbz m n) symmetry
      proved by (@mat_eqA_sym_arcbz m n) transitivity proved by
        (@mat_eqA_trans_arcbz m n) as mat_eqA_rel_arcbz.

      (* Define this morphism to be able to use rewrite
      [zero_matrix_mult_l]. *)

      Add Parametric Morphism m n i (h:i<n) : (fun M => @get_col_arcbz
        m n M i h) with signature (@mat_eqA_arcbz m n) ==>
      (@eq_vec_arcbz m) as get_col_mor_arcbz.

      Proof.
        intros. unfold eq_vec_arcbz. apply Vforall2n_intro. intros.
        repeat rewrite <- get_elem_swap_arcbz. apply H.
      Qed.
      
      (* Define this morphism to be able to use [rewrite H0] in
      [mat_vec_prod_mor]. *)

      Add Parametric Morphism n : (@vec_to_col_mat_arcbz n) with
        signature (@eq_vec_arcbz n) ==> (@mat_eqA_arcbz n 1) as
          vec_to_col_mat_mor_arcbz.
        
      Proof.
        unfold vec_to_col_mat_arcbz, mat_eqA_arcbz, get_elem_arcbz. intros.
        repeat rewrite get_elem_swap_arcbz. unfold get_col_arcbz.
        repeat rewrite Vnth_map.
        apply (Vnth_mor eqA). rewrite (eq_vec_cons eqA). intuition.
        apply (Vnth_mor eqA). hyp.
      Qed.
      
      (* Define this morphism to be able to use [rewrite H] for
      [mat_vec_prod_mor]. *)

      Add Parametric Morphism m n p : (@mat_mult_arcbz m n p) with
        signature (@mat_eqA_arcbz m n) ==> (@mat_eqA_arcbz n p) ==>
        (@mat_eqA_arcbz m p) as mat_mult_mor_arcbz.

      Proof.
        unfold mat_mult_arcbz. intros. unfold mat_eqA_arcbz. intros.
        repeat rewrite mat_build_elem_arcbz. apply dot_product_mor_arcbz.
        apply get_row_mor_arcbz. hyp. apply get_col_mor_arcbz. hyp.
      Qed.
      
      (* Define this morphism to be able to rewrite
      [mat_vec_prod_distr_vec] later. *)
      
      Add Parametric Morphism m n : (@mat_vec_prod_arcbz m n) with
        signature (@mat_eqA_arcbz m n) ==> (@eq_vec_arcbz n) ==>
        (@eq_vec_arcbz m) as mat_vec_prod_mor_arcbz.

      Proof.
        unfold mat_vec_prod_arcbz. intros.
        apply get_col_mor_arcbz. rewrite H. rewrite H0.
        refl.
      Qed.
      
      (* Adding notations *)

      Notation vec := (vector Arbz dim).
      Notation eq_vec_st := (@eq_vec_st _ _ sid_theoryArbz dim).
      Notation mat_eqA := (@mat_eqA_arcbz dim dim).
      Notation mat_eqA_st := (@mat_eqA_st_arcbz dim dim). 
      Notation matrixInt := (matrixInt_arcbz matrix_arcbz).
      Notation mint := (matrixInt dim).
      Notation mat := (matrix_arcbz dim dim).
      Notation eq_vec_st' := (@eq_vec_st _ _ sid_theoryArbz dim).
      Notation eq_vec_mat_eqA_st' := (@VecEq.eq_vec_st _ _ mat_eqA_st).
      Notation eq_vec := (@eq_vec_arcbz dim).
      Notation "x =v y" := (eq_vec x y)(at level 70).
      Notation "x >>= y" := (gerbz x y) (at level 70).
      
      Infix "[+]" := vector_plus_arcbz (at level 50).
      Infix "<*>" := mat_mult_arcbz (at level 40).
      
      Add Parametric Relation k : (vector vec k) (@VecEq.eq_vec _
        eq_vec k) reflexivity proved by (@eq_vec_refl _ _ eq_vec_st k)
      symmetry proved by (@eq_vec_sym _ _ eq_vec_st k) transitivity
        proved by (@eq_vec_trans _ _ eq_vec_st k) as
          eq_vec_eq_vec_rel_arcbz.
      
      Add Parametric Relation k : (vector (matrix_arcbz dim dim) k)
        (@VecEq.eq_vec _ mat_eqA k) reflexivity proved by (@eq_vec_refl
          _ _ mat_eqA_st k) symmetry proved by (@eq_vec_sym _ _ mat_eqA_st
            k) transitivity proved by (@eq_vec_trans _ _ mat_eqA_st k) as
          eq_vec_mat_eqA_rel_arcbz.
      
      Definition eq_mint_arcbz k (mi1 mi2 : mint k) :=
        let (c1, args1) := mi1 in
          let (c2, args2) := mi2 in
            c1 =v c2 /\ VecEq.eq_vec mat_eqA args1 args2.
      
      Notation "x =i y" := (eq_mint_arcbz x y) (at level 70).
      
      Lemma eq_mint_refl_arcbz : forall k (x : mint k), x =i x.
        
      Proof.
        unfold eq_mint_arcbz. destruct x. intuition.
      Qed.
      
      Lemma eq_mint_sym_arcbz : forall k (x y : mint k), x =i y -> y
        =i x.
        
      Proof.
        unfold eq_mint_arcbz. destruct x. destruct y. intuition.
      Qed.
      
      Lemma eq_mint_trans_arcbz : forall k (x y z : mint k), x =i y ->
        y =i z -> x =i z.
        
      Proof.
        unfold eq_mint_arcbz. destruct x. destruct y. destruct z. intuition.
        trans const_arcbz1; hyp. trans args_arcbz1; hyp.
      Qed.
      
      Add Parametric Relation k : (@mint k) (@eq_mint_arcbz k)
        reflexivity proved by (@eq_mint_refl_arcbz k) symmetry proved
          by (@eq_mint_sym_arcbz k) transitivity proved by
            (@eq_mint_trans_arcbz k) as eq_mint_rel_arcbz.
      
      Add Parametric Morphism k : (@mkMatrixInt_arcbz matrix_arcbz dim
        k) with signature eq_vec ==> (@VecEq.eq_vec _ mat_eqA k) ==>
      (@eq_mint_arcbz k) as mkMatrixInt_mor_arcbz.
        
      Proof.
        unfold eq_mint_arcbz. auto.
      Qed.
      
      Add Parametric Morphism k : (@const_arcbz matrix_arcbz dim k)
        with signature (@eq_mint_arcbz k) ==> eq_vec as const_mor_arcbz.
        
      Proof.
        destruct x. destruct y. simpl. intuition.
      Qed.
      
      Add Parametric Morphism k : (@args_arcbz matrix_arcbz dim k)
        with signature (@eq_mint_arcbz k) ==> (@VecEq.eq_vec _ mat_eqA
          k) as args_mor_arcbz.
        
      Proof.
        destruct x. destruct y. simpl. intuition.
      Qed.
      
      Section MBI.
        
        Definition dom_arcbz := { v : vec | vec_invariant_arcbz v }.
        
        Definition dom2vec_arcbz (d : dom_arcbz) : vec := proj1_sig d.
        
        Definition add_matrices_arcbz i m n (v : vector (matrix_arcbz
          m n) i) := Vfold_left (@mat_plus_arcbz m n)
        (zero_matrix_arcbz m n) v.
        
        Definition mi_eval_aux_arcbz n (mi : mint n) (v : vector vec
          n) : vec := add_vectors_arcbz (n:=dim) (k:=n)(Vmap2
            (@mat_vec_prod_arcbz dim dim) (args_arcbz mi) v) [+]
          const_arcbz mi.
        
        Add Parametric Morphism n : (@mi_eval_aux_arcbz n) with
          signature (@eq_mint_arcbz n) ==> (@VecEq.eq_vec _ eq_vec n)
          ==> eq_vec as mi_eval_aux_mor_arcbz.
          
        Proof.
          unfold mi_eval_aux_arcbz. intuition. apply vector_plus_mor_arcbz.
          apply add_vectors_mor_arcbz.
          apply Vforall2n_intro. intros. repeat rewrite Vnth_map2.
          apply mat_vec_prod_mor_arcbz.
          apply (Vnth_mor mat_eqA). rewrite H. refl.
          apply (Vnth_mor eq_vec). hyp.
          rewrite H. refl.
        Qed.
        
        Variable ma : MatrixMethodConf_arcbz.

        Variable mi_eval_ok : forall f v, vec_invariant_arcbz
          (mi_eval_aux_arcbz (trsInt_arcbz ma f) (Vmap dom2vec_arcbz
            v)).

        Definition mi_eval_arcbz f (v : vector dom_arcbz
          (ASignature.arity f)) : dom_arcbz := exist (fun v =>
            vec_invariant_arcbz v) (mi_eval_aux_arcbz (trsInt_arcbz ma
              f) (Vmap dom2vec_arcbz v)) (mi_eval_ok f v).

        Lemma mi_eval_cons_arcbz : forall n (mi : mint (S n)) v vs,
          mi_eval_aux_arcbz mi (Vcons v vs) =v mat_vec_prod_arcbz
          (Vhead (args_arcbz mi)) v [+] mi_eval_aux_arcbz
          (mkMatrixInt_arcbz (const_arcbz mi) (Vtail (args_arcbz mi)))
          vs.

        Proof.
          intros. unfold mi_eval_aux_arcbz. simpl.
          rewrite vector_plus_assoc_arcbz.
          apply vector_plus_mor_arcbz.
          apply vector_plus_comm_arcbz. refl.
        Qed.
        
        Definition dom_zero_arcbz: dom_arcbz.

        Proof.
          exists (Vreplace (Vconst A0rbz dim) dim_pos A1rbz).
          apply inv_id_matrix_arcbz.
        Defined.

        Definition I_arcbz := @mkInterpretation Sig dom_arcbz
          dom_zero_arcbz mi_eval_arcbz.

      (*REMOVE: unusued
         Variable succ : relation dom.
         Notation "x >v y" := (succ x y) (at level 70).*)

        Infix ">=v" := vec_ge_arcbz (at level 70).

        Definition succeq_arcbz (x y : dom_arcbz) := (dom2vec_arcbz x)
          >=v (dom2vec_arcbz y).

        Lemma refl_succeq_arcbz : reflexive succeq_arcbz.
          
        Proof.
          intro x. apply vec_ge_refl_arcbz.
        Qed.

        Lemma trans_succeq_arcbz : transitive succeq_arcbz.
          
        Proof.
          unfold succeq_arcbz.
          apply Rof_trans with (f:=dom2vec_arcbz).
          apply vec_ge_trans_arcbz.
        Qed.

        (** Monotonicity *)
        
        Section VecMonotonicity_arcbz.

          Variable f : matrix_arcbz dim dim -> vec -> vec.
          Variable f_mon : forall M v1 v2, v1 >=v v2 -> f M v1 >=v f M v2.
          Variables (a b : vec).

          Lemma vec_add_weak_monotone_map2_arcbz : forall n1 (v1 :
            vector vec n1) n2 (v2 : vector vec n2) n (M : vector
              (matrix_arcbz dim dim) n) i_j, a >=v b ->
            add_vectors_arcbz (Vmap2 f M (Vcast (Vapp v1 (Vcons a v2))
              i_j)) >=v add_vectors_arcbz (Vmap2 f M (Vcast (Vapp v1
                (Vcons b v2)) i_j)).

          Proof.
            induction v1; intros; simpl.
            destruct n; try solve [NatUtil.absurd_arith].
            unfold add_vectors_arcbz, succeq_arcbz,
              vec_ge_arcbz. simpl. apply Vforall2n_intro. 
            intros. unfold vector_plus_arcbz. do 2 rewrite Vnth_map2.
            assert (Vnth (f (Vhead M) a) ip >>= Vnth (f (Vhead M) b) ip).
            apply Vforall2n_nth. apply f_mon. hyp.
            apply plus_ge_compat_arcbz. apply ge_reflrbz. hyp.
            destruct n0; try solve [NatUtil.absurd_arith].
            unfold add_vectors_arcbz, succeq_arcbz, vec_ge_arcbz.
            simpl. apply Vforall2n_intro. 
            intros. unfold vector_plus_arcbz. do 2 rewrite Vnth_map2.
            apply plus_ge_compat_arcbz. 
            apply Vforall2n_nth.
            unfold add_vectors_arcbz in IHv1. apply IHv1.
            hyp. apply ge_reflrbz.
          Qed.
          
        End VecMonotonicity_arcbz.

        Lemma monotone_succeq_arcbz : monotone I_arcbz succeq_arcbz.

        Proof.
          intros f i j i_j vi vj a b ab.
          simpl. unfold mi_eval_arcbz, mi_eval_aux_arcbz,
          succeq_arcbz. simpl.
          apply (@vec_plus_ge_compat_r_arcbz dim).
          do 2 rewrite Vmap_cast. do 2 rewrite Vmap_app. simpl.
          apply vec_add_weak_monotone_map2_arcbz; trivial.
          intros. unfold succeq_arcbz, vec_ge_arcbz.
          apply Vforall2n_intro. intros.
          unfold mat_vec_prod_arcbz.
          do 2 rewrite Vnth_col_mat_arcbz. apply mat_mult_mon_arcbz.
          apply mat_ge_refl_arcbz. intros x y xp yp.
          do 2 rewrite vec_to_col_mat_spec_arcbz.
          apply Vforall2n_nth. hyp.
        Qed.

        Lemma succeq_dec_arcbz : rel_dec succeq_arcbz.
          
        Proof.
          intros x y. unfold succeq_arcbz,
          vec_ge_arcbz. apply Vforall2n_dec.
          intros m1 n. apply ge_decrbz.
        Defined.

        (** Decidability of order on terms induced by matrix
           interpretations. *)

        Section OrderDecidability_arcbz.
          
          Require Import ABterm.
          
          Notation bterm := (bterm Sig).

          (** Symbolic computation of term interpretation. *)
          
          Definition mat_matrixInt_prod_arcbz n M (mi : mint n) : mint
            n := mkMatrixInt_arcbz (mat_vec_prod_arcbz M (const_arcbz
              mi)) (Vmap (mat_mult_arcbz M) (args_arcbz mi)).

          Definition combine_matrices_arcbz n k (v : vector (vector
            mat k) n) := Vbuild (fun i ip => add_matrices_arcbz (Vmap
              (fun v => Vnth v ip) v)).

          Lemma combine_matrices_nil_arcbz : forall i,
            combine_matrices_arcbz Vnil = Vconst (@zero_matrix_arcbz
              dim dim) i.
            
          Proof.
            intros. apply Veq_nth. intros. unfold combine_matrices_arcbz.
            rewrite Vnth_const. rewrite Vbuild_nth. trivial.
          Qed.

          Lemma combine_matrices_cons_arcbz : forall k n v (vs :
            vector (vector mat k) n), combine_matrices_arcbz (Vcons v
              vs) = Vmap2 (@mat_plus_arcbz _ _) (combine_matrices_arcbz
                vs) v.

          Proof.
            intros. apply Veq_nth. intros.
            unfold combine_matrices_arcbz, add_matrices_arcbz. simpl.
            rewrite Vnth_map2. do 2 rewrite Vbuild_nth. refl.
          Qed.

          Fixpoint mi_of_term_arcbz k (t : bterm k) : mint (S k) :=
            match t with
              | BVar i ip => 
                let zero_int := Vconst (zero_matrix_arcbz dim dim) (S k) in
                  let args_int := Vreplace zero_int (le_lt_S ip) (id_matrix_arcbz dim) in
                    mkMatrixInt_arcbz (@zero_vec_arcbz dim) args_int
              | BFun f v => 
                let f_int := trsInt_arcbz ma f in
                  let args_int := Vmap (@mi_of_term_arcbz k) v in
                    let args_int' := Vmap2 (@mat_matrixInt_prod_arcbz (S k)) 
                      (args_arcbz f_int) args_int in
                      let res_const := add_vectors_arcbz (Vcons (const_arcbz f_int) 
                        (Vmap (@const_arcbz matrix_arcbz dim (S k)) args_int')) in
                      let res_args := combine_matrices_arcbz
                        (Vmap (@args_arcbz matrix_arcbz dim (S k)) 
                          args_int') in
                        mkMatrixInt_arcbz res_const res_args
            end.

          Require Import ATrs.

          Definition rule_mi_arcbz r :=
            let mvl := maxvar (lhs r) in
              let mvr := maxvar (rhs r) in
                let m := max mvl mvr in
                  let lt := inject_term (le_max_l mvl mvr) in
                    let rt := inject_term (le_max_r mvl mvr) in
                      (mi_of_term_arcbz lt, mi_of_term_arcbz rt).

          (** Order characteristic for symbolically computed interpretation and 
           its decidability. *)

          Notation mat_ge := (@mat_ge_arcbz dim dim).

          Definition mint_ge_arcbz n (l r : mint n) := Vforall2n
            mat_ge (args_arcbz l) (args_arcbz r) /\ (@vec_ge_arcbz
              dim) (const_arcbz l) (const_arcbz r).
          
          Definition term_ord_arcbz (ord : forall n, relation (mint
            n)) l r := let (li, ri) := rule_mi_arcbz (mkRule l r) in
          ord _ li ri.

          Variable mint_gt_arcbz : forall n (l r : mint n), Prop.
          Variable mint_gt_dec_arcbz : forall n, rel_dec (@mint_gt_arcbz n).

          Definition term_ge_arcbz := term_ord_arcbz mint_ge_arcbz.
          Definition term_gt_arcbz := term_ord_arcbz mint_gt_arcbz.

          Lemma mint_ge_dec_arcbz : forall n, rel_dec (@mint_ge_arcbz n).

          Proof.
            intros n x y. unfold mint_ge_arcbz.
            destruct (Vforall2n_dec
              (@mat_ge_dec_arcbz dim dim) (args_arcbz x) (args_arcbz y)); 
            intuition.
            destruct (vec_ge_dec_arcbz (const_arcbz x)
              (const_arcbz y)); intuition.
          Defined.

          Lemma term_ge_dec_arcbz : rel_dec term_ge_arcbz.
            
          Proof.
            intros l r. unfold term_ge_arcbz, term_ord_arcbz. simpl.
            match goal with |- {mint_ge_arcbz ?l ?r}
              + {~mint_ge_arcbz ?l ?r} => 
              destruct (mint_ge_dec_arcbz l r); auto
            end.
          Defined.

          Lemma term_gt_dec_arcbz : rel_dec term_gt_arcbz.
            
          Proof.
            intros l r. unfold term_gt_arcbz, term_ord_arcbz. simpl.
            match goal with |- {mint_gt_arcbz ?l ?r}
              + {~mint_gt_arcbz ?l ?r} => 
              destruct (mint_gt_dec_arcbz l r); auto
            end.
          Defined.

          (*REMOVE: unused: Notation IR_succ := (IR I succ).*)
          Notation IR_succeq := (IR I_arcbz succeq_arcbz).

          Definition mint_eval_arcbz (val : valuation I_arcbz) k (mi :
            mint k) : vec := let coefs := Vbuild (fun i (ip : i < k)
              => dom2vec_arcbz (val i)) in add_vectors_arcbz (Vcons
                (const_arcbz mi) (Vmap2 (@mat_vec_prod_arcbz dim dim)
                  (args_arcbz mi) coefs)).

          Add Parametric Morphism val k : (@mint_eval_arcbz val k)
            with signature (@eq_mint_arcbz k) ==> eq_vec as
              mint_eval_mor_arcbz.

          Proof.
            unfold eq_mint_arcbz. intros [c1 args1] [c2 args2]. intuition.
            unfold mint_eval_arcbz. simpl. apply add_vectors_mor_arcbz.
            rewrite (eq_vec_cons eq_vec). intuition.
            apply Vmap2_mor with (eqA := @mat_eqA_arcbz dim dim) (eqB := eq_vec).
            apply eq_vec_st. apply mat_vec_prod_mor_arcbz. hyp.
            apply eq_vec_refl. apply eq_vec_st.
          Qed.

          Lemma mint_eval_split_arcbz : forall val k (mi : mint k),
            let coefs := Vbuild (fun i (ip : i < k)
              => dom2vec_arcbz (val i)) in
            mint_eval_arcbz val mi =v const_arcbz mi [+] 
            add_vectors_arcbz (Vmap2
              (@mat_vec_prod_arcbz dim dim) (args_arcbz mi) coefs).

          Proof.
            intros. unfold mint_eval_arcbz, add_vectors_arcbz. simpl.
            rewrite vector_plus_comm_arcbz. refl.
          Qed.
          
          Hint Rewrite mat_mult_id_l_arcbz zero_matrix_mult_l_arcbz
            using simpl : arith.

          Lemma mint_eval_var_aux_arcbz : forall M i k (v : vector vec
            k) (ip : i < k), add_vectors_arcbz (Vmap2
              (@mat_vec_prod_arcbz dim dim) (Vreplace (Vconst
                (zero_matrix_arcbz dim dim) k) ip M) v) =v
            col_mat_to_vec_arcbz (M <*> (vec_to_col_mat_arcbz (Vnth v
              ip))).

          Proof.
            induction i; intros.
            destruct k. NatUtil.absurd_arith.
            unfold add_vectors_arcbz. simpl.
            fold (add_vectors_arcbz (Vmap2 (@mat_vec_prod_arcbz dim dim)
              (Vconst (zero_matrix_arcbz dim dim) k) (Vtail v))).
            assert (add_vectors_arcbz (Vmap2
              (@mat_vec_prod_arcbz dim dim) (Vconst
                (zero_matrix_arcbz dim dim) k) (Vtail v))
            =v @zero_vec_arcbz dim).
            Focus 2. rewrite H.
            rewrite vector_plus_zero_l_arcbz. unfold mat_vec_prod_arcbz.
            replace (Vhead v) with (Vnth v ip).
            refl.
            rewrite Vhead_nth.
            rewrite (NatUtil.lt_unique (Lt.lt_O_Sn k) ip). refl.
            apply add_vectors_zero_arcbz.
            apply Vforall_nth_intro. intros.
            rewrite Vnth_map2. rewrite Vnth_const.
            unfold mat_vec_prod_arcbz.
            rewrite zero_matrix_mult_l_arcbz.
            apply Vforall2n_intro. intros.
            rewrite Vnth_col_mat_arcbz.
            unfold zero_matrix_arcbz, zero_vec_arcbz.
            rewrite mat_build_elem_arcbz.
            rewrite Vnth_const. refl.
            destruct k. NatUtil.absurd_arith.
            rewrite Vreplace_tail. simpl.
            rewrite add_vectors_cons_arcbz.
            unfold mat_vec_prod_arcbz at 1.
            rewrite zero_matrix_mult_l_arcbz.
            assert (col_mat_to_vec_arcbz
              (zero_matrix_arcbz dim 1) =v zero_vec_arcbz dim).
            apply Vforall2n_intro. intros. rewrite Vnth_col_mat_arcbz.
            unfold zero_matrix_arcbz, zero_vec_arcbz.
            rewrite mat_build_elem_arcbz. rewrite Vnth_const. refl. rewrite H.
            rewrite vector_plus_zero_l_arcbz. rewrite IHi. rewrite Vnth_tail.
            rewrite (NatUtil.le_unique (Lt.lt_n_S (Lt.lt_S_n ip)) ip). refl.
          Qed.

          Lemma mint_eval_eq_term_int_var_arcbz : forall v (val :
            valuation I_arcbz) k (t_b : maxvar_le k (Var v)),
          dom2vec_arcbz (bterm_int val (inject_term t_b)) =v
          mint_eval_arcbz val (mi_of_term_arcbz (inject_term t_b)).

          Proof.
            intros. rewrite mint_eval_split_arcbz.
            change (const_arcbz (mi_of_term_arcbz
              (inject_term t_b))) with (zero_vec_arcbz dim).
            rewrite vector_plus_zero_l_arcbz.
            change (args_arcbz (mi_of_term_arcbz
              (inject_term t_b))) with (Vreplace (Vconst 
                (zero_matrix_arcbz dim dim) (S k))
              (NatUtil.le_lt_S (maxvar_var t_b)) 
              (id_matrix_arcbz dim)).
            rewrite mint_eval_var_aux_arcbz. rewrite Vbuild_nth. simpl.
            trans (col_mat_to_vec_arcbz
              (vec_to_col_mat_arcbz (dom2vec_arcbz (val v)))).
            rewrite col_mat_to_vec_idem_arcbz. refl. apply get_col_mor_arcbz.
            rewrite mat_mult_id_l_arcbz. refl. ded dim_pos. auto.
          Qed.
          
        (* REMARK: using Hint rewrite to be able to use the [autorewrite] *)
          Hint Rewrite vector_plus_zero_l_arcbz vector_plus_zero_r_arcbz
            add_vectors_cons_arcbz : arith.

          Lemma mint_eval_const_arcbz : forall val k (c : vec),
            mint_eval_arcbz (k:=k) val (mkMatrixInt_arcbz c
              (combine_matrices_arcbz Vnil)) =v c.

          Proof.
            intros. unfold mint_eval_arcbz. simpl. autorewrite with arith.
            trans (c [+] @zero_vec_arcbz dim).
            apply vector_plus_mor_arcbz. refl.
            apply add_vectors_zero_arcbz.
            apply Vforall_nth_intro. intros.
            rewrite Vnth_map2. rewrite combine_matrices_nil_arcbz.
            rewrite Vnth_const.
            unfold mat_vec_prod_arcbz.
            apply Vforall2n_intro. intros.
            rewrite Vnth_col_mat_arcbz.
            trans (get_elem_arcbz 
              (zero_matrix_arcbz dim 1) ip0 access_0).
            apply get_elem_mor_arcbz. apply zero_matrix_mult_l_arcbz.
            unfold zero_matrix_arcbz. rewrite mat_build_elem_arcbz.
            unfold zero_vec_arcbz. rewrite Vnth_const. refl.
            apply vector_plus_zero_r_arcbz.
          Qed.

          Lemma mint_eval_cons_arcbz : forall n k val c_hd c_tl a_hd 
            (a_tl : vector (vector mat k) n),
            mint_eval_arcbz val (mkMatrixInt_arcbz (c_hd [+] c_tl)
              (combine_matrices_arcbz (Vcons a_hd a_tl))) =v
            mint_eval_arcbz val (mkMatrixInt_arcbz c_hd a_hd) [+]
            mint_eval_arcbz val (mkMatrixInt_arcbz c_tl
              (combine_matrices_arcbz a_tl)).

          Proof.
            intros. unfold mint_eval_arcbz. simpl.
            set (vali := Vbuild (A := vec) 
              (fun i (_ : i < k) => dom2vec_arcbz (val i))).
            rewrite combine_matrices_cons_arcbz.
            autorewrite with arith.
            repeat rewrite <- vector_plus_assoc_arcbz.
            apply vector_plus_mor_arcbz. 
            refl. rewrite vector_plus_assoc_arcbz.
            rewrite (vector_plus_comm_arcbz _ c_tl).
            rewrite <- vector_plus_assoc_arcbz.
            apply vector_plus_mor_arcbz. refl. 
            apply add_vectors_split_arcbz. intros.
            repeat rewrite Vnth_map2. rewrite vector_plus_comm_arcbz.
            apply mat_vec_prod_distr_mat_arcbz.
          Qed.

          Lemma mint_eval_mult_factor_arcbz : forall k val M (mi :
            mint k), mint_eval_arcbz val (mat_matrixInt_prod_arcbz M
              mi) =v mat_vec_prod_arcbz M (mint_eval_arcbz val mi).

          Proof.
            unfold mint_eval_arcbz. intros. simpl.
            autorewrite with arith.
            rewrite mat_vec_prod_distr_vec_arcbz.
            apply vector_plus_mor_arcbz. refl.
            set (gen := Vbuild (A:=vec)
              (fun i (_ : i < k) => dom2vec_arcbz (val i))).
            rewrite (mat_vec_prod_distr_add_vectors_arcbz M 
              (Vmap2 (@mat_vec_prod_arcbz dim dim) (args_arcbz mi) gen)
              (Vmap2 (@mat_vec_prod_arcbz dim dim) (Vmap (mat_mult_arcbz M) 
                (args_arcbz mi)) gen)).
            refl. intros. repeat rewrite Vnth_map2. rewrite Vnth_map.
            unfold mat_vec_prod_arcbz. rewrite vec_to_col_mat_idem_arcbz.
            apply get_col_mor_arcbz. rewrite mat_mult_assoc_arcbz. refl.
          Qed.

          Lemma mint_eval_eq_bterm_int_fapp_arcbz : forall k i fi val 
            (v : vector (bterm k) i),
            let arg_eval := Vmap2 
              (@mat_matrixInt_prod_arcbz (S k)) (args_arcbz fi) 
              (Vmap (@mi_of_term_arcbz k) v) in
              mi_eval_aux_arcbz fi (Vmap 
                (fun t : bterm k => mint_eval_arcbz val 
                  (mi_of_term_arcbz t)) v) =v
              mint_eval_arcbz val (mkMatrixInt_arcbz
                (add_vectors_arcbz (Vcons (const_arcbz fi) (Vmap 
                  (@const_arcbz matrix_arcbz dim (S k)) arg_eval)))
                (combine_matrices_arcbz (Vmap 
                  (@args_arcbz matrix_arcbz dim (S k)) arg_eval))).

          Proof.
            induction i; intros.
          (* i = 0 *)
            VOtac. simpl.
            unfold mi_eval_aux_arcbz, add_vectors_arcbz.
            simpl. autorewrite with arith.
            sym. apply mint_eval_const_arcbz.
          (* i > 0 *)
            VSntac v. simpl mi_eval_aux_arcbz.
            rewrite mi_eval_cons_arcbz. 
            rewrite IHi. simpl.
            trans (@mint_eval_arcbz val (S k)
              (@mkMatrixInt_arcbz matrix_arcbz dim (S k)
                (@mat_vec_prod_arcbz dim dim
                  (@Vhead (matrix_arcbz dim dim) i
                    (@args_arcbz matrix_arcbz dim (S i) fi))
                  (@const_arcbz matrix_arcbz dim (S k)
                    (@Vhead (mint (S k)) i
                      (@Vmap (ABterm.bterm Sig k)
                        (mint (S k))
                        (@mi_of_term_arcbz k) (S i) v)))
                  [+] @add_vectors_arcbz dim (S i) (@Vcons (vector Arbz dim)
                    (@const_arcbz matrix_arcbz dim (S i) fi) i
                    (@Vmap (mint (S k)) 
                      (vector Arbz dim) (@const_arcbz matrix_arcbz dim (S k)) i
                      (@Vmap2 (matrix_arcbz dim dim)
                        (mint (S k))
                        (mint (S k))
                        (@mat_matrixInt_prod_arcbz (S k)) i
                        (@Vtail (matrix_arcbz dim dim) i
                          (@args_arcbz matrix_arcbz dim (S i) fi))
                        (@Vtail (mint (S k)) i
                          (@Vmap (ABterm.bterm Sig k)
                            (mint (S k))
                            (@mi_of_term_arcbz k) (S i) v))))))
                (@combine_matrices_arcbz (S i) (S k)
                  (@Vcons (vector (matrix_arcbz dim dim) (S k))
                    (@Vmap (matrix_arcbz dim dim) (matrix_arcbz dim dim)
                      (@mat_mult_arcbz dim dim dim
                        (@Vhead (matrix_arcbz dim dim) i
                          (@args_arcbz matrix_arcbz dim (S i) fi))) 
                      (S k)
                      (@args_arcbz matrix_arcbz dim (S k)
                        (@Vhead (mint (S k)) i
                          (@Vmap (ABterm.bterm Sig k)
                            (mint (S k))
                            (@mi_of_term_arcbz k) (S i) v)))) i
                    (@Vmap (mint (S k))
                      (vector (matrix_arcbz dim dim) (S k))
                      (@args_arcbz matrix_arcbz dim (S k)) i
                      (@Vmap2 (matrix_arcbz dim dim)
                        (mint (S k))
                        (mint (S k))
                        (@mat_matrixInt_prod_arcbz (S k)) i
                        (@Vtail (matrix_arcbz dim dim) i
                          (@args_arcbz matrix_arcbz dim (S i) fi))
                        (@Vtail (mint (S k)) i
                          (@Vmap (ABterm.bterm Sig k)
                            (mint (S k))
                            (@mi_of_term_arcbz k) (S i) v)))))))).
            Focus 2. apply mint_eval_mor_arcbz. split.
            rewrite add_vectors_perm_arcbz.
            rewrite (add_vectors_cons_arcbz (i := S i)
              (mat_vec_prod_arcbz (Vhead (args_arcbz fi))
                (const_arcbz (Vhead (Vmap (mi_of_term_arcbz (k:=k)) v))))). refl.
            apply eq_vec_refl. apply mat_eqA_st.
            rewrite mint_eval_cons_arcbz. apply vector_plus_mor_arcbz.
            Focus 2. rewrite Vmap_tail. refl.
            rewrite H. simpl.
            fold (mat_matrixInt_prod_arcbz 
              (Vhead (args_arcbz fi)) (mi_of_term_arcbz (Vhead v))).
            sym. apply mint_eval_mult_factor_arcbz.
          Qed.

          Lemma mint_eval_eq_bterm_int_arcbz : forall (val : valuation
            I_arcbz) t k (t_b : maxvar_le k t), dom2vec_arcbz
          (bterm_int val (inject_term t_b)) =v mint_eval_arcbz val
          (mi_of_term_arcbz (inject_term t_b)).

          Proof.
            intros val t. pattern t. apply term_ind_forall; intros.
            apply mint_eval_eq_term_int_var_arcbz.
            rewrite inject_term_eq. simpl.
            rewrite Vmap_map.
            rewrite (@Vmap_eqA _ _ eq_vec eq_vec_st
              (fun x => dom2vec_arcbz (bterm_int val x)) 
              (fun (t : bterm k) => mint_eval_arcbz val
                (mi_of_term_arcbz t))).
            simpl. apply mint_eval_eq_bterm_int_fapp_arcbz.
            apply Vforall_nth_intro. intros.
            rewrite inject_terms_nth. apply (Vforall_nth ip H).
          Qed.

          Lemma mint_eval_eq_term_int_arcbz : forall t (val :
            valuation I_arcbz) k (t_b : maxvar_le k t), dom2vec_arcbz
          (term_int val t) =v mint_eval_arcbz val (mi_of_term_arcbz
            (inject_term t_b)).

          Proof.
            intros. rewrite <- (term_int_eq_bterm_int val t_b).
            apply mint_eval_eq_bterm_int_arcbz.
          Qed.

          Lemma mint_eval_equiv_arcbz : forall l r (val : valuation I_arcbz),
            let (li, ri) := rule_mi_arcbz (mkRule l r) in
              let lev := term_int val l in
                let rev := term_int val r in
                  let lv := mint_eval_arcbz val li in
                    let rv := mint_eval_arcbz val ri in
                      lv =v dom2vec_arcbz lev /\ rv =v dom2vec_arcbz rev.

          Proof.
            intros. simpl. split.
            rewrite (mint_eval_eq_term_int_arcbz val (le_max_l (maxvar l) (maxvar r))).
            refl.
            rewrite (mint_eval_eq_term_int_arcbz val (le_max_r (maxvar l) (maxvar r))).
            refl.
          Qed.

          Lemma mint_eval_mon_succeq_args_arcbz : forall k (val :
            vector vec k) (mi mi' : mint k), mint_ge_arcbz mi mi' ->
          add_vectors_arcbz (Vmap2 (@mat_vec_prod_arcbz dim dim)
            (args_arcbz mi) val) >=v add_vectors_arcbz (Vmap2
              (@mat_vec_prod_arcbz dim dim) (args_arcbz mi') val).

          Proof.
            destruct mi. gen val. clear val. induction args_arcbz0. intros.
            destruct mi'. VOtac. 
            unfold mint_eval_arcbz, add_vectors_arcbz. simpl.
            apply (vec_ge_refl_arcbz (@zero_vec_arcbz dim)).
            intros. destruct mi'. VSntac args_arcbz1.
            unfold mint_eval_arcbz, add_vectors_arcbz. simpl.
            destruct H. apply (@vec_plus_ge_compat_arcbz dim).
            apply (IHargs_arcbz0 (Vtail val)
              (mkMatrixInt_arcbz const_arcbz1 (Vtail (args_arcbz1)))).
            split. simpl. change args_arcbz0 with (Vtail (Vcons h args_arcbz0)). 
            apply Vforall2n_tail. hyp. hyp.
            apply mat_vec_prod_ge_compat_arcbz.
            change h with (Vhead (Vcons h args_arcbz0)). do 2 rewrite Vhead_nth.
            apply Vforall2n_nth. hyp.
            apply (vec_ge_refl_arcbz (Vhead val)).
          Qed.

          Lemma mint_eval_mon_succeq_arcbz : forall (val : valuation
            I_arcbz) k (mi mi' : mint k), mint_ge_arcbz mi mi' ->
          mint_eval_arcbz val mi >=v mint_eval_arcbz val mi'.

          Proof.
            intros. unfold mint_eval_arcbz, add_vectors_arcbz. simpl.
            apply (@vec_plus_ge_compat_arcbz dim).
            exact (mint_eval_mon_succeq_args_arcbz _ H).
            destruct H. hyp.
          Qed.

          Lemma term_ge_incl_succeq_arcbz : term_ge_arcbz <<
            IR_succeq.

          Proof.
            intros l r lr v. destruct (mint_eval_equiv_arcbz l r v). simpl in * .
            unfold succeq_arcbz.
            rewrite <- (vec_ge_mor_arcbz H H0).
            apply mint_eval_mon_succeq_arcbz. hyp.
          Qed.

          Definition succeq_arcbz' := term_ge_arcbz.
          Definition succeq'_sub_arcbz := term_ge_incl_succeq_arcbz.
          Definition succeq'_dec_arcbz := term_ge_dec_arcbz.

        End OrderDecidability_arcbz.
      End MBI.
    End MatrixBasedInt_arcbz.
  End Arctic_int.
End S.
