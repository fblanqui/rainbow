(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-25 (setoid)
- Adam Koprowski and Johannes Waldmann, 2008-01
*)

Set Implicit Arguments.

Require Import AMonAlg2 OrdSemiRing2 ATrs LogicUtil RelUtil
  NatUtil AWFMInterpretation Max VecEq Setoid VecOrd Matrix2 VecUtil
  VecArith2.

(***********************************************************************)
(** * Matrix interpretation over domain arctic natural numbers. *)

Section MatrixLinearFunction_arcnat.
  
  Variables (matrix_arcnat : nat -> nat -> Type) (dim argCnt : nat).
  
  (** [const_arcnat] being a constant vector of the interpretation of
     size [dim] and [args_arcnat] representing coefficients for the
     arguments with a [dim x dim] matrix per argument. *)
  
  Record matrixInt_arcnat : Type := mkMatrixInt_arcnat {
    const_arcnat : vector Ar dim;
    args_arcnat : vector (matrix_arcnat dim dim) argCnt
  }.
  
End MatrixLinearFunction_arcnat.

Implicit Arguments mkMatrixInt_arcnat [matrix_arcnat dim argCnt].

Section S.
  
  Variable Sig: Signature.
  Variable dim : nat.
  Parameter dim_pos : dim > 0.

  (** Matrix based int over domain arctic naturals. *)
  
  Section Arctic_nat.
    
    Section Conf.
      
      Notation matrixInt := (matrixInt_arcnat matrix_arcnat).
      
      Record MatrixMethodConf_arcnat : Type :=
        mkMatrixMethodConf_arcnat {
          trsInt_arcnat : forall f : Sig, matrixInt dim (ASignature.arity f)
        }.
      
      Notation vec := (vector Ar dim).
      Definition vec_at0_arcnat (v : vec) := Vnth v dim_pos.
      
      Notation "x >>= y" := (ger x y) (at level 70).
      
      Definition vec_invariant_arcnat (v : vec) := vec_at0_arcnat v >>= A1r.
      
      Lemma inv_id_matrix_arcnat : vec_invariant_arcnat
        (Vreplace (Vconst A0r dim) dim_pos A1r).
      Proof.
        unfold vec_invariant_arcnat, vec_at0_arcnat.
        rewrite Vnth_replace. apply ge_reflr.
      Qed.
      
    End Conf.
    
    Section MatrixBasedInt_arcnat.
      
      Notation A := Ar.
      Notation A0 := A0r.
      Notation A1 := A1r.
      Notation eqA := eqAr.
      Notation sid_theoryA := sid_theoryAr.
      Notation ge := ger.
      Notation ge_refl := ge_reflr.
      Notation ge_trans := ge_transr.
      
      (* Define Morphism [vector_plus_mor] to be able to use [rewrite]
         at the Lemma [mint_eval_var_aux] later. *)

      Add Parametric Morphism n : (@vector_plus_arcnat n)
        with signature (@eq_vec_arcnat n)
          ==> (@eq_vec_arcnat n) ==> (@eq_vec_arcnat n)
          as vector_plus_mor_arcnat.
      Proof.
        intros. apply Vforall2n_intro. intros. unfold vector_plus_arcnat.
        repeat rewrite Vnth_map2.
        (*FIXME: rewrite H does not work even if Vnth is declared as morphism *)
        apply Aplus_morr; apply (Vnth_mor eqAr); hyp.
      Qed.

      (* Add new setoid to be able to use [sym] at [eqA] use later in
      some lemma. *)

      Add Setoid A eqA sid_theoryA as A_Setoid_arcnat.
      
      (* Define [ge] relation to be able to use [trans] for morphism
      of [vec_ge_mor]. *)

      Add Relation A ge 
      reflexivity proved by ge_refl
      transitivity proved by ge_trans
        as ge_rel_arcnat.

      (* Define morphism to be able to rewrite [vec_ge_mor] later. *)

      Add Parametric Morphism n : (@vec_ge_arcnat n)
        with signature (@eq_vec_arcnat n)
          ==> (@eq_vec_arcnat n) ==> iff
          as vec_ge_mor_arcnatarcnat.

      Proof.
        unfold vec_ge_arcnat. intros.
        apply (Vforall2n_mor sid_theoryAr). intuition.
        trans a1. apply eq_ge_compatr. sym. hyp.
        trans a2. hyp. apply eq_ge_compatr. hyp.
        trans a1'. apply eq_ge_compatr. hyp.
        trans a2'. hyp. apply eq_ge_compatr. sym. hyp.
        hyp. hyp.
      Qed.
      
      Implicit Arguments vec_ge_mor_arcnat [n x y x0 y0].

      (* Define this relation on [vec_eq] to be able to use
         [symm], etc. *)
      
      Add Parametric Relation n : (vector Ar n) (@eq_vec_arcnat n)
        reflexivity proved by (@eq_vec_refl A eqA sid_theoryA n)
        symmetry proved by (@eq_vec_sym A eqA sid_theoryA n)
          transitivity proved by (@eq_vec_trans A eqA sid_theoryA n) as
            eq_vec_rel_arcnat.

      (* Add these relations and morphisms to be able to use it rewriting
         and [trans], etc later for matrix.
         Add [mat_eqA] to be able to use rewrite [mat_mult_id_l]. *)
      
      Add Parametric Relation m n : (matrix_arcnat m n) (@mat_eqA_arcnat m n)
        reflexivity proved by (@mat_eqA_refl_arcnat m n)
        symmetry proved by (@mat_eqA_sym_arcnat m n)
          transitivity proved by (@mat_eqA_trans_arcnat m n)
            as mat_eqA_rel_arcnat.

      (* Define this morphism to be able to use rewrite
         [zero_matrix_mult_l]. *)

      Add Parametric Morphism m n i (h:i<n) :
        (fun M => @get_col_arcnat m n M i h)
        with signature (@mat_eqA_arcnat m n) ==> (@eq_vec_arcnat m)
          as get_col_mor_arcnat.

      Proof.
        intros. unfold eq_vec_arcnat. apply Vforall2n_intro. intros.
        repeat rewrite <- get_elem_swap_arcnat. apply H.
      Qed.
      
      (* Define this morphism to be able to use [rewrite H0] in
         [mat_vec_prod_mor]. *)

      Add Parametric Morphism n : (@vec_to_col_mat_arcnat n) with
        signature (@eq_vec_arcnat n) ==> (@mat_eqA_arcnat n 1) as
          vec_to_col_mat_mor_arcnat.
        
      Proof.
        unfold vec_to_col_mat_arcnat, mat_eqA_arcnat,
          get_elem_arcnat. intros.  repeat rewrite
        get_elem_swap_arcnat. unfold get_col_arcnat.  repeat rewrite
          Vnth_map.  apply (Vnth_mor eqA). rewrite (eq_vec_cons
        eqA). intuition.  apply (Vnth_mor eqA). hyp.
        Qed.
        
      (* Define this morphism to be able to use [rewrite H] for
      [mat_vec_prod_mor]. *)

        Add Parametric Morphism m n p : (@mat_mult_arcnat m n p) with
          signature (@mat_eqA_arcnat m n) ==> (@mat_eqA_arcnat n p) ==>
          (@mat_eqA_arcnat m p) as mat_mult_mor_arcnat.
          
        Proof.
          unfold mat_mult_arcnat. intros. unfold mat_eqA_arcnat. intros.
          repeat rewrite mat_build_elem_arcnat. apply dot_product_mor_arcnat.
          apply get_row_mor_arcnat. hyp. apply get_col_mor_arcnat. hyp.
        Qed.
        
      (* Define this morphism to be able to rewrite
      [mat_vec_prod_distr_vec] later. *)
        
        Add Parametric Morphism m n : (@mat_vec_prod_arcnat m n) with
          signature (@mat_eqA_arcnat m n) ==> (@eq_vec_arcnat n) ==>
          (@eq_vec_arcnat m) as mat_vec_prod_mor_arcnat.

        Proof.
          unfold mat_vec_prod_arcnat. intros. apply
          get_col_mor_arcnat. rewrite H. rewrite H0. refl.
        Qed.
        
      (* Adding notations *)
        
        Notation vec := (vector Ar dim).
        Notation eq_vec_st := (@eq_vec_st _ _ sid_theoryAr dim).
        Notation mat_eqA := (@mat_eqA_arcnat dim dim).
        Notation mat_eqA_st := (@mat_eqA_st_arcnat dim dim). 
        Notation matrixInt := (matrixInt_arcnat matrix_arcnat).
        Notation mint := (matrixInt dim).
        Notation mat := (matrix_arcnat dim dim).
        Notation eq_vec_st' := (@eq_vec_st _ _ sid_theoryAr dim).
        Notation eq_vec_mat_eqA_st' := (@VecEq.eq_vec_st _ _ mat_eqA_st).
        Notation eq_vec := (@eq_vec_arcnat dim).
        Notation "x =v y" := (eq_vec x y)(at level 70).
        Notation "x >>= y" := (ger x y) (at level 70).
        
        Infix "[+]" := vector_plus_arcnat (at level 50).
        Infix "<*>" := mat_mult_arcnat (at level 40).
        
        Add Parametric Relation k : (vector vec k) (@VecEq.eq_vec _
          eq_vec k) reflexivity proved by (@eq_vec_refl _ _ eq_vec_st k)
        symmetry proved by (@eq_vec_sym _ _ eq_vec_st k) transitivity
          proved by (@eq_vec_trans _ _ eq_vec_st k) as
            eq_vec_eq_vec_rel_arcnat.
        
        Add Parametric Relation k : (vector (matrix_arcnat dim dim) k)
          (@VecEq.eq_vec _ mat_eqA k) reflexivity proved by
          (@eq_vec_refl _ _ mat_eqA_st k) symmetry proved by
            (@eq_vec_sym _ _ mat_eqA_st k) transitivity proved by
              (@eq_vec_trans _ _ mat_eqA_st k) as eq_vec_mat_eqA_rel_arcnat.
        
        Definition eq_mint_arcnat k (mi1 mi2 : mint k) :=
          let (c1, args1) := mi1 in
            let (c2, args2) := mi2 in
              c1 =v c2 /\ VecEq.eq_vec mat_eqA args1 args2.
        
        Notation "x =i y" := (eq_mint_arcnat x y) (at level 70).
        
        Lemma eq_mint_refl_arcnat : forall k (x : mint k), x =i x.
          
        Proof.
          unfold eq_mint_arcnat. destruct x. intuition.
        Qed.
        
        Lemma eq_mint_sym_arcnat : forall k (x y : mint k), x =i y -> y
          =i x.
          
        Proof.
          unfold eq_mint_arcnat. destruct x. destruct y. intuition.
        Qed.
        
        Lemma eq_mint_trans_arcnat : forall k (x y z : mint k), x =i y
          -> y =i z -> x =i z.
          
        Proof.
          unfold eq_mint_arcnat. destruct x. destruct y. destruct
          z. intuition. trans const_arcnat1; hyp. trans args_arcnat1;
          hyp.
        Qed.
        
        Add Parametric Relation k : (@mint k) (@eq_mint_arcnat k)
          reflexivity proved by (@eq_mint_refl_arcnat k) symmetry proved
            by (@eq_mint_sym_arcnat k) transitivity proved by
              (@eq_mint_trans_arcnat k) as eq_mint_rel_arcnat.
        
        Add Parametric Morphism k : (@mkMatrixInt_arcnat matrix_arcnat
          dim k) with signature eq_vec ==> (@VecEq.eq_vec _ mat_eqA k)
        ==> (@eq_mint_arcnat k) as mkMatrixInt_mor_arcnat.
          
        Proof.
          unfold eq_mint_arcnat. auto.
        Qed.
        
        Add Parametric Morphism k : (@const_arcnat matrix_arcnat dim k)
          with signature (@eq_mint_arcnat k) ==> eq_vec as
            const_mor_arcnat.
          
        Proof.
          destruct x. destruct y. simpl. intuition.
        Qed.
        
        Add Parametric Morphism k : (@args_arcnat matrix_arcnat dim k)
          with signature (@eq_mint_arcnat k) ==> (@VecEq.eq_vec _
            mat_eqA k) as args_mor_arcnat.
          
        Proof.
          destruct x. destruct y. simpl. intuition.
        Qed.
        
        Section MBI.

          Definition dom_arcnat := { v : vec | vec_invariant_arcnat v }.
          
          Definition dom2vec_arcnat (d : dom_arcnat) : vec := proj1_sig d.
          
          Definition add_matrices_arcnat i m n (v : vector
            (matrix_arcnat m n) i) := Vfold_left (@mat_plus_arcnat m n)
          (zero_matrix_arcnat m n) v.

          Definition mi_eval_aux_arcnat n (mi : mint n) (v : vector vec
            n) : vec := add_vectors_arcnat (n:=dim) (k:=n)(Vmap2
              (@mat_vec_prod_arcnat dim dim) (args_arcnat mi) v) [+]
            const_arcnat mi.
          
          Add Parametric Morphism n : (@mi_eval_aux_arcnat n) with
            signature (@eq_mint_arcnat n) ==> (@VecEq.eq_vec _ eq_vec n)
            ==> eq_vec as mi_eval_aux_mor_arcnat.
            
          Proof.
            unfold mi_eval_aux_arcnat. intuition. apply vector_plus_mor_arcnat.
            apply add_vectors_mor_arcnat.
            apply Vforall2n_intro. intros. repeat rewrite Vnth_map2.
            apply mat_vec_prod_mor_arcnat.
            apply (Vnth_mor mat_eqA). rewrite H. refl. apply (Vnth_mor eq_vec). hyp.
            rewrite H. refl.
          Qed.
          
          Variable ma : MatrixMethodConf_arcnat.
          
          Variable mi_eval_ok : forall f v, vec_invariant_arcnat
            (mi_eval_aux_arcnat (trsInt_arcnat ma f) (Vmap
              dom2vec_arcnat v)).
          
          Definition mi_eval_arcnat f (v : vector dom_arcnat
            (ASignature.arity f)) : dom_arcnat := exist (fun v =>
              vec_invariant_arcnat v) (mi_eval_aux_arcnat (trsInt_arcnat
                ma f) (Vmap dom2vec_arcnat v)) (mi_eval_ok f v).
          
          Lemma mi_eval_cons_arcnat : forall n (mi : mint (S n)) v vs,
            mi_eval_aux_arcnat mi (Vcons v vs) =v mat_vec_prod_arcnat
            (Vhead (args_arcnat mi)) v [+] mi_eval_aux_arcnat
            (mkMatrixInt_arcnat (const_arcnat mi) (Vtail (args_arcnat
              mi))) vs.
            
          Proof.
            intros. unfold mi_eval_aux_arcnat. simpl. rewrite
            vector_plus_assoc_arcnat.
            apply vector_plus_mor_arcnat.
            apply vector_plus_comm_arcnat. refl.
          Qed.
          
          Definition dom_zero_arcnat: dom_arcnat.
          
          Proof.
            exists (Vreplace (Vconst A0r dim) dim_pos A1r).
            apply inv_id_matrix_arcnat.
          Defined.
          
          Definition I_arcnat := @mkInterpretation Sig dom_arcnat
            dom_zero_arcnat mi_eval_arcnat.
          
          Infix ">=v" := vec_ge_arcnat (at level 70).
          
          Definition succeq_arcnat (x y : dom_arcnat) := (dom2vec_arcnat
            x) >=v (dom2vec_arcnat y).
          
          Lemma refl_succeq_arcnat : reflexive succeq_arcnat.
            
          Proof.
            intro x. apply vec_ge_refl_arcnat.
          Qed.
          
          Lemma trans_succeq_arcnat : transitive succeq_arcnat.
            
          Proof.
            unfold succeq_arcnat. apply Rof_trans with
            (f:=dom2vec_arcnat). apply vec_ge_trans_arcnat.
          Qed.
          
        (** Monotonicity *)
          
          Section VecMonotonicity_arcnat.
            
            Variable f : matrix_arcnat dim dim -> vec -> vec.
            Variable f_mon : forall M v1 v2, v1 >=v v2 -> f M v1 >=v f M v2.
            Variables (a b : vec).
            
            Lemma vec_add_weak_monotone_map2_arcnat : forall n1 (v1 :
              vector vec n1) n2 (v2 : vector vec n2) n (M : vector
                (matrix_arcnat dim dim) n) i_j, a >=v b ->
              add_vectors_arcnat (Vmap2 f M (Vcast (Vapp v1 (Vcons a
                v2)) i_j)) >=v add_vectors_arcnat (Vmap2 f M (Vcast (Vapp
                  v1 (Vcons b v2)) i_j)).
              
            Proof.
              induction v1; intros; simpl.
              destruct n; try solve [NatUtil.absurd_arith].
              unfold add_vectors_arcnat, succeq_arcnat, vec_ge_arcnat.
              simpl. apply Vforall2n_intro. 
              intros. unfold vector_plus_arcnat. do 2 rewrite Vnth_map2.
              assert (Vnth (f (Vhead M) a) ip >>= Vnth (f (Vhead M) b) ip).
              apply Vforall2n_nth. apply f_mon. hyp.
              apply plus_ge_compat_arcnat. apply ge_reflr. hyp.
              destruct n0; try solve [NatUtil.absurd_arith].
              unfold add_vectors_arcnat, succeq_arcnat, vec_ge_arcnat.
              simpl. apply Vforall2n_intro. 
              intros. unfold vector_plus_arcnat. do 2 rewrite Vnth_map2.
              apply plus_ge_compat_arcnat. 
              apply Vforall2n_nth. unfold add_vectors_arcnat in IHv1. apply IHv1.
              hyp. apply ge_reflr.
            Qed.
            
          End VecMonotonicity_arcnat.
          
          Lemma monotone_succeq_arcnat : monotone I_arcnat succeq_arcnat.
            
          Proof.
            intros f i j i_j vi vj a b ab.
            simpl. unfold mi_eval_arcnat,
            mi_eval_aux_arcnat, succeq_arcnat. simpl.
            apply (@vec_plus_ge_compat_r_arcnat dim).
            do 2 rewrite Vmap_cast. do 2 rewrite Vmap_app. simpl.
            apply vec_add_weak_monotone_map2_arcnat; trivial.
            intros. unfold succeq_arcnat, vec_ge_arcnat.
            apply Vforall2n_intro. intros.
            unfold mat_vec_prod_arcnat. 
            do 2 rewrite Vnth_col_mat_arcnat. apply mat_mult_mon_arcnat.
            apply mat_ge_refl_arcnat. intros x y xp yp.
            do 2 rewrite vec_to_col_mat_spec_arcnat.
            apply Vforall2n_nth. hyp.
          Qed.
          
          Lemma succeq_dec_arcnat : rel_dec succeq_arcnat.
            
          Proof.
            intros x y. unfold succeq_arcnat, vec_ge_arcnat.
            apply Vforall2n_dec.
            intros m1 n. apply ge_decr.
          Defined.
          
        (** Decidability of order on terms induced by matrix interpretations. *)

          Section OrderDecidability_arcnat.
            
            Require Import ABterm.
            
            Notation bterm := (bterm Sig).
            
          (** Symbolic computation of term interpretation. *)
            
            Definition mat_matrixInt_prod_arcnat n M (mi : mint n) :
              mint n := mkMatrixInt_arcnat (mat_vec_prod_arcnat M
                (const_arcnat mi)) (Vmap (mat_mult_arcnat M) (args_arcnat
                  mi)).
            
            Definition combine_matrices_arcnat n k (v : vector (vector
              mat k) n) := Vbuild (fun i ip => add_matrices_arcnat (Vmap
                (fun v => Vnth v ip) v)).
            
            Lemma combine_matrices_nil_arcnat : forall i,
              combine_matrices_arcnat Vnil = Vconst (@zero_matrix_arcnat
                dim dim) i.
              
            Proof.
              intros. apply Veq_nth. intros. unfold combine_matrices_arcnat.
              rewrite Vnth_const. rewrite Vbuild_nth. trivial.
            Qed.
            
            Lemma combine_matrices_cons_arcnat : forall k n v (vs :
              vector (vector mat k) n), combine_matrices_arcnat (Vcons v
                vs) = Vmap2 (@mat_plus_arcnat _ _)
              (combine_matrices_arcnat vs) v.
              
            Proof.
              intros. apply Veq_nth. intros.
              unfold combine_matrices_arcnat, add_matrices_arcnat. simpl.
              rewrite Vnth_map2. do 2 rewrite Vbuild_nth. refl.
            Qed.
            
            Fixpoint mi_of_term_arcnat k (t : bterm k) : mint (S k) :=
              match t with
                | BVar i ip => 
                  let zero_int := Vconst (zero_matrix_arcnat dim dim) (S k) in
                    let args_int := Vreplace zero_int (le_lt_S ip) (id_matrix_arcnat dim) in
                      mkMatrixInt_arcnat (@zero_vec_arcnat dim) args_int
                | BFun f v => 
                  let f_int := trsInt_arcnat ma f in
                    let args_int := Vmap (@mi_of_term_arcnat k) v in
                      let args_int' := Vmap2 (@mat_matrixInt_prod_arcnat (S k)) 
                        (args_arcnat f_int) args_int in
                        let res_const := add_vectors_arcnat (Vcons (const_arcnat f_int) 
                          (Vmap (@const_arcnat matrix_arcnat dim (S k)) args_int')) in
                        let res_args := combine_matrices_arcnat
                          (Vmap (@args_arcnat matrix_arcnat dim (S k)) 
                            args_int') in
                          mkMatrixInt_arcnat res_const res_args
              end.
            
            Require Import ATrs.
            
            Definition rule_mi_arcnat r :=
              let mvl := maxvar (lhs r) in
                let mvr := maxvar (rhs r) in
                  let m := max mvl mvr in
                    let lt := inject_term (le_max_l mvl mvr) in
                      let rt := inject_term (le_max_r mvl mvr) in
                        (mi_of_term_arcnat lt, mi_of_term_arcnat rt).

          (** Order characteristic for symbolically computed
             interpretation and its decidability. *)

            Notation mat_ge := (@mat_ge_arcnat dim dim).
            
            Definition mint_ge_arcnat n (l r : mint n) := Vforall2n
              mat_ge (args_arcnat l) (args_arcnat r) /\ (@vec_ge_arcnat
                dim) (const_arcnat l) (const_arcnat r).
            
            Definition term_ord_arcnat (ord : forall n, relation (mint
              n)) l r := let (li, ri) := rule_mi_arcnat (mkRule l r) in
            ord _ li ri.
            
            Variable mint_gt_arcnat : forall n (l r : mint n), Prop.
            Variable mint_gt_dec_arcnat : forall n, rel_dec
              (@mint_gt_arcnat n).
            
            Definition term_ge_arcnat := term_ord_arcnat mint_ge_arcnat.
            Definition term_gt_arcnat := term_ord_arcnat mint_gt_arcnat.
            
            Lemma mint_ge_dec_arcnat : forall n, rel_dec (@mint_ge_arcnat n).
              
            Proof.
              intros n x y. unfold mint_ge_arcnat. destruct
              (Vforall2n_dec (@mat_ge_dec_arcnat dim dim) (args_arcnat
                x) (args_arcnat y)); intuition.  destruct
              (vec_ge_dec_arcnat (const_arcnat x) (const_arcnat y));
              intuition.
              Defined.
              
              Lemma term_ge_dec_arcnat : rel_dec term_ge_arcnat.
                
              Proof.
                intros l r. unfold term_ge_arcnat, term_ord_arcnat. simpl.
                match goal with |- {mint_ge_arcnat ?l ?r} + {~mint_ge_arcnat ?l ?r} => 
                  destruct (mint_ge_dec_arcnat l r); auto
                end.
              Defined.
              
              Lemma term_gt_dec_arcnat : rel_dec term_gt_arcnat.
                
              Proof.
                intros l r. unfold term_gt_arcnat, term_ord_arcnat. simpl.
                match goal with |- {mint_gt_arcnat ?l ?r} +
                  {~mint_gt_arcnat ?l ?r} => destruct (mint_gt_dec_arcnat l
                    r); auto end.
              Defined.

              Notation IR_succeq := (IR I_arcnat succeq_arcnat).
              
              Definition mint_eval_arcnat (val : valuation I_arcnat) k (mi
                : mint k) : vec := let coefs := Vbuild (fun i (ip : i < k)
                  => dom2vec_arcnat (val i)) in add_vectors_arcnat (Vcons
                    (const_arcnat mi) (Vmap2 (@mat_vec_prod_arcnat dim dim)
                      (args_arcnat mi) coefs)).
              
              Add Parametric Morphism val k : (@mint_eval_arcnat val k)
                with signature (@eq_mint_arcnat k) ==> eq_vec as
                  mint_eval_mor_arcnat.
                
              Proof.
                unfold eq_mint_arcnat. intros [c1 args1] [c2 args2]. intuition.
                unfold mint_eval_arcnat. simpl. apply add_vectors_mor_arcnat.
                rewrite (eq_vec_cons eq_vec). intuition.
                apply Vmap2_mor with (eqA := @mat_eqA_arcnat dim dim) (eqB := eq_vec).
                apply eq_vec_st. apply mat_vec_prod_mor_arcnat. hyp.
                apply eq_vec_refl. apply eq_vec_st.
              Qed.
              
              Lemma mint_eval_split_arcnat : forall val k (mi : mint k),
                let coefs := Vbuild (fun i (ip : i < k) => dom2vec_arcnat
                  (val i)) in mint_eval_arcnat val mi =v const_arcnat mi [+]
                add_vectors_arcnat (Vmap2 (@mat_vec_prod_arcnat dim dim)
                  (args_arcnat mi) coefs).

              Proof.
                intros. unfold mint_eval_arcnat, add_vectors_arcnat. simpl.
                rewrite vector_plus_comm_arcnat. refl.
              Qed.
              
              Hint Rewrite mat_mult_id_l_arcnat zero_matrix_mult_l_arcnat
                using simpl : arith.
              
              Lemma mint_eval_var_aux_arcnat : forall M i k (v : vector
                vec k) (ip : i < k), add_vectors_arcnat (Vmap2
                  (@mat_vec_prod_arcnat dim dim) (Vreplace (Vconst
                    (zero_matrix_arcnat dim dim) k) ip M) v) =v
                col_mat_to_vec_arcnat (M <*> (vec_to_col_mat_arcnat (Vnth
                  v ip))).
                
              Proof.
                induction i; intros.
                destruct k. NatUtil.absurd_arith.
                unfold add_vectors_arcnat. simpl.
                fold (add_vectors_arcnat
                  (Vmap2 (@mat_vec_prod_arcnat dim dim)
                    (Vconst (zero_matrix_arcnat dim dim) k) (Vtail v))).
                assert (add_vectors_arcnat
                  (Vmap2 (@mat_vec_prod_arcnat dim dim) (Vconst
                    (zero_matrix_arcnat dim dim) k) (Vtail v))
                  =v @zero_vec_arcnat dim).
                Focus 2. rewrite H.
                rewrite vector_plus_zero_l_arcnat.
                unfold mat_vec_prod_arcnat.
                replace (Vhead v) with (Vnth v ip).
                refl.
                rewrite Vhead_nth.
                rewrite (NatUtil.lt_unique (Lt.lt_O_Sn k) ip). refl.
                apply add_vectors_zero_arcnat.
                apply Vforall_nth_intro. intros.
                rewrite Vnth_map2. rewrite Vnth_const.
                unfold mat_vec_prod_arcnat.
                rewrite zero_matrix_mult_l_arcnat.
                apply Vforall2n_intro. intros.
                rewrite Vnth_col_mat_arcnat.
                unfold zero_matrix_arcnat, zero_vec_arcnat.
                rewrite mat_build_elem_arcnat.
                rewrite Vnth_const. refl.
                destruct k. NatUtil.absurd_arith.
                rewrite Vreplace_tail. simpl.
                rewrite add_vectors_cons_arcnat.
                unfold mat_vec_prod_arcnat at 1.
                rewrite zero_matrix_mult_l_arcnat.
                assert (col_mat_to_vec_arcnat
                  (zero_matrix_arcnat dim 1) =v zero_vec_arcnat dim).
                apply Vforall2n_intro. intros.
                rewrite Vnth_col_mat_arcnat.
                unfold zero_matrix_arcnat, zero_vec_arcnat.
                rewrite mat_build_elem_arcnat.
                rewrite Vnth_const. refl. rewrite H.
                rewrite vector_plus_zero_l_arcnat.
                rewrite IHi. rewrite Vnth_tail.
                rewrite (NatUtil.le_unique (Lt.lt_n_S (Lt.lt_S_n ip)) ip). refl.
              Qed.

              Lemma mint_eval_eq_term_int_var_arcnat : forall v (val :
                valuation I_arcnat) k (t_b : maxvar_le k (Var v)),
              dom2vec_arcnat (bterm_int val (inject_term t_b)) =v
              mint_eval_arcnat val (mi_of_term_arcnat (inject_term
                t_b)).

              Proof.
                intros. rewrite mint_eval_split_arcnat.
                change (const_arcnat (mi_of_term_arcnat
                  (inject_term t_b))) with (zero_vec_arcnat dim).
                rewrite vector_plus_zero_l_arcnat.
                change (args_arcnat (mi_of_term_arcnat
                  (inject_term t_b))) with (Vreplace (Vconst 
                    (zero_matrix_arcnat dim dim) (S k))
                  (NatUtil.le_lt_S (maxvar_var t_b)) 
                  (id_matrix_arcnat dim)).
                rewrite mint_eval_var_aux_arcnat.
                rewrite Vbuild_nth. simpl.
                trans (col_mat_to_vec_arcnat
                  (vec_to_col_mat_arcnat (dom2vec_arcnat (val v)))).
                rewrite col_mat_to_vec_idem_arcnat.
                refl. apply get_col_mor_arcnat.
                rewrite mat_mult_id_l_arcnat. refl.
                ded dim_pos. auto.
              Qed.

              Hint Rewrite vector_plus_zero_l_arcnat
                vector_plus_zero_r_arcnat add_vectors_cons_arcnat : arith.

              Lemma mint_eval_const_arcnat : forall val k (c : vec),
                mint_eval_arcnat (k:=k) val (mkMatrixInt_arcnat c
                  (combine_matrices_arcnat Vnil)) =v c.

              Proof.
                intros. unfold mint_eval_arcnat. simpl. autorewrite with arith.
                trans (c [+] @zero_vec_arcnat dim).
                apply vector_plus_mor_arcnat. refl.
                apply add_vectors_zero_arcnat.
                apply Vforall_nth_intro. intros.
                rewrite Vnth_map2. 
                rewrite combine_matrices_nil_arcnat. rewrite Vnth_const.
                unfold mat_vec_prod_arcnat. 
                apply Vforall2n_intro. intros.
                rewrite Vnth_col_mat_arcnat.
                trans (get_elem_arcnat (zero_matrix_arcnat dim 1) ip0 access_0).
                apply get_elem_mor_arcnat.
                apply zero_matrix_mult_l_arcnat.
                unfold zero_matrix_arcnat. 
                rewrite mat_build_elem_arcnat.
                unfold zero_vec_arcnat. rewrite Vnth_const. refl.
                apply vector_plus_zero_r_arcnat.
              Qed.

              Lemma mint_eval_cons_arcnat : forall n k val c_hd c_tl a_hd
                (a_tl : vector (vector mat k) n), mint_eval_arcnat val
                (mkMatrixInt_arcnat (c_hd [+] c_tl)
                  (combine_matrices_arcnat (Vcons a_hd a_tl))) =v
                mint_eval_arcnat val (mkMatrixInt_arcnat c_hd a_hd) [+]
                mint_eval_arcnat val (mkMatrixInt_arcnat c_tl
                  (combine_matrices_arcnat a_tl)).

              Proof.
                intros. unfold mint_eval_arcnat. simpl.
                set (vali := Vbuild (A := vec)
                  (fun i (_ : i < k) => dom2vec_arcnat (val i))).
                rewrite combine_matrices_cons_arcnat.
                autorewrite with arith.
                repeat rewrite <- vector_plus_assoc_arcnat.
                apply vector_plus_mor_arcnat. refl.
                rewrite vector_plus_assoc_arcnat.
                rewrite (vector_plus_comm_arcnat _ c_tl).
                rewrite <- vector_plus_assoc_arcnat.
                apply vector_plus_mor_arcnat. refl.
                apply add_vectors_split_arcnat. intros.
                repeat rewrite Vnth_map2. rewrite vector_plus_comm_arcnat.
                apply mat_vec_prod_distr_mat_arcnat.
              Qed.

              Lemma mint_eval_mult_factor_arcnat : forall k val M (mi :
                mint k), mint_eval_arcnat val (mat_matrixInt_prod_arcnat M
                  mi) =v mat_vec_prod_arcnat M (mint_eval_arcnat val mi).

              Proof.
                unfold mint_eval_arcnat. intros. simpl.
                autorewrite with arith.
                rewrite mat_vec_prod_distr_vec_arcnat.
                apply vector_plus_mor_arcnat. refl.
                set (gen := Vbuild (A:=vec)
                  (fun i (_ : i < k) => dom2vec_arcnat (val i))).
                rewrite (mat_vec_prod_distr_add_vectors_arcnat M 
                  (Vmap2 (@mat_vec_prod_arcnat dim dim) (args_arcnat mi) gen)
                  (Vmap2 (@mat_vec_prod_arcnat dim dim) (Vmap (mat_mult_arcnat M) 
                    (args_arcnat mi)) gen)).
                refl. intros. repeat rewrite Vnth_map2. rewrite Vnth_map.
                unfold mat_vec_prod_arcnat. rewrite vec_to_col_mat_idem_arcnat.
                apply get_col_mor_arcnat. rewrite mat_mult_assoc_arcnat. refl.
              Qed.

              Lemma mint_eval_eq_bterm_int_fapp_arcnat : forall k i fi val 
                (v : vector (bterm k) i),
                let arg_eval := Vmap2
                  (@mat_matrixInt_prod_arcnat (S k)) (args_arcnat fi) 
                  (Vmap (@mi_of_term_arcnat k) v) in
                  mi_eval_aux_arcnat fi (Vmap 
                    (fun t : bterm k =>
                      mint_eval_arcnat val (mi_of_term_arcnat t)) v) =v
                  mint_eval_arcnat val (mkMatrixInt_arcnat
                    (add_vectors_arcnat (Vcons (const_arcnat fi) (Vmap 
                      (@const_arcnat matrix_arcnat dim (S k)) arg_eval)))
                    (combine_matrices_arcnat (Vmap
                      (@args_arcnat matrix_arcnat dim (S k)) arg_eval))).

              Proof.
                induction i; intros.
                (* i = 0 *)
                VOtac. simpl.
                unfold mi_eval_aux_arcnat, add_vectors_arcnat.
                simpl. autorewrite with arith.
                sym. apply mint_eval_const_arcnat.
                (* i > 0 *)
                VSntac v. simpl mi_eval_aux_arcnat.
                rewrite mi_eval_cons_arcnat. 
                rewrite IHi. simpl.
                trans (@mint_eval_arcnat val (S k)
                  (@mkMatrixInt_arcnat matrix_arcnat dim (S k)
                    (@mat_vec_prod_arcnat dim dim
                      (@Vhead (matrix_arcnat dim dim) i
                        (@args_arcnat matrix_arcnat dim (S i) fi))
                      (@const_arcnat matrix_arcnat dim (S k)
                        (@Vhead (mint (S k)) i
                          (@Vmap (ABterm.bterm Sig k)
                            (mint (S k))
                            (@mi_of_term_arcnat k) (S i) v)))
                      [+] @add_vectors_arcnat dim (S i) (@Vcons (vector Ar dim)
                        (@const_arcnat matrix_arcnat dim (S i) fi) i
                        (@Vmap (mint (S k)) 
                          (vector Ar dim) (@const_arcnat matrix_arcnat dim (S k)) i
                          (@Vmap2 (matrix_arcnat dim dim)
                            (mint (S k))
                            (mint (S k))
                            (@mat_matrixInt_prod_arcnat (S k)) i
                            (@Vtail (matrix_arcnat dim dim) i
                              (@args_arcnat matrix_arcnat dim (S i) fi))
                            (@Vtail (mint (S k)) i
                              (@Vmap (ABterm.bterm Sig k)
                                (mint (S k))
                                (@mi_of_term_arcnat k) (S i) v))))))
                    (@combine_matrices_arcnat (S i) (S k)
                      (@Vcons (vector (matrix_arcnat dim dim) (S k))
                        (@Vmap (matrix_arcnat dim dim) (matrix_arcnat dim dim)
                          (@mat_mult_arcnat dim dim dim
                            (@Vhead (matrix_arcnat dim dim) i
                              (@args_arcnat matrix_arcnat dim (S i) fi))) 
                          (S k)
                          (@args_arcnat matrix_arcnat dim (S k)
                            (@Vhead (mint (S k)) i
                              (@Vmap (ABterm.bterm Sig k)
                                (mint (S k))
                                (@mi_of_term_arcnat k) (S i) v)))) i
                        (@Vmap (mint (S k))
                          (vector (matrix_arcnat dim dim) (S k))
                          (@args_arcnat matrix_arcnat dim (S k)) i
                          (@Vmap2 (matrix_arcnat dim dim)
                            (mint (S k))
                            (mint (S k))
                            (@mat_matrixInt_prod_arcnat (S k)) i
                            (@Vtail (matrix_arcnat dim dim) i
                              (@args_arcnat matrix_arcnat dim (S i) fi))
                            (@Vtail (mint (S k)) i
                              (@Vmap (ABterm.bterm Sig k)
                                (mint (S k))
                                (@mi_of_term_arcnat k) (S i) v)))))))).
                Focus 2. apply mint_eval_mor_arcnat. split.
                rewrite add_vectors_perm_arcnat.
                rewrite (add_vectors_cons_arcnat (i := S i)
                  (mat_vec_prod_arcnat (Vhead (args_arcnat fi))
                    (const_arcnat (Vhead (Vmap (mi_of_term_arcnat (k:=k)) v))))). refl.
                apply eq_vec_refl. apply mat_eqA_st.
                rewrite mint_eval_cons_arcnat. apply vector_plus_mor_arcnat.
                Focus 2. rewrite Vmap_tail. refl.
                rewrite H. simpl.
                fold (mat_matrixInt_prod_arcnat
                  (Vhead (args_arcnat fi)) (mi_of_term_arcnat (Vhead v))).
                sym. apply mint_eval_mult_factor_arcnat.
              Qed.

              Lemma mint_eval_eq_bterm_int_arcnat : forall (val :
                valuation I_arcnat) t k (t_b : maxvar_le k t),
              dom2vec_arcnat (bterm_int val (inject_term t_b)) =v
              mint_eval_arcnat val (mi_of_term_arcnat (inject_term
                t_b)).

              Proof.
                intros val t. pattern t. apply term_ind_forall; intros.
                apply mint_eval_eq_term_int_var_arcnat.
                rewrite inject_term_eq. simpl.
                rewrite Vmap_map.
                rewrite (@Vmap_eqA _ _ eq_vec eq_vec_st
                  (fun x => dom2vec_arcnat (bterm_int val x)) 
                  (fun (t : bterm k) =>
                    mint_eval_arcnat val (mi_of_term_arcnat t))).
                simpl. apply mint_eval_eq_bterm_int_fapp_arcnat.
                apply Vforall_nth_intro. intros.
                rewrite inject_terms_nth. apply (Vforall_nth ip H).
              Qed.

              Lemma mint_eval_eq_term_int_arcnat : forall t (val :
                valuation I_arcnat) k (t_b : maxvar_le k t),
              dom2vec_arcnat (term_int val t) =v mint_eval_arcnat val
              (mi_of_term_arcnat (inject_term t_b)).

              Proof.
                intros. rewrite <- (term_int_eq_bterm_int val t_b).
                apply mint_eval_eq_bterm_int_arcnat.
              Qed.

              Lemma mint_eval_equiv_arcnat : forall l r (val : valuation I_arcnat),
                let (li, ri) := rule_mi_arcnat (mkRule l r) in
                  let lev := term_int val l in
                    let rev := term_int val r in
                      let lv := mint_eval_arcnat val li in
                        let rv := mint_eval_arcnat val ri in
                          lv =v dom2vec_arcnat lev /\ rv =v dom2vec_arcnat rev.

              Proof.
                intros. simpl. split.
                rewrite (mint_eval_eq_term_int_arcnat
                  val (le_max_l (maxvar l) (maxvar r))).
                refl.
                rewrite (mint_eval_eq_term_int_arcnat
                  val (le_max_r (maxvar l) (maxvar r))).
                refl.
              Qed.

              Lemma mint_eval_mon_succeq_args_arcnat : forall k (val :
                vector vec k) (mi mi' : mint k), mint_ge_arcnat mi mi' ->
              add_vectors_arcnat (Vmap2 (@mat_vec_prod_arcnat dim dim)
                (args_arcnat mi) val) >=v add_vectors_arcnat (Vmap2
                  (@mat_vec_prod_arcnat dim dim) (args_arcnat mi') val).

              Proof.
                destruct mi. gen val. clear val. induction args_arcnat0. intros.
                destruct mi'. VOtac. 
                unfold mint_eval_arcnat, add_vectors_arcnat. simpl.
                apply (vec_ge_refl_arcnat (@zero_vec_arcnat dim)).
                intros. destruct mi'. VSntac args_arcnat1.
                unfold mint_eval_arcnat, add_vectors_arcnat. simpl.
                destruct H. apply (@vec_plus_ge_compat_arcnat dim).
                apply (IHargs_arcnat0 (Vtail val)
                  (mkMatrixInt_arcnat const_arcnat1 (Vtail (args_arcnat1)))).
                split. simpl. change args_arcnat0 with
                (Vtail (Vcons h args_arcnat0)). 
                apply Vforall2n_tail. hyp. hyp.
                apply mat_vec_prod_ge_compat_arcnat.
                change h with (Vhead (Vcons h args_arcnat0)).
                do 2 rewrite Vhead_nth.
                apply Vforall2n_nth. hyp.
                apply (vec_ge_refl_arcnat (Vhead val)).
              Qed.

              Lemma mint_eval_mon_succeq_arcnat : forall (val : valuation
                I_arcnat) k (mi mi' : mint k), mint_ge_arcnat mi mi' ->
              mint_eval_arcnat val mi >=v mint_eval_arcnat val mi'.

              Proof.
                intros. unfold mint_eval_arcnat, add_vectors_arcnat. simpl.
                apply (@vec_plus_ge_compat_arcnat dim).
                exact (mint_eval_mon_succeq_args_arcnat _ H).
                destruct H. hyp.
              Qed.

              Lemma term_ge_incl_succeq_arcnat : term_ge_arcnat << IR_succeq.

              Proof.
                intros l r lr v. destruct (mint_eval_equiv_arcnat l r v). simpl in * .
                unfold succeq_arcnat.
                rewrite <- (vec_ge_mor_arcnat H H0).
                apply mint_eval_mon_succeq_arcnat. hyp.
              Qed.

              Definition succeq_arcnat' := term_ge_arcnat.
              Definition succeq'_sub_arcnat := term_ge_incl_succeq_arcnat.
              Definition succeq'_dec_arcnat := term_ge_dec_arcnat.
              
            End OrderDecidability_arcnat.
          End MBI.
        End MatrixBasedInt_arcnat.
      End Arctic_nat.
    End S.
