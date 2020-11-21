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
(** ** Matrix interpretation over domain tropical. *)

Section MatrixLinearFunction_tropic.
  
  Variables (matrix_trop : nat -> nat -> Type) (dim argCnt : nat).
    
  (** [const_trop] being a constant vector of the interpretation of
     size [dim] and [args_trop] representing coefficients for the
     arguments with a [dim x dim] matrix per argument. *)
  
  Record matrixInt_trop : Type := mkMatrixInt_trop {
    const_trop : vector At dim;
    args_trop : vector (matrix_trop dim dim) argCnt
  }.
  
End MatrixLinearFunction_tropic.

Implicit Arguments mkMatrixInt_trop [matrix_trop dim argCnt].

Section S.
  
  Variable Sig: Signature.
  Variable dim : nat.
  Parameter dim_pos : dim > 0.

  (** Matrix based int over domain tropical. *)
  
  Section Tropical_Dom.

    Notation matrixInt := (matrixInt_trop matrix_trop).

    (* TODO: missing trsInt_ok *)

    Record MatrixMethodConf_trop : Type := mkMatrixMethodConf_trop {
      trsInt_trop : forall f : Sig, matrixInt dim (ASignature.arity f)
    }.
    
    Notation vec := (vector At dim).
    Definition vec_at0_trop (v : vec) := Vnth v dim_pos .
    
    Notation "x >> y" := (gtt x y) (at level 70).
    
    Definition vec_invariant_trop (v : vec) := A0t >> vec_at0_trop v.
    
    Parameter inv_id_matrix_trop : 
      vec_invariant_trop (Vreplace (Vconst A0t dim) dim_pos A1t).
    
    Section MatrixBasedInt_trop.
      
      Notation A := At.
      Notation A0 := A0t.
      Notation A1 := A1t.
      Notation eqA := eqAt.
      Notation sid_theoryA := sid_theoryAt.
      Notation ge := get.
      Notation ge_refl := ge_reflt.
      Notation ge_trans := ge_transt.

        (* Define Morphism [vector_plus_mor] to be able to use
           [rewrite] at the Lemma [mint_eval_var_aux] later. *)

      Add Parametric Morphism n : (@vector_plus_trop n) with
        signature (@eq_vec_trop n) ==> (@eq_vec_trop n) ==>
        (@eq_vec_trop n) as vector_plus_mor_trop.

      Proof.
        intros. apply Vforall2n_intro. intros. unfold vector_plus_trop.
        repeat rewrite Vnth_map2.
          (*FIXME: rewrite H does not work even if Vnth is declared as morphism *)
        apply Aplus_mort; apply (Vnth_mor eqAt); hyp.
      Qed.

        (* Add new setoid to be able to use [sym] at [eqA] use later
        in some lemmas. *)

      Add Setoid A eqA sid_theoryA as A_Setoid_trop.
      
        (* Define [ge] relation to be able to use [trans] for morphism
        of [vec_ge_mor]. *)

      Add Relation A ge 
      reflexivity proved by ge_refl
      transitivity proved by ge_trans
        as ge_rel_trop.

        (* Define morphism to be able to rewrite [vec_ge_mor]
        later. *)
      
      Add Parametric Morphism n : (@vec_ge_trop n) with signature
        (@eq_vec_trop n) ==> (@eq_vec_trop n) ==> iff as
          vec_ge_mor_troptrop.

      Proof.
        unfold vec_ge_trop. intros.
        apply (Vforall2n_mor sid_theoryAt). intuition.
        trans a1. apply eq_ge_compatt. sym. hyp.
        trans a2. hyp. apply eq_ge_compatt. hyp.
        trans a1'. apply eq_ge_compatt. hyp.
        trans a2'. hyp. apply eq_ge_compatt. sym. hyp.
        hyp. hyp.
      Qed.
      
      Implicit Arguments vec_ge_mor_trop [n x y x0 y0].

        (* Define this relation on [vec_eq] to be able to use
           [symm], etc. *)
      
      Add Parametric Relation n : (vector At n) (@eq_vec_trop n)
        reflexivity proved by (@eq_vec_refl A eqA sid_theoryA n)
        symmetry proved by (@eq_vec_sym A eqA sid_theoryA n)
          transitivity proved by (@eq_vec_trans A eqA sid_theoryA n)
            as eq_vec_rel_trop.
      
        (* Add these relations and morphisms to be able to use it rewriting
           and [trans], etc later for matrix.
           Add [mat_eqA] to be able to use rewrite [mat_mult_id_l] *)
      
      Add Parametric Relation m n : (matrix_trop m n) (@mat_eqA_trop
        m n) reflexivity proved by (@mat_eqA_refl_trop m n) symmetry
      proved by (@mat_eqA_sym_trop m n) transitivity proved by
        (@mat_eqA_trans_trop m n) as mat_eqA_rel_trop.
      
        (* Define this morphism to be able to use rewrite
        [zero_matrix_mult_l]. *)

      Add Parametric Morphism m n i (h:i<n) : (fun M =>
        @get_col_trop m n M i h) with signature (@mat_eqA_trop m n)
      ==> (@eq_vec_trop m) as get_col_mor_trop.
        
      Proof.
        intros. unfold eq_vec_trop. apply Vforall2n_intro. intros.
        repeat rewrite <- get_elem_swap_trop. apply H.
      Qed.
      
        (* Define this morphism to be able to use [rewrite H0] in
        [mat_vec_prod_mor]. *)
      
      Add Parametric Morphism n : (@vec_to_col_mat_trop n) with
        signature (@eq_vec_trop n) ==> (@mat_eqA_trop n 1) as
          vec_to_col_mat_mor_trop.
        
      Proof.
        unfold vec_to_col_mat_trop, mat_eqA_trop,
          get_elem_trop. intros.
        repeat rewrite get_elem_swap_trop.
        unfold get_col_trop. repeat rewrite Vnth_map.
        apply (Vnth_mor eqA). rewrite (eq_vec_cons eqA). intuition.
        apply (Vnth_mor eqA). hyp.
      Qed.
      
        (* Define this morphism to be able to use [rewrite H] for
        [mat_vec_prod_mor]. *)
      
      Add Parametric Morphism m n p : (@mat_mult_trop m n p) with
        signature (@mat_eqA_trop m n) ==> (@mat_eqA_trop n p) ==>
        (@mat_eqA_trop m p) as mat_mult_mor_trop.
        
      Proof.
        unfold mat_mult_trop. intros. unfold mat_eqA_trop. intros.
        repeat rewrite mat_build_elem_trop. apply dot_product_mor_trop.
        apply get_row_mor_trop. hyp. apply get_col_mor_trop. hyp.
      Qed.

        (* Define this morphism to be able to rewrite
        [mat_vec_prod_distr_vec] later. *)
      
      Add Parametric Morphism m n : (@mat_vec_prod_trop m n) with
        signature (@mat_eqA_trop m n) ==> (@eq_vec_trop n) ==>
        (@eq_vec_trop m) as mat_vec_prod_mor_trop.
        
      Proof.
        unfold mat_vec_prod_trop.
        intros. apply get_col_mor_trop. rewrite H. rewrite H0.
        refl.
      Qed.
      
        (* Adding notations *)

      Notation vec := (vector At dim).
      Notation eq_vec_st := (@eq_vec_st _ _ sid_theoryAt dim).
      Notation mat_eqA := (@mat_eqA_trop dim dim).
      Notation mat_eqA_st := (@mat_eqA_st_trop dim dim). 
      Notation matrixInt := (matrixInt_trop matrix_trop).
      Notation mint := (matrixInt dim).
      Notation mat := (matrix_trop dim dim).
      Notation eq_vec_st' := (@eq_vec_st _ _ sid_theoryAt dim).
      Notation eq_vec_mat_eqA_st' := (@VecEq.eq_vec_st _ _ mat_eqA_st).
      Notation eq_vec := (@eq_vec_trop dim).
      Notation "x =v y" := (eq_vec x y)(at level 70).
      Notation "x >>= y" := (get x y) (at level 70).

      Infix "[+]" := vector_plus_trop (at level 50).
      Infix "<*>" := mat_mult_trop (at level 40).

      Add Parametric Relation k : (vector vec k) (@VecEq.eq_vec _
        eq_vec k) reflexivity proved by (@eq_vec_refl _ _ eq_vec_st
          k) symmetry proved by (@eq_vec_sym _ _ eq_vec_st k)
        transitivity proved by (@eq_vec_trans _ _ eq_vec_st k) as
          eq_vec_eq_vec_rel_trop.
      
      Add Parametric Relation k : (vector (matrix_trop dim dim) k)
        (@VecEq.eq_vec _ mat_eqA k) reflexivity proved by
        (@eq_vec_refl _ _ mat_eqA_st k) symmetry proved by
          (@eq_vec_sym _ _ mat_eqA_st k) transitivity proved by
            (@eq_vec_trans _ _ mat_eqA_st k) as eq_vec_mat_eqA_rel_trop.

      Definition eq_mint_trop k (mi1 mi2 : mint k) := let (c1,
        args1) := mi1 in let (c2, args2) := mi2 in c1 =v c2 /\
      VecEq.eq_vec mat_eqA args1 args2.

      Notation "x =i y" := (eq_mint_trop x y) (at level 70).
      
      Lemma eq_mint_refl_trop : forall k (x : mint k), x =i x.
        
      Proof.
        unfold eq_mint_trop. destruct x. intuition.
      Qed.

      Lemma eq_mint_sym_trop : forall k (x y : mint k), x =i y -> y
        =i x.

      Proof.
        unfold eq_mint_trop. destruct x. destruct y. intuition.
      Qed.

      Lemma eq_mint_trans_trop : forall k (x y z : mint k), x =i y
        -> y =i z -> x =i z.

      Proof.
        unfold eq_mint_trop. destruct x. destruct y. destruct z. intuition.
        trans const_trop1; hyp. trans args_trop1; hyp.
      Qed.

      Add Parametric Relation k : (@mint k) (@eq_mint_trop k)
        reflexivity proved by (@eq_mint_refl_trop k) symmetry proved
          by (@eq_mint_sym_trop k) transitivity proved by
            (@eq_mint_trans_trop k) as eq_mint_rel_trop.
      
      Add Parametric Morphism k : (@mkMatrixInt_trop matrix_trop dim
        k) with signature eq_vec ==> (@VecEq.eq_vec _ mat_eqA k) ==>
      (@eq_mint_trop k) as mkMatrixInt_mor_trop.

      Proof.
        unfold eq_mint_trop. auto.
      Qed.

      Add Parametric Morphism k : (@const_trop matrix_trop dim k)
        with signature (@eq_mint_trop k) ==> eq_vec as
          const_mor_trop.

      Proof.
        destruct x. destruct y. simpl. intuition.
      Qed.

      Add Parametric Morphism k : (@args_trop matrix_trop dim k)
        with signature (@eq_mint_trop k) ==> (@VecEq.eq_vec _
          mat_eqA k) as args_mor_trop.

      Proof.
        destruct x. destruct y. simpl. intuition.
      Qed.

      Section MBI.

        Definition dom_trop := { v : vec | vec_invariant_trop v }.

        Definition dom2vec_trop (d : dom_trop) : vec := proj1_sig d.

        Definition add_matrices_trop i m n (v : vector (matrix_trop
          m n) i) := Vfold_left (@mat_plus_trop m n)
        (zero_matrix_trop m n) v.

        Definition mi_eval_aux_trop n (mi : mint n) (v : vector vec n) : vec :=
          add_vectors_trop (n:=dim) (k:=n)(Vmap2 (@mat_vec_prod_trop dim dim)
            (args_trop mi) v) [+] const_trop mi.

        Add Parametric Morphism n : (@mi_eval_aux_trop n) with
          signature (@eq_mint_trop n) ==> (@VecEq.eq_vec _ eq_vec n)
          ==> eq_vec as mi_eval_aux_mor_trop.

        Proof.
          unfold mi_eval_aux_trop.
          intuition. apply vector_plus_mor_trop.
          apply add_vectors_mor_trop.
          apply Vforall2n_intro. intros. repeat rewrite Vnth_map2.
          apply mat_vec_prod_mor_trop.
          apply (Vnth_mor mat_eqA). rewrite H. refl.
          apply (Vnth_mor eq_vec). hyp.
          rewrite H. refl.
        Qed.

        Variable ma : MatrixMethodConf_trop.

        Variable mi_eval_ok : forall f v, vec_invariant_trop
          (mi_eval_aux_trop (trsInt_trop ma f) (Vmap dom2vec_trop
            v)).

        Definition mi_eval_trop f (v : vector dom_trop
          (ASignature.arity f)) : dom_trop := exist (fun v =>
            vec_invariant_trop v) (mi_eval_aux_trop (trsInt_trop ma f)
              (Vmap dom2vec_trop v)) (mi_eval_ok f v).

        Lemma mi_eval_cons_trop : forall n (mi : mint (S n)) v vs,
          mi_eval_aux_trop mi (Vcons v vs) =v mat_vec_prod_trop
          (Vhead (args_trop mi)) v [+] mi_eval_aux_trop
          (mkMatrixInt_trop (const_trop mi) (Vtail (args_trop mi)))
          vs.

        Proof.
          intros. unfold mi_eval_aux_trop.
          simpl. rewrite vector_plus_assoc_trop.
          apply vector_plus_mor_trop.
          apply vector_plus_comm_trop. refl.
        Qed.
        
        Notation "x >> y" := (gtt x y) (at level 70).

        Definition dom_zero_trop: dom_trop.

        Proof.
          exists (Vreplace (Vconst A0t dim) dim_pos A1t).
          apply inv_id_matrix_trop.
        Defined.

        Definition I_trop := @mkInterpretation Sig dom_trop
          dom_zero_trop mi_eval_trop.

          (*REMOVE: unusued
             Variable succ : relation dom.
             Notation "x >v y" := (succ x y) (at level 70).*)

        Infix ">=v" := vec_ge_trop (at level 70).

        Definition succeq_trop (x y : dom_trop) := (dom2vec_trop x)
          >=v (dom2vec_trop y).

        Lemma refl_succeq_trop : reflexive succeq_trop.
          
        Proof.
          intro x. apply vec_ge_refl_trop.
        Qed.

        Lemma trans_succeq_trop : transitive succeq_trop.
          
        Proof.
          unfold succeq_trop. apply Rof_trans with
          (f:=dom2vec_trop). apply vec_ge_trans_trop.
        Qed.

      (** Monotonicity *)

        Section VecMonotonicity_trop.

          Variable f : matrix_trop dim dim -> vec -> vec.
          Variable f_mon : forall M v1 v2, v1 >=v v2 -> f M v1 >=v f M v2.
          Variables (a b : vec).

          Lemma vec_add_weak_monotone_map2_trop : forall n1 (v1 :
            vector vec n1) n2 (v2 : vector vec n2) n (M : vector
              (matrix_trop dim dim) n) i_j, a >=v b ->
            add_vectors_trop (Vmap2 f M (Vcast (Vapp v1 (Vcons a
              v2)) i_j)) >=v add_vectors_trop (Vmap2 f M (Vcast (Vapp
                v1 (Vcons b v2)) i_j)).

          Proof.
            induction v1; intros; simpl.
            destruct n; try solve [NatUtil.absurd_arith].
            unfold add_vectors_trop, succeq_trop,
              vec_ge_trop. simpl. apply Vforall2n_intro. 
            intros. unfold vector_plus_trop. do 2 rewrite Vnth_map2.
            assert (Vnth (f (Vhead M) a) ip >>= Vnth (f (Vhead M) b) ip).
            apply Vforall2n_nth. apply f_mon. hyp.
            apply plus_ge_compat_trop. apply ge_reflt. hyp.
            destruct n0; try solve [NatUtil.absurd_arith].
            unfold add_vectors_trop, succeq_trop, vec_ge_trop.
            simpl. apply Vforall2n_intro. 
            intros. unfold vector_plus_trop. do 2 rewrite Vnth_map2.
            apply plus_ge_compat_trop. 
            apply Vforall2n_nth.
            unfold add_vectors_trop in IHv1. apply IHv1.
            hyp. apply ge_reflt.
          Qed.
          
        End VecMonotonicity_trop.

        Lemma monotone_succeq_trop : monotone I_trop succeq_trop.

        Proof.
          intros f i j i_j vi vj a b ab.
          simpl. unfold mi_eval_trop, mi_eval_aux_trop,
          succeq_trop. simpl.
          apply (@vec_plus_ge_compat_r_trop dim).
          do 2 rewrite Vmap_cast. do 2 rewrite Vmap_app. simpl.
          apply vec_add_weak_monotone_map2_trop; trivial.
          intros. unfold succeq_trop, vec_ge_trop.
          apply Vforall2n_intro. intros.
          unfold mat_vec_prod_trop. 
          do 2 rewrite Vnth_col_mat_trop. apply mat_mult_mon_trop.
          apply mat_ge_refl_trop. intros x y xp yp.
          do 2 rewrite vec_to_col_mat_spec_trop.
          apply Vforall2n_nth. hyp.
        Qed.

        Lemma succeq_dec_trop : rel_dec succeq_trop.
          
        Proof.
          intros x y. unfold succeq_trop, vec_ge_trop.
          apply Vforall2n_dec.
          intros m1 n. apply ge_dect.
        Defined.

          (** Decidability of order on terms induced by matrix
          interpretations. *)

        Section OrderDecidability_trop.

          Require Import ABterm.
          
          Notation bterm := (bterm Sig).

            (** Symbolic computation of term interpretation. *)

          Definition mat_matrixInt_prod_trop n M (mi : mint n) :
            mint n := mkMatrixInt_trop (mat_vec_prod_trop M
              (const_trop mi)) (Vmap (mat_mult_trop M) (args_trop
                mi)).

          Definition combine_matrices_trop n k (v : vector (vector
            mat k) n) := Vbuild (fun i ip => add_matrices_trop (Vmap
              (fun v => Vnth v ip) v)).

          Lemma combine_matrices_nil_trop : forall i,
            combine_matrices_trop Vnil = Vconst (@zero_matrix_trop
              dim dim) i.
            
          Proof.
            intros. apply Veq_nth. intros. unfold combine_matrices_trop.
            rewrite Vnth_const. rewrite Vbuild_nth. trivial.
          Qed.

          Lemma combine_matrices_cons_trop : forall k n v (vs :
            vector (vector mat k) n), combine_matrices_trop (Vcons v
              vs) = Vmap2 (@mat_plus_trop _ _) (combine_matrices_trop
                vs) v.

          Proof.
            intros. apply Veq_nth. intros.
            unfold combine_matrices_trop, add_matrices_trop. simpl.
            rewrite Vnth_map2. do 2 rewrite Vbuild_nth. refl.
          Qed.

          Fixpoint mi_of_term_trop k (t : bterm k) : mint (S k) :=
            match t with
              | BVar i ip => 
                let zero_int := Vconst (zero_matrix_trop dim dim) (S k) in
                  let args_int := Vreplace zero_int (le_lt_S ip) (id_matrix_trop dim) in
                    mkMatrixInt_trop (@zero_vec_trop dim) args_int
              | BFun f v => 
                let f_int := trsInt_trop ma f in
                  let args_int := Vmap (@mi_of_term_trop k) v in
                    let args_int' := Vmap2 (@mat_matrixInt_prod_trop (S k)) 
                      (args_trop f_int) args_int in
                      let res_const := add_vectors_trop (Vcons (const_trop f_int) 
                        (Vmap (@const_trop matrix_trop dim (S k)) args_int')) in
                      let res_args := combine_matrices_trop
                        (Vmap (@args_trop matrix_trop dim (S k)) 
                          args_int') in
                        mkMatrixInt_trop res_const res_args
            end.

          Require Import ATrs.

          Definition rule_mi_trop r :=
            let mvl := maxvar (lhs r) in
              let mvr := maxvar (rhs r) in
                let m := max mvl mvr in
                  let lt := inject_term (le_max_l mvl mvr) in
                    let rt := inject_term (le_max_r mvl mvr) in
                      (mi_of_term_trop lt, mi_of_term_trop rt).

            (** Order characteristic for symbolically computed interpretation and 
               its decidability. *)
          
          Notation mat_ge := (@mat_ge_trop dim dim).
          
          Definition mint_ge_trop n (l r : mint n) := Vforall2n
            mat_ge (args_trop l) (args_trop r) /\ (@vec_ge_trop dim)
            (const_trop l) (const_trop r).

          Definition term_ord_trop (ord : forall n, relation (mint
            n)) l r := let (li, ri) := rule_mi_trop (mkRule l r) in
          ord _ li ri.

          Variable mint_gt_trop : forall n (l r : mint n), Prop.
          Variable mint_gt_dec_trop : forall n, rel_dec (@mint_gt_trop n).

          Definition term_ge_trop := term_ord_trop mint_ge_trop.
          Definition term_gt_trop := term_ord_trop mint_gt_trop.

          Lemma mint_ge_dec_trop : forall n, rel_dec (@mint_ge_trop n).

          Proof.
            intros n x y. unfold mint_ge_trop.
            destruct (Vforall2n_dec
              (@mat_ge_dec_trop dim dim) (args_trop x) (args_trop y)); 
            intuition.
            destruct (vec_ge_dec_trop (const_trop x) (const_trop y)); intuition.
          Defined.

          Lemma term_ge_dec_trop : rel_dec term_ge_trop.
            
          Proof.
            intros l r. unfold term_ge_trop, term_ord_trop. simpl.
            match goal with |- {mint_ge_trop ?l ?r} + {~mint_ge_trop ?l ?r} => 
              destruct (mint_ge_dec_trop l r); auto
            end.
          Defined.

          Lemma term_gt_dec_trop : rel_dec term_gt_trop.
            
          Proof.
            intros l r. unfold term_gt_trop, term_ord_trop. simpl.
            match goal with |- {mint_gt_trop ?l ?r} + {~mint_gt_trop ?l ?r} => 
              destruct (mint_gt_dec_trop l r); auto
            end.
          Defined.

          Notation IR_succeq := (IR I_trop succeq_trop).

          Definition mint_eval_trop (val : valuation I_trop) k (mi :
            mint k) : vec := let coefs := Vbuild (fun i (ip : i < k)
              => dom2vec_trop (val i)) in add_vectors_trop (Vcons
                (const_trop mi) (Vmap2 (@mat_vec_prod_trop dim dim)
                  (args_trop mi) coefs)).

          Add Parametric Morphism val k : (@mint_eval_trop val k)
            with signature (@eq_mint_trop k) ==> eq_vec as
              mint_eval_mor_trop.

          Proof.
            unfold eq_mint_trop. intros [c1 args1] [c2 args2]. intuition.
            unfold mint_eval_trop. simpl. apply add_vectors_mor_trop.
            rewrite (eq_vec_cons eq_vec). intuition.
            apply Vmap2_mor with (eqA := @mat_eqA_trop dim dim) (eqB := eq_vec).
            apply eq_vec_st. apply mat_vec_prod_mor_trop. hyp.
            apply eq_vec_refl. apply eq_vec_st.
          Qed.

          Lemma mint_eval_split_trop : forall val k (mi : mint k),
            let coefs := Vbuild (fun i (ip : i < k) => dom2vec_trop
              (val i)) in mint_eval_trop val mi =v const_trop mi [+]
            add_vectors_trop (Vmap2 (@mat_vec_prod_trop dim dim)
              (args_trop mi) coefs).

          Proof.
            intros. unfold mint_eval_trop, add_vectors_trop. simpl.
            rewrite vector_plus_comm_trop. refl.
          Qed.
          
          Hint Rewrite mat_mult_id_l_trop zero_matrix_mult_l_trop
            using simpl : arith.

          Lemma mint_eval_var_aux_trop : forall M i k (v : vector
            vec k) (ip : i < k), add_vectors_trop (Vmap2
              (@mat_vec_prod_trop dim dim) (Vreplace (Vconst
                (zero_matrix_trop dim dim) k) ip M) v) =v
            col_mat_to_vec_trop (M <*> (vec_to_col_mat_trop (Vnth v
              ip))).

          Proof.
            induction i; intros.
            destruct k. NatUtil.absurd_arith.
            unfold add_vectors_trop. simpl.
            fold (add_vectors_trop
              (Vmap2 (@mat_vec_prod_trop dim dim)
                (Vconst (zero_matrix_trop dim dim) k) (Vtail v))).
            assert (add_vectors_trop
              (Vmap2 (@mat_vec_prod_trop dim dim) (Vconst
                (zero_matrix_trop dim dim) k) (Vtail v))
              =v @zero_vec_trop dim).
            Focus 2. rewrite H.
            rewrite vector_plus_zero_l_trop.
            unfold mat_vec_prod_trop.
            replace (Vhead v) with (Vnth v ip).
            refl.
            rewrite Vhead_nth.
            rewrite (NatUtil.lt_unique (Lt.lt_O_Sn k) ip). refl.
            apply add_vectors_zero_trop. apply Vforall_nth_intro. intros.
            rewrite Vnth_map2. rewrite Vnth_const.
            unfold mat_vec_prod_trop.
            rewrite zero_matrix_mult_l_trop.
            apply Vforall2n_intro. intros. rewrite Vnth_col_mat_trop.
            unfold zero_matrix_trop, zero_vec_trop.
            rewrite mat_build_elem_trop. rewrite Vnth_const. refl.
            destruct k. NatUtil.absurd_arith.
            rewrite Vreplace_tail. simpl.
            rewrite add_vectors_cons_trop.
            unfold mat_vec_prod_trop at 1.
            rewrite zero_matrix_mult_l_trop.
            assert (col_mat_to_vec_trop 
              (zero_matrix_trop dim 1) =v zero_vec_trop dim).
            apply Vforall2n_intro. intros.
            rewrite Vnth_col_mat_trop.
            unfold zero_matrix_trop, zero_vec_trop.
            rewrite mat_build_elem_trop. 
            rewrite Vnth_const. refl. rewrite H.
            rewrite vector_plus_zero_l_trop.
            rewrite IHi. rewrite Vnth_tail.
            rewrite (NatUtil.le_unique 
              (Lt.lt_n_S (Lt.lt_S_n ip)) ip). refl.
          Qed.

          Lemma mint_eval_eq_term_int_var_trop : forall v (val :
            valuation I_trop) k (t_b : maxvar_le k (Var v)),
          dom2vec_trop (bterm_int val (inject_term t_b)) =v
          mint_eval_trop val (mi_of_term_trop (inject_term t_b)).

          Proof.
            intros. rewrite mint_eval_split_trop.
            change (const_trop (mi_of_term_trop 
              (inject_term t_b))) with (zero_vec_trop dim).
            rewrite vector_plus_zero_l_trop.
            change (args_trop (mi_of_term_trop 
              (inject_term t_b))) with (Vreplace (Vconst 
                (zero_matrix_trop dim dim) (S k)) (NatUtil.le_lt_S (maxvar_var t_b)) 
              (id_matrix_trop dim)).
            rewrite mint_eval_var_aux_trop.
            rewrite Vbuild_nth. simpl.
            trans (col_mat_to_vec_trop 
              (vec_to_col_mat_trop (dom2vec_trop (val v)))).
            rewrite col_mat_to_vec_idem_trop. 
            refl. apply get_col_mor_trop.
            rewrite mat_mult_id_l_trop. refl. ded dim_pos. auto.
          Qed.
          
            (* REMARK: using Hint rewrite to be able to use the
            [autorewrite] *)

          Hint Rewrite vector_plus_zero_l_trop
            vector_plus_zero_r_trop add_vectors_cons_trop : arith.

          Lemma mint_eval_const_trop : forall val k (c : vec),
            mint_eval_trop (k:=k) val (mkMatrixInt_trop c
              (combine_matrices_trop Vnil)) =v c.

          Proof.
            intros. unfold mint_eval_trop. simpl.
            autorewrite with arith.
            trans (c [+] @zero_vec_trop dim).
            apply vector_plus_mor_trop. refl.
            apply add_vectors_zero_trop. 
            apply Vforall_nth_intro. intros.
            rewrite Vnth_map2. 
            rewrite combine_matrices_nil_trop. rewrite Vnth_const.
            unfold mat_vec_prod_trop. apply Vforall2n_intro. intros.
            rewrite Vnth_col_mat_trop.
            trans (get_elem_trop (zero_matrix_trop dim 1) ip0 access_0).
            apply get_elem_mor_trop. apply zero_matrix_mult_l_trop.
            unfold zero_matrix_trop. rewrite mat_build_elem_trop.
            unfold zero_vec_trop. rewrite Vnth_const. refl.
            apply vector_plus_zero_r_trop.
          Qed.

          Lemma mint_eval_cons_trop : forall n k val c_hd c_tl a_hd
            (a_tl : vector (vector mat k) n), mint_eval_trop val
            (mkMatrixInt_trop (c_hd [+] c_tl) (combine_matrices_trop
              (Vcons a_hd a_tl))) =v mint_eval_trop val
            (mkMatrixInt_trop c_hd a_hd) [+] mint_eval_trop val
            (mkMatrixInt_trop c_tl (combine_matrices_trop a_tl)).

          Proof.
            intros. unfold mint_eval_trop. simpl.
            set (vali := Vbuild (A := vec) 
              (fun i (_ : i < k) => dom2vec_trop (val i))).
            rewrite combine_matrices_cons_trop.
            autorewrite with arith. 
            repeat rewrite <- vector_plus_assoc_trop.
            apply vector_plus_mor_trop. refl. 
            rewrite vector_plus_assoc_trop.
            rewrite (vector_plus_comm_trop _ c_tl). 
            rewrite <- vector_plus_assoc_trop.
            apply vector_plus_mor_trop. refl.
            apply add_vectors_split_trop. intros.
            repeat rewrite Vnth_map2. rewrite vector_plus_comm_trop.
            apply mat_vec_prod_distr_mat_trop.
          Qed.

          Lemma mint_eval_mult_factor_trop : forall k val M (mi :
            mint k), mint_eval_trop val (mat_matrixInt_prod_trop M
              mi) =v mat_vec_prod_trop M (mint_eval_trop val mi).

          Proof.
            unfold mint_eval_trop. intros. 
            simpl. autorewrite with arith.
            rewrite mat_vec_prod_distr_vec_trop.
            apply vector_plus_mor_trop. refl.
            set (gen := Vbuild (A:=vec) 
              (fun i (_ : i < k) => dom2vec_trop (val i))).
            rewrite (mat_vec_prod_distr_add_vectors_trop M 
              (Vmap2 (@mat_vec_prod_trop dim dim) (args_trop mi) gen)
              (Vmap2 (@mat_vec_prod_trop dim dim) (Vmap (mat_mult_trop M) 
                (args_trop mi)) gen)).
            refl. intros. repeat rewrite Vnth_map2. rewrite Vnth_map.
            unfold mat_vec_prod_trop. rewrite vec_to_col_mat_idem_trop.
            apply get_col_mor_trop. rewrite mat_mult_assoc_trop. refl.
          Qed.

          Lemma mint_eval_eq_bterm_int_fapp_trop : forall k i fi val
            (v : vector (bterm k) i), let arg_eval := Vmap2
              (@mat_matrixInt_prod_trop (S k)) (args_trop fi) (Vmap
                (@mi_of_term_trop k) v) in mi_eval_aux_trop fi (Vmap
                  (fun t : bterm k => mint_eval_trop val (mi_of_term_trop
                    t)) v) =v mint_eval_trop val (mkMatrixInt_trop
                      (add_vectors_trop (Vcons (const_trop fi) (Vmap
                        (@const_trop matrix_trop dim (S k)) arg_eval)))
                      (combine_matrices_trop (Vmap (@args_trop matrix_trop dim
                        (S k)) arg_eval))).

          Proof.
            induction i; intros.
              (* i = 0 *)
            VOtac. simpl.
            unfold mi_eval_aux_trop, add_vectors_trop.
            simpl. autorewrite with arith.
            sym. apply mint_eval_const_trop.
              (* i > 0 *)
            VSntac v. simpl mi_eval_aux_trop.
            rewrite mi_eval_cons_trop. 
            rewrite IHi. simpl.
            trans (@mint_eval_trop val (S k)
              (@mkMatrixInt_trop matrix_trop dim (S k)
                (@mat_vec_prod_trop dim dim
                  (@Vhead (matrix_trop dim dim) i
                    (@args_trop matrix_trop dim (S i) fi))
                  (@const_trop matrix_trop dim (S k)
                    (@Vhead (mint (S k)) i
                      (@Vmap (ABterm.bterm Sig k)
                        (mint (S k))
                        (@mi_of_term_trop k) (S i) v)))
                  [+] @add_vectors_trop dim (S i) (@Vcons (vector At dim)
                    (@const_trop matrix_trop dim (S i) fi) i
                    (@Vmap (mint (S k)) 
                      (vector At dim) (@const_trop matrix_trop dim (S k)) i
                      (@Vmap2 (matrix_trop dim dim)
                        (mint (S k))
                        (mint (S k))
                        (@mat_matrixInt_prod_trop (S k)) i
                        (@Vtail (matrix_trop dim dim) i
                          (@args_trop matrix_trop dim (S i) fi))
                        (@Vtail (mint (S k)) i
                          (@Vmap (ABterm.bterm Sig k)
                            (mint (S k))
                            (@mi_of_term_trop k) (S i) v))))))
                (@combine_matrices_trop (S i) (S k)
                  (@Vcons (vector (matrix_trop dim dim) (S k))
                    (@Vmap (matrix_trop dim dim) (matrix_trop dim dim)
                      (@mat_mult_trop dim dim dim
                        (@Vhead (matrix_trop dim dim) i
                          (@args_trop matrix_trop dim (S i) fi))) 
                      (S k)
                      (@args_trop matrix_trop dim (S k)
                        (@Vhead (mint (S k)) i
                          (@Vmap (ABterm.bterm Sig k)
                            (mint (S k))
                            (@mi_of_term_trop k) (S i) v)))) i
                    (@Vmap (mint (S k))
                      (vector (matrix_trop dim dim) (S k))
                      (@args_trop matrix_trop dim (S k)) i
                      (@Vmap2 (matrix_trop dim dim)
                        (mint (S k))
                        (mint (S k))
                        (@mat_matrixInt_prod_trop (S k)) i
                        (@Vtail (matrix_trop dim dim) i
                          (@args_trop matrix_trop dim (S i) fi))
                        (@Vtail (mint (S k)) i
                          (@Vmap (ABterm.bterm Sig k)
                            (mint (S k))
                            (@mi_of_term_trop k) (S i) v)))))))).
            Focus 2. apply mint_eval_mor_trop. split. rewrite add_vectors_perm_trop.
            rewrite (add_vectors_cons_trop (i := S i) 
              (mat_vec_prod_trop (Vhead (args_trop fi))
                (const_trop (Vhead (Vmap (mi_of_term_trop (k:=k)) v))))). refl.
            apply eq_vec_refl. apply mat_eqA_st.
            rewrite mint_eval_cons_trop. apply vector_plus_mor_trop.
            Focus 2. rewrite Vmap_tail. refl.
            rewrite H. simpl.
            fold (mat_matrixInt_prod_trop 
              (Vhead (args_trop fi)) (mi_of_term_trop (Vhead v))).
            sym. apply mint_eval_mult_factor_trop.
          Qed.

          Lemma mint_eval_eq_bterm_int_trop : forall (val :
            valuation I_trop) t k (t_b : maxvar_le k t),
          dom2vec_trop (bterm_int val (inject_term t_b)) =v
          mint_eval_trop val (mi_of_term_trop (inject_term t_b)).

          Proof.
            intros val t. pattern t. apply term_ind_forall; intros.
            apply mint_eval_eq_term_int_var_trop.
            rewrite inject_term_eq. simpl.
            rewrite Vmap_map.
            rewrite (@Vmap_eqA _ _ eq_vec eq_vec_st
              (fun x => dom2vec_trop (bterm_int val x)) 
              (fun (t : bterm k) => mint_eval_trop val (mi_of_term_trop t))).
            simpl. apply mint_eval_eq_bterm_int_fapp_trop.
            apply Vforall_nth_intro. intros.
            rewrite inject_terms_nth. apply (Vforall_nth ip H).
          Qed.

          Lemma mint_eval_eq_term_int_trop : forall t (val :
            valuation I_trop) k (t_b : maxvar_le k t), dom2vec_trop
          (term_int val t) =v mint_eval_trop val (mi_of_term_trop
            (inject_term t_b)).

          Proof.
            intros. rewrite <- (term_int_eq_bterm_int val t_b).
            apply mint_eval_eq_bterm_int_trop.
          Qed.

          Lemma mint_eval_equiv_trop : forall l r (val : valuation I_trop),
            let (li, ri) := rule_mi_trop (mkRule l r) in
              let lev := term_int val l in
                let rev := term_int val r in
                  let lv := mint_eval_trop val li in
                    let rv := mint_eval_trop val ri in
                      lv =v dom2vec_trop lev /\ rv =v dom2vec_trop rev.

          Proof.
            intros. simpl. split.
            rewrite (mint_eval_eq_term_int_trop 
              val (le_max_l (maxvar l) (maxvar r))).
            refl.
            rewrite (mint_eval_eq_term_int_trop
              val (le_max_r (maxvar l) (maxvar r))).
            refl.
          Qed.

          Lemma mint_eval_mon_succeq_args_trop : forall k (val :
            vector vec k) (mi mi' : mint k), mint_ge_trop mi mi' ->
          add_vectors_trop (Vmap2 (@mat_vec_prod_trop dim dim)
            (args_trop mi) val) >=v add_vectors_trop (Vmap2
              (@mat_vec_prod_trop dim dim) (args_trop mi') val).

          Proof.
            destruct mi. gen val. clear val. induction args_trop0. intros.
            destruct mi'. VOtac. 
            unfold mint_eval_trop, add_vectors_trop. simpl.
            apply (vec_ge_refl_trop (@zero_vec_trop dim)).
            intros. destruct mi'. VSntac args_trop1.
            unfold mint_eval_trop, add_vectors_trop. simpl.
            destruct H. apply (@vec_plus_ge_compat_trop dim).
            apply (IHargs_trop0 (Vtail val)
              (mkMatrixInt_trop const_trop1 (Vtail (args_trop1)))).
            split. simpl. change args_trop0 with (Vtail (Vcons h args_trop0)). 
            apply Vforall2n_tail. hyp. hyp.
            apply mat_vec_prod_ge_compat_trop.
            change h with (Vhead (Vcons h args_trop0)). do 2 rewrite Vhead_nth.
            apply Vforall2n_nth. hyp.
            apply (vec_ge_refl_trop (Vhead val)).
          Qed.

          Lemma mint_eval_mon_succeq_trop : forall (val : valuation I_trop) k 
            (mi mi' : mint k), mint_ge_trop mi mi' -> 
            mint_eval_trop val mi >=v mint_eval_trop val mi'.

          Proof.
            intros. unfold mint_eval_trop, add_vectors_trop. simpl.
            apply (@vec_plus_ge_compat_trop dim).
            exact (mint_eval_mon_succeq_args_trop _ H).
            destruct H. hyp.
          Qed.

          Lemma term_ge_incl_succeq_trop : term_ge_trop <<
            IR_succeq.

          Proof.
            intros l r lr v. destruct (mint_eval_equiv_trop l r v). simpl in * .
            unfold succeq_trop.
            rewrite <- (vec_ge_mor_trop H H0).
            apply mint_eval_mon_succeq_trop. hyp.
          Qed.

          Definition succeq_trop' := term_ge_trop.
          Definition succeq'_sub_trop := term_ge_incl_succeq_trop.
          Definition succeq'_dec_trop := term_ge_dec_trop.

        End OrderDecidability_trop.
      End MBI.
    End MatrixBasedInt_trop.
  End Tropical_Dom.
End S.
