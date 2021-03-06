(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-25 (setoid)
- Adam Koprowski and Johannes Waldmann, 2008-01
*)

Set Implicit Arguments.

Require Import AMonAlg2 OrdSemiRing2 ATrs LogicUtil RelUtil NatUtil
  AWFMInterpretation Max VecEq Setoid VecOrd Matrix2 VecUtil VecArith2.

(***********************************************************************)
(** * Matrix interpretation over domain natural numbers. *)

Section MatrixLinearFunction_nat.

  Variables (matrix : nat -> nat -> Type) (dim argCnt : nat).

  (** [const] being a constant vector of the interpretation of size
     [dim] and [args] representing coefficients for the arguments with
     a [dim x dim] matrix per argument. *)
  
  Record matrixInt : Type := mkMatrixInt {
    const : vector AN dim;
    args : vector (matrix dim dim) argCnt
  }.

End MatrixLinearFunction_nat.

Implicit Arguments mkMatrixInt [matrix dim argCnt].

(***********************************************************************)
(** Matrix method conf over domain natural numbers. *)

Section S.
  
  Variable Sig: Signature.
  Variable dim : nat.
  Parameter dim_pos : dim > 0.
  
  Section MatrixMethodConf.
    
    Notation A := AN.
    Notation A0 := A0N.
    Notation A1 := A1N.
    Notation vec := (vector AN dim).
    Notation eq_vec := (@eq_vec dim).
    Notation "x =v y" := (eq_vec x y)(at level 70).
    Notation mat_eqA := (@mat_eqA dim dim).
    Notation mat_eqA_st := (@mat_eqA_st dim dim). 
    Notation matrixInt := (matrixInt matrix).
    Notation mint := (matrixInt dim).
    Notation mat := (matrix dim dim).
    Notation eq_vec_st := (@eq_vec_st _ _ sid_theoryA dim).
    Notation eq_vec_mat_eqA_st := (@VecEq.eq_vec_st _ _ mat_eqA_st).
    
    (** Interpretations for all function symbols of the signature with
       respective to arity [trsInt]. *)

    Record MatrixMethodConf : Type := mkMatrixMethodConf {
      trsInt : forall f : Sig, mint (ASignature.arity f)
    }.
    
    Parameter vec_invariant : vec -> Prop.
    Parameter inv_id_matrix : 
      vec_invariant (Vreplace (Vconst A0N dim) dim_pos A1N).
    
  End MatrixMethodConf.

  Section MatrixBasedInt_nat.

    Notation A := AN.
    Notation A0 := A0N.
    Notation A1 := A1N.
    Notation eqA := eqAN.
    Notation sid_theoryA := sid_theoryAN.
    Notation ge := geN.
    Notation ge_refl := ge_reflN.
    Notation ge_trans := ge_transN.

    (** Define Morphism [vector_plus_mor] to be able to use [rewrite]
       at the Lemma [mint_eval_var_aux] later. *)
    
    Add Parametric Morphism n : (@vector_plus n)
      with signature (@eq_vec n) ==> (@eq_vec n) ==> (@eq_vec n)
        as vector_plus_mor.

    Proof.
      intros. apply Vforall2n_intro. intros. unfold vector_plus.
      repeat rewrite Vnth_map2.
      (* FIXME: rewrite H does not work even if Vnth is declared as morphism *)
      apply Aplus_morN; apply (Vnth_mor eqA); hyp.
    Qed.
    
    (* Add new setoid to be able to use [sym] at [eqA] use later in
    some lemma. *)
    Add Setoid A eqA sid_theoryA as A_Setoid.
    
    (* Define [ge] relation to be able to use [trans] for morphism of
    [vec_ge_mor]. *)
    Add Relation A ge 
    reflexivity proved by ge_refl
    transitivity proved by ge_trans
      as ge_rel.
    
    (* Define morphism to be able to rewrite [vec_ge_mor] later. *)
    Add Parametric Morphism n : (@vec_ge n)
      with signature (@eq_vec n) ==> (@eq_vec n) ==> iff
        as vec_ge_mor.

    Proof.
      unfold vec_ge. intros. apply (Vforall2n_mor sid_theoryAN).
      intuition.
      trans a1. apply eq_ge_compatN. sym. hyp.
      trans a2. hyp. apply eq_ge_compatN. hyp.
      trans a1'. apply eq_ge_compatN. hyp.
      trans a2'. hyp. apply eq_ge_compatN. sym. hyp.
      hyp. hyp.
    Qed.

    Implicit Arguments vec_ge_mor [n x y x0 y0].

    (* Define this relation on [vec_eq] to be able to use
       [symm], etc. *)
    Add Parametric Relation n : (vector A n) (@eq_vec n)
      reflexivity proved by (@eq_vec_refl A eqA sid_theoryA n)
      symmetry proved by (@eq_vec_sym A eqA sid_theoryA n)
        transitivity proved by (@eq_vec_trans A eqA sid_theoryA n)
          as eq_vec_rel.

    (* Add these relations and morphisms to be able to use it
       rewriting and [trans], etc later for matrix.  Add [mat_eqA] to
       be able to use rewrite [mat_mult_id_l]. *)

    Add Parametric Relation m n : (matrix m n) (@mat_eqA m n)
      reflexivity proved by (@mat_eqA_refl m n)
      symmetry proved by (@mat_eqA_sym m n)
        transitivity proved by (@mat_eqA_trans m n)
          as mat_eqA_rel.

    (* Define this morphism to be able to use rewrite
    [zero_matrix_mult_l]. *)

    Add Parametric Morphism m n i (h:i<n) : (fun M => @get_col m n M i h)
      with signature (@mat_eqA m n) ==> (@eq_vec m)
        as get_col_mor.
    Proof.
      intros. unfold eq_vec. apply Vforall2n_intro. intros.
      repeat rewrite <- get_elem_swap. apply H.
    Qed.

    (* Define this morphism to be able to use [rewrite H0] in
    [mat_vec_prod_mor]. *)
    Add Parametric Morphism n : (@vec_to_col_mat n)
      with signature (@eq_vec n) ==> (@mat_eqA n 1)
        as vec_to_col_mat_mor.

    Proof.
      unfold vec_to_col_mat, mat_eqA, get_elem. intros.
      repeat rewrite get_elem_swap. unfold get_col. repeat rewrite Vnth_map.
      apply (Vnth_mor eqA). rewrite (eq_vec_cons eqA). intuition.
      apply (Vnth_mor eqA). hyp.
    Qed.

    (* Define this morphism to be able to use [rewrite H] for
    [mat_vec_prod_mor]. *)
    Add Parametric Morphism m n p : (@mat_mult m n p)
      with signature (@mat_eqA m n) ==> (@mat_eqA n p) ==> (@mat_eqA m p)
        as mat_mult_mor.
      
    Proof.
      unfold mat_mult. intros. unfold mat_eqA. intros.
      repeat rewrite mat_build_elem. apply dot_product_mor.
      apply get_row_mor. hyp. apply get_col_mor. hyp.
    Qed.

    (* Define this morphism to be able to rewrite
    [mat_vec_prod_distr_vec] later. *)
    Add Parametric Morphism m n : (@mat_vec_prod m n)
      with signature (@mat_eqA m n) ==> (@eq_vec n) ==> (@eq_vec m)
        as mat_vec_prod_mor.
    Proof.
      unfold mat_vec_prod. intros. apply get_col_mor. rewrite H. rewrite H0.
      refl.
    Qed.
    
    Notation vec := (vector AN dim).
    Notation eq_vec_st := (@eq_vec_st _ _ sid_theoryAN dim).
    Notation mat_eqA := (@mat_eqA dim dim).
    Notation mat_eqA_st := (@mat_eqA_st dim dim). 
    Notation matrixInt := (matrixInt matrix).
    Notation mint := (matrixInt dim).
    Notation mat := (matrix dim dim).
    Notation eq_vec_st' := (@eq_vec_st _ _ sid_theoryAN dim).
    Notation eq_vec_mat_eqA_st' := (@VecEq.eq_vec_st _ _ mat_eqA_st).
    Notation eq_vec := (@eq_vec dim).
    Notation "x =v y" := (eq_vec x y)(at level 70).
    Notation "x >>= y" := (geN x y) (at level 70).
    Infix "[+]" := vector_plus (at level 50).
    Infix "<*>" := mat_mult (at level 40).

    Add Parametric Relation k : (vector vec k) (@VecEq.eq_vec _ eq_vec k)
      reflexivity proved by (@eq_vec_refl _ _ eq_vec_st k)
      symmetry proved by (@eq_vec_sym _ _ eq_vec_st k)
        transitivity proved by (@eq_vec_trans _ _ eq_vec_st k)
          as eq_vec_eq_vec_rel.
    
    Add Parametric Relation k : (vector (matrix dim dim) k)
      (@VecEq.eq_vec _ mat_eqA k)
      reflexivity proved by (@eq_vec_refl _ _ mat_eqA_st k)
      symmetry proved by (@eq_vec_sym _ _ mat_eqA_st k)
        transitivity proved by (@eq_vec_trans _ _ mat_eqA_st k)
          as eq_vec_mat_eqA_rel.
    
    Definition eq_mint k (mi1 mi2 : mint k) :=
      let (c1, args1) := mi1 in
        let (c2, args2) := mi2 in
          c1 =v c2 /\ VecEq.eq_vec mat_eqA args1 args2.
   
    Notation "x =i y" := (eq_mint x y) (at level 70).
    
    Lemma eq_mint_refl : forall k (x : mint k), x =i x.
      
    Proof.
      unfold eq_mint. destruct x. intuition.
    Qed.

    Lemma eq_mint_sym : forall k (x y : mint k), x =i y -> y =i x.

    Proof.
      unfold eq_mint. destruct x. destruct y. intuition.
    Qed.

    Lemma eq_mint_trans : forall k (x y z : mint k),
      x =i y -> y =i z -> x =i z.

    Proof.
      unfold eq_mint. destruct x. destruct y. destruct z.
      intuition.
      trans const1; hyp. trans args1; hyp.
    Qed.

    Add Parametric Relation k : (@mint k) (@eq_mint k)
      reflexivity proved by (@eq_mint_refl k)
      symmetry proved by (@eq_mint_sym k)
        transitivity proved by (@eq_mint_trans k)
          as eq_mint_rel.
    
    Add Parametric Morphism k : (@mkMatrixInt matrix dim k)
      with signature eq_vec ==> (@VecEq.eq_vec _ mat_eqA k) ==> (@eq_mint k)
        as mkMatrixInt_mor.

    Proof.
      unfold eq_mint. auto.
    Qed.

    Add Parametric Morphism k : (@const matrix dim k)
      with signature (@eq_mint k) ==>  eq_vec as const_mor.

    Proof.
      destruct x. destruct y. simpl. intuition.
    Qed.

    Add Parametric Morphism k : (@args matrix dim k)
      with signature (@eq_mint k) ==> (@VecEq.eq_vec _ mat_eqA k) as args_mor.

    Proof.
      destruct x. destruct y. simpl. intuition.
    Qed.

    Section MBI.

      Definition vec_at0 (v : vec) := Vnth v dim_pos.
      Definition dom := { v : vec | vec_invariant v }.

      Definition dom2vec (d : dom) : vec := proj1_sig d.

      Definition add_matrices i m n (v : vector (matrix m n) i) := 
        Vfold_left (@mat_plus m n) (zero_matrix m n) v.

      Definition mi_eval_aux n (mi : mint n) (v : vector vec n) : vec :=
        add_vectors (n:=dim) (k:=n)(Vmap2 (@mat_vec_prod dim dim)
          (args mi) v) [+] const mi.

      Add Parametric Morphism n : (@mi_eval_aux n)
        with signature (@eq_mint n) ==> (@VecEq.eq_vec _ eq_vec n) ==> eq_vec
          as mi_eval_aux_mor.

      Proof.
        unfold mi_eval_aux. intuition. apply vector_plus_mor.
        apply add_vectors_mor.
        apply Vforall2n_intro. intros. repeat rewrite Vnth_map2.
        apply mat_vec_prod_mor.
        apply (Vnth_mor mat_eqA). rewrite H. refl.
        apply (Vnth_mor eq_vec). hyp.
        rewrite H. refl.
      Qed.

      Variable m : MatrixMethodConf.

      Variable mi_eval_ok : forall f v,
        vec_invariant (mi_eval_aux (trsInt m f) (Vmap dom2vec v)).

      Definition mi_eval f (v : vector dom (ASignature.arity f)) : dom :=
        exist (fun v => vec_invariant v) (mi_eval_aux (trsInt m f)
          (Vmap dom2vec v)) (mi_eval_ok f v).

      Lemma mi_eval_cons : forall n (mi : mint (S n)) v vs,
        mi_eval_aux mi (Vcons v vs) =v
        mat_vec_prod (Vhead (args mi)) v [+] 
        mi_eval_aux (mkMatrixInt (const mi) (Vtail (args mi))) vs.

      Proof.
        intros. unfold mi_eval_aux. simpl. rewrite vector_plus_assoc.
        apply vector_plus_mor. apply vector_plus_comm. refl.
      Qed.
      
      Definition dom_zero: dom.

      Proof.
        exists (Vreplace (Vconst A0 dim) dim_pos A1).
        apply inv_id_matrix.
      Defined.

      Definition I := @mkInterpretation Sig dom dom_zero mi_eval.

      Infix ">=v" := vec_ge (at level 70).

      Definition succeq (x y : dom) := (dom2vec x) >=v (dom2vec y).

      Lemma refl_succeq : reflexive succeq.
        
      Proof.
        intro x. apply vec_ge_refl.
      Qed.

      Lemma trans_succeq : transitive succeq.
        
      Proof.
        unfold succeq. apply Rof_trans with (f:=dom2vec).
        apply vec_ge_trans.
      Qed.

      (** Monotonicity *)

      Section VecMonotonicity_nat.

        Variable f : matrix dim dim -> vec -> vec.
        Variable f_mon : forall M v1 v2,
          v1 >=v v2 -> f M v1 >=v f M v2.
        Variables (a b : vec).

        Lemma vec_add_weak_monotone_map2 : forall n1 (v1 : vector vec n1) n2 
          (v2 : vector vec n2) n (M : vector (matrix dim dim) n) i_j, a >=v b ->
          add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons a v2)) i_j)) >=v 
          add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons b v2)) i_j)).

        Proof.
          induction v1; intros; simpl.
          destruct n; try solve [NatUtil.absurd_arith].
          unfold add_vectors, succeq, vec_ge. simpl. apply Vforall2n_intro. 
          intros. unfold vector_plus. do 2 rewrite Vnth_map2.
          assert (Vnth (f (Vhead M) a) ip >>= Vnth (f (Vhead M) b) ip).
          apply Vforall2n_nth. apply f_mon. hyp.
          apply plus_ge_compat. apply ge_refl. hyp.
          destruct n0; try solve [NatUtil.absurd_arith].
          unfold add_vectors, succeq, vec_ge. simpl. apply Vforall2n_intro. 
          intros. unfold vector_plus. do 2 rewrite Vnth_map2.
          apply plus_ge_compat. 
          apply Vforall2n_nth. unfold add_vectors in IHv1. apply IHv1.
          hyp. apply ge_refl.
        Qed.
        
      End VecMonotonicity_nat.

      Lemma monotone_succeq : monotone I succeq.

      Proof.
        intros f i j i_j vi vj a b ab.
        simpl. unfold mi_eval, mi_eval_aux, succeq. simpl.
        apply (@vec_plus_ge_compat_r dim).
        do 2 rewrite Vmap_cast. do 2 rewrite Vmap_app. simpl.
        apply vec_add_weak_monotone_map2; trivial.
        intros. unfold succeq, vec_ge. apply Vforall2n_intro. intros.
        unfold Matrix2.mat_vec_prod. do 2 rewrite Vnth_col_mat.
        apply mat_mult_mon.
        apply mat_ge_refl. intros x y xp yp.
        do 2 rewrite vec_to_col_mat_spec.
        apply Vforall2n_nth. hyp.
      Qed.

      Lemma succeq_dec : rel_dec succeq.
        
      Proof.
        intros x y. unfold succeq, vec_ge. apply Vforall2n_dec.
        intros m1 n. apply ge_dec.
      Defined.

      (** Decidability of order on terms induced by matrix interpretations. *)

      Section OrderDecidability_nat.

        Require Import ABterm.
        
        Notation bterm := (bterm Sig).

        (** Symbolic computation of term interpretation. *)

        Definition mat_matrixInt_prod n M (mi : mint n) : mint n := 
          mkMatrixInt (mat_vec_prod M (const mi)) 
          (Vmap (mat_mult M) (args mi)).

        Definition combine_matrices n k (v : vector (vector mat k) n) :=
          Vbuild (fun i ip => add_matrices (Vmap (fun v => Vnth v ip) v)).

        Lemma combine_matrices_nil : forall i,
          combine_matrices Vnil = Vconst (@zero_matrix dim dim) i.
          
        Proof.
          intros. apply Veq_nth. intros. unfold combine_matrices.
          rewrite Vnth_const. rewrite Vbuild_nth. trivial.
        Qed.

        Lemma combine_matrices_cons :
          forall k n v (vs : vector (vector mat k) n),
            combine_matrices (Vcons v vs) =
            Vmap2 (@mat_plus  _ _) (combine_matrices vs) v.

        Proof.
          intros. apply Veq_nth. intros.
          unfold combine_matrices, add_matrices. simpl.
          rewrite Vnth_map2. do 2 rewrite Vbuild_nth. refl.
        Qed.

        Fixpoint mi_of_term k (t : bterm k) : mint (S k) :=
          match t with
            | BVar i ip => 
              let zero_int := Vconst (zero_matrix dim dim) (S k) in
                let args_int := Vreplace zero_int (le_lt_S ip)
                  (id_matrix dim) in
                  mkMatrixInt (@zero_vec dim) args_int
            | BFun f v => 
              let f_int := trsInt m f in
                let args_int := Vmap (@mi_of_term k) v in
                  let args_int' := Vmap2 (@mat_matrixInt_prod (S k)) 
                    (args f_int) args_int in
                    let res_const := add_vectors (Vcons (const f_int) 
                      (Vmap (@const matrix dim (S k)) args_int')) in
                    let res_args := combine_matrices
                      (Vmap (@args matrix dim (S k)) args_int') in
                    mkMatrixInt res_const res_args
          end.

        Require Import ATrs.

        Definition rule_mi r :=
          let mvl := maxvar (lhs r) in
            let mvr := maxvar (rhs r) in
              let m := max mvl mvr in
                let lt := inject_term (le_max_l mvl mvr) in
                  let rt := inject_term (le_max_r mvl mvr) in
                    (mi_of_term lt, mi_of_term rt).

        (** Order characteristic for symbolically computed interpretation and 
           its decidability. *)

        Notation mat_ge := (@mat_ge dim dim).

        Definition mint_ge n (l r : mint n) := 
          Vforall2n mat_ge (args l) (args r) /\
          (@vec_ge dim) (const l) (const r).

        Definition term_ord (ord : forall n, relation (mint n)) l r :=
          let (li, ri) := rule_mi (mkRule l r) in
            ord _ li ri.

        Variable mint_gt : forall n (l r : mint n), Prop.
        Variable mint_gt_dec : forall n, rel_dec (@mint_gt n).

        Definition term_ge := term_ord mint_ge.
        Definition term_gt := term_ord mint_gt.

        Lemma mint_ge_dec : forall n, rel_dec (@mint_ge n).

        Proof.
          intros n x y. unfold mint_ge.
          destruct (Vforall2n_dec (@mat_ge_dec dim dim) (args x) (args y)); 
            intuition.
          destruct (vec_ge_dec (const x) (const y)); intuition.
        Defined.

        Lemma term_ge_dec : rel_dec term_ge.
          
        Proof.
          intros l r. unfold term_ge, term_ord. simpl.
          match goal with |- {mint_ge ?l ?r} + {~mint_ge ?l ?r} => 
            destruct (mint_ge_dec l r); auto
          end.
        Defined.

        Lemma term_gt_dec : rel_dec term_gt.
          
        Proof.
          intros l r. unfold term_gt, term_ord. simpl.
          match goal with |- {mint_gt ?l ?r} + {~mint_gt ?l ?r} => 
            destruct (mint_gt_dec l r); auto
          end.
        Defined.

        Notation IR_succeq := (IR I succeq).

        Definition mint_eval (val : valuation I) k (mi : mint k) : vec :=
          let coefs := Vbuild (fun i (ip : i < k) => dom2vec (val i)) in
            add_vectors (Vcons (const mi)
              (Vmap2 (@mat_vec_prod dim dim) (args mi) coefs)).

        Add Parametric Morphism val k : (@mint_eval val k)
          with signature (@eq_mint k) ==> eq_vec
            as mint_eval_mor.

        Proof.
          unfold eq_mint. intros [c1 args1] [c2 args2]. intuition.
          unfold mint_eval. simpl. apply add_vectors_mor.
          rewrite (eq_vec_cons eq_vec). intuition.
          apply Vmap2_mor with (eqA := mat_eqA) (eqB := eq_vec).
          apply eq_vec_st. apply mat_vec_prod_mor. hyp.
          apply eq_vec_refl. apply eq_vec_st.
        Qed.

        Lemma mint_eval_split : forall val k (mi : mint k),
          let coefs := Vbuild (fun i (ip : i < k) => dom2vec (val i)) in
            mint_eval val mi =v const mi [+] 
            add_vectors (Vmap2 (@mat_vec_prod dim dim) (args mi) coefs).

        Proof.
          intros. unfold mint_eval, add_vectors. simpl.
          rewrite vector_plus_comm. refl.
        Qed.
        
        Hint Rewrite mat_mult_id_l zero_matrix_mult_l using simpl : arith.

        Lemma mint_eval_var_aux : forall M i k (v : vector vec k) (ip : i < k),
          add_vectors (Vmap2 (@mat_vec_prod dim dim) (Vreplace (Vconst 
            (zero_matrix dim dim) k) ip M) v) =v
          col_mat_to_vec (M <*> (vec_to_col_mat (Vnth v ip))).

        Proof.
          induction i; intros.
          destruct k. NatUtil.absurd_arith.
          unfold add_vectors. simpl.
          fold (add_vectors (Vmap2 (@mat_vec_prod dim dim)
            (Vconst (zero_matrix dim dim) k) (Vtail v))).
          assert (add_vectors (Vmap2 (@mat_vec_prod dim dim) (Vconst
            (zero_matrix dim dim) k) (Vtail v))
          =v @zero_vec dim).
          Focus 2. rewrite H.
          rewrite vector_plus_zero_l. unfold mat_vec_prod.
          replace (Vhead v) with (Vnth v ip).
          refl.
          rewrite Vhead_nth. rewrite (NatUtil.lt_unique (Lt.lt_O_Sn k) ip).
          refl.
          apply add_vectors_zero. apply Vforall_nth_intro. intros.
          rewrite Vnth_map2. rewrite Vnth_const.
          unfold mat_vec_prod.
          rewrite zero_matrix_mult_l.
          apply Vforall2n_intro. intros. rewrite Vnth_col_mat.
          unfold zero_matrix, zero_vec.
          rewrite mat_build_elem. rewrite Vnth_const. refl.
          destruct k. NatUtil.absurd_arith.
          rewrite Vreplace_tail. simpl. rewrite add_vectors_cons.
          unfold mat_vec_prod at 1. rewrite zero_matrix_mult_l.
          assert (col_mat_to_vec (zero_matrix dim 1) =v zero_vec dim).
          apply Vforall2n_intro. intros. rewrite Vnth_col_mat.
          unfold zero_matrix, zero_vec.
          rewrite mat_build_elem. rewrite Vnth_const. refl. rewrite H.
          rewrite vector_plus_zero_l. rewrite IHi. rewrite Vnth_tail.
          rewrite (NatUtil.le_unique (Lt.lt_n_S (Lt.lt_S_n ip)) ip). refl.
        Qed.

        Lemma mint_eval_eq_term_int_var : forall v (val : valuation I) k 
          (t_b : maxvar_le k (Var v)),
          dom2vec (bterm_int val (inject_term t_b)) =v 
          mint_eval val (mi_of_term (inject_term t_b)).

        Proof.
          intros. rewrite mint_eval_split.
          change (const (mi_of_term (inject_term t_b))) with (zero_vec dim).
          rewrite vector_plus_zero_l.
          change (args (mi_of_term (inject_term t_b))) with (Vreplace (Vconst 
            (zero_matrix dim dim) (S k)) (NatUtil.le_lt_S (maxvar_var t_b)) 
          (id_matrix dim)).
          rewrite mint_eval_var_aux. rewrite Vbuild_nth. simpl.
          trans (col_mat_to_vec (vec_to_col_mat (dom2vec (val v)))).
          rewrite col_mat_to_vec_idem. refl. apply get_col_mor.
          rewrite mat_mult_id_l. refl. ded dim_pos. auto.
        Qed.

        Hint Rewrite vector_plus_zero_l vector_plus_zero_r add_vectors_cons : arith.

        Lemma mint_eval_const : forall val k (c : vec),
          mint_eval (k:=k) val (mkMatrixInt c (combine_matrices Vnil)) =v c.

        Proof.
          intros. unfold mint_eval. simpl. autorewrite with arith.
          trans (c [+] @zero_vec dim). apply vector_plus_mor. refl.
          apply add_vectors_zero. apply Vforall_nth_intro. intros.
          rewrite Vnth_map2. rewrite combine_matrices_nil. rewrite Vnth_const.
          unfold Matrix2.mat_vec_prod. apply Vforall2n_intro. intros.
          rewrite Vnth_col_mat.
          trans (get_elem (zero_matrix dim 1) ip0 access_0).
          apply get_elem_mor. apply zero_matrix_mult_l.
          unfold zero_matrix. rewrite mat_build_elem.
          unfold zero_vec. rewrite Vnth_const. refl.
          apply vector_plus_zero_r.
        Qed.

        Lemma mint_eval_cons : forall n k val c_hd c_tl a_hd 
          (a_tl : vector (vector mat k) n),
          mint_eval val (mkMatrixInt (c_hd [+] c_tl)
            (combine_matrices (Vcons a_hd a_tl))) =v
          mint_eval val (mkMatrixInt c_hd a_hd) [+]
          mint_eval val (mkMatrixInt c_tl (combine_matrices a_tl)).

        Proof.
          intros. unfold mint_eval. simpl.
          set (vali := Vbuild (A := vec) (fun i (_ : i < k) => dom2vec (val i))).
          rewrite combine_matrices_cons.
          autorewrite with arith. repeat rewrite <- vector_plus_assoc.
          apply vector_plus_mor. refl. rewrite vector_plus_assoc.
          rewrite (vector_plus_comm _ c_tl). rewrite <- vector_plus_assoc.
          apply vector_plus_mor. refl. apply add_vectors_split. intros.
          repeat rewrite Vnth_map2. rewrite vector_plus_comm.
          apply mat_vec_prod_distr_mat.
        Qed.

        Lemma mint_eval_mult_factor : forall k val M (mi : mint k),
          mint_eval val (mat_matrixInt_prod M mi) =v
          mat_vec_prod M (mint_eval val mi).

        Proof.
          unfold mint_eval. intros. simpl. autorewrite with arith.
          rewrite mat_vec_prod_distr_vec. apply vector_plus_mor. refl.
          set (gen := Vbuild (A:=vec) (fun i (_ : i < k) => dom2vec (val i))).
          rewrite (mat_vec_prod_distr_add_vectors M 
            (Vmap2 (@mat_vec_prod dim dim) (args mi) gen)
            (Vmap2 (@mat_vec_prod dim dim) (Vmap (mat_mult M) (args mi)) gen)).
          refl. intros. repeat rewrite Vnth_map2. rewrite Vnth_map.
          unfold Matrix2.mat_vec_prod. rewrite vec_to_col_mat_idem.
          apply get_col_mor. rewrite mat_mult_assoc. refl.
        Qed.

        Lemma mint_eval_eq_bterm_int_fapp : forall k i fi val 
          (v : vector (bterm k) i),
          let arg_eval := Vmap2 (@mat_matrixInt_prod (S k)) (args fi) 
            (Vmap (@mi_of_term k) v) in
            mi_eval_aux fi (Vmap 
              (fun t : bterm k => mint_eval val (mi_of_term t)) v) =v
            mint_eval val (mkMatrixInt
              (add_vectors (Vcons (const fi) (Vmap 
                (@const matrix dim (S k)) arg_eval)))
              (combine_matrices (Vmap (@args matrix dim (S k)) arg_eval))).

        Proof.
          induction i; intros.
          (* i = 0 *)
          VOtac. simpl.
          unfold mi_eval_aux, add_vectors. simpl. autorewrite with arith.
          sym. apply mint_eval_const.
          (* i > 0 *)
          VSntac v. simpl mi_eval_aux.
          rewrite mi_eval_cons. 
          rewrite IHi. simpl.
          trans (@mint_eval val (S k)
            (@mkMatrixInt matrix dim (S k)
              (@Matrix2.mat_vec_prod dim dim
                (@Vhead (matrix dim dim) i
                  (@args matrix dim (S i) fi))
                (@const matrix dim (S k)
                  (@Vhead (mint (S k)) i
                    (@Vmap (ABterm.bterm Sig k)
                      (mint (S k))
                      (@mi_of_term k) (S i) v)))
                [+] @add_vectors dim (S i) (@Vcons (vector A dim)
                  (@const matrix dim (S i) fi) i
                  (@Vmap (mint (S k)) 
                    (vector A dim) (@const matrix dim (S k)) i
                    (@Vmap2 (matrix dim dim)
                      (mint (S k))
                      (mint (S k))
                      (@mat_matrixInt_prod (S k)) i
                      (@Vtail (matrix dim dim) i
                        (@args matrix dim (S i) fi))
                      (@Vtail (mint (S k)) i
                        (@Vmap (ABterm.bterm Sig k)
                          (mint (S k))
                          (@mi_of_term k) (S i) v))))))
              (@combine_matrices (S i) (S k)
                (@Vcons (vector (matrix dim dim) (S k))
                  (@Vmap (matrix dim dim) (matrix dim dim)
                    (@mat_mult dim dim dim
                      (@Vhead (matrix dim dim) i
                        (@args matrix dim (S i) fi))) 
                    (S k)
                    (@args matrix dim (S k)
                      (@Vhead (mint (S k)) i
                        (@Vmap (ABterm.bterm Sig k)
                          (mint (S k))
                          (@mi_of_term k) (S i) v)))) i
                  (@Vmap (mint (S k))
                    (vector (matrix dim dim) (S k))
                    (@args matrix dim (S k)) i
                    (@Vmap2 (matrix dim dim)
                      (mint (S k))
                      (mint (S k))
                      (@mat_matrixInt_prod (S k)) i
                      (@Vtail (matrix dim dim) i
                        (@args matrix dim (S i) fi))
                      (@Vtail (mint (S k)) i
                        (@Vmap (ABterm.bterm Sig k)
                          (mint (S k))
                          (@mi_of_term k) (S i) v)))))))).
          Focus 2. apply mint_eval_mor. split. rewrite add_vectors_perm.
          rewrite (add_vectors_cons (i := S i) (mat_vec_prod (Vhead (args fi))
            (const (Vhead (Vmap (mi_of_term (k:=k)) v))))). refl.
          apply eq_vec_refl. apply mat_eqA_st.
          rewrite mint_eval_cons. apply vector_plus_mor.
          Focus 2. rewrite Vmap_tail. refl.
          rewrite H. simpl.
          fold (mat_matrixInt_prod (Vhead (args fi)) (mi_of_term (Vhead v))).
          sym. apply mint_eval_mult_factor.
        Qed.

        Lemma mint_eval_eq_bterm_int : forall (val : valuation I) t k 
          (t_b : maxvar_le k t),
          dom2vec (bterm_int val (inject_term t_b)) =v
          mint_eval val (mi_of_term (inject_term t_b)).

        Proof.
          intros val t. pattern t. apply term_ind_forall; intros.
          apply mint_eval_eq_term_int_var.
          rewrite inject_term_eq. simpl.
          rewrite Vmap_map.
          rewrite (@Vmap_eqA _ _ eq_vec eq_vec_st
            (fun x => dom2vec (bterm_int val x)) 
            (fun (t : bterm k) => mint_eval val (mi_of_term t))).
          simpl. apply mint_eval_eq_bterm_int_fapp.
          apply Vforall_nth_intro. intros.
          rewrite inject_terms_nth. apply (Vforall_nth ip H).
        Qed.

        Lemma mint_eval_eq_term_int : forall t (val : valuation I) k
          (t_b : maxvar_le k t),
          dom2vec (term_int val t) =v
          mint_eval val (mi_of_term (inject_term t_b)).

        Proof.
          intros. rewrite <- (term_int_eq_bterm_int val t_b).
          apply mint_eval_eq_bterm_int.
        Qed.

        Lemma mint_eval_equiv : forall l r (val : valuation I),
          let (li, ri) := rule_mi (mkRule l r) in
            let lev := term_int val l in
              let rev := term_int val r in
                let lv := mint_eval val li in
                  let rv := mint_eval val ri in
                    lv =v dom2vec lev /\ rv =v dom2vec rev.

        Proof.
          intros. simpl. split.
          rewrite (mint_eval_eq_term_int val (le_max_l (maxvar l) (maxvar r))).
          refl.
          rewrite (mint_eval_eq_term_int val (le_max_r (maxvar l) (maxvar r))).
          refl.
        Qed.

        Lemma mint_eval_mon_succeq_args : forall k (val : vector vec k) 
          (mi mi' : mint k), mint_ge mi mi' -> 
          add_vectors (Vmap2 (@mat_vec_prod dim dim) (args mi) val) >=v 
          add_vectors (Vmap2 (@mat_vec_prod dim dim) (args mi') val).

        Proof.
          destruct mi. gen val. clear val. induction args0. intros.
          destruct mi'. VOtac. 
          unfold mint_eval, add_vectors. simpl.
          apply (vec_ge_refl (@zero_vec dim)).
          intros. destruct mi'. VSntac args1.
          unfold mint_eval, add_vectors. simpl.
          destruct H. apply (@vec_plus_ge_compat dim).
          apply (IHargs0 (Vtail val) (mkMatrixInt const1 (Vtail (args1)))).
          split. simpl. change args0 with (Vtail (Vcons h args0)). 
          apply Vforall2n_tail. hyp. hyp.
          apply mat_vec_prod_ge_compat.
          change h with (Vhead (Vcons h args0)). do 2 rewrite Vhead_nth.
          apply Vforall2n_nth. hyp.
          apply (vec_ge_refl (Vhead val)).
        Qed.

        Lemma mint_eval_mon_succeq : forall (val : valuation I) k 
          (mi mi' : mint k), mint_ge mi mi' -> 
          mint_eval val mi >=v mint_eval val mi'.

        Proof.
          intros. unfold mint_eval, add_vectors. simpl.
          apply (@vec_plus_ge_compat dim).
          exact (mint_eval_mon_succeq_args _ H).
          destruct H. hyp.
        Qed.

        Lemma term_ge_incl_succeq : term_ge << IR_succeq.

        Proof.
          intros l r lr v. destruct (mint_eval_equiv l r v). simpl in * .
          unfold succeq.
          rewrite <- (vec_ge_mor H H0).
          apply mint_eval_mon_succeq. hyp.
        Qed.

        Definition succeq' := term_ge.
        Definition succeq'_sub := term_ge_incl_succeq.
        Definition succeq'_dec := term_ge_dec.

      End OrderDecidability_nat.
    End MBI.
  End MatrixBasedInt_nat.
End S.
