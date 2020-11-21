(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frédéric Blanqui, 2009-03-25 (setoid), 2014-02-25 (classes)
- Adam Koprowski and Johannes Waldmann, 2008-01
*)

Set Implicit Arguments.

Require Import OrdSemiRing2 VecUtil Matrix2 AMonAlg VecArith2
  Structures.Equalities LogicUtil Morphisms RelUtil NatUtil
  AWFMInterpretation Max.

Section S.

  Context {OSR : OrderedSemiRing}.

  Import OSR_Notations.

  Record matrixInt (dim argCnt : nat) := {
    const : vector s_typ dim;
    args  : vector (matrix dim dim) argCnt }.

  Variable Sig: Signature.

  (* REMARK: make dim as a parameter *)

  Variable dim      : nat.
  Parameter dim_pos : dim > 0.

  Class TMatrixInt := {
    mi_trsInt : forall f : Sig, matrixInt dim (arity f) }.

  Class MatrixMethodConf := {
    mic_mi            :> TMatrixInt;
    mic_vec_invariant : vector s_typ dim -> Prop;
    mic_inv_id_matrix : mic_vec_invariant (id_vec dim_pos) }.

Section MatrixBasedInt.

  Context {MC : MatrixMethodConf}.

  Notation vec     := (vector s_typ dim).
  Notation eq_vec  := (Vforall2 s_eq (n:= dim)).
  Infix "=v"       := eq_vec (at level 70).
  Notation vec_ge  := (Vforall2 osr_ge (n:= dim)).
  Infix ">=v"      := vec_ge (at level 70).
  Notation mat     := (matrix dim dim).
  Notation mat_eqA := (mat_eqA dim dim).
  Notation mint    := (matrixInt dim).

  (*REMOVE?*)
  Global Instance eq_vec_eq_vec_rel k : Equivalence (Vforall2 eq_vec (n:=k)).

  Proof. class. Qed.

  Global Instance eq_vec_mat_eqA_rel k : Equivalence (Vforall2 mat_eqA (n:=k)).

  Proof. class. Qed.
  
  Definition eq_mint k (mi1 mi2 : mint k) :=
    let (c1, args1) := mi1 in
    let (c2, args2) := mi2 in
      c1 =v c2 /\ Vforall2 mat_eqA args1 args2.

  Notation "x =i y" := (eq_mint x y) (at level 70).

  Global Instance eq_mint_refl k : Reflexive (@eq_mint k).

  Proof. unfold eq_mint, Reflexive. destruct x. intuition. Qed.

  Global Instance eq_mint_sym k : Symmetric (@eq_mint k).

  Proof. unfold eq_mint, Symmetric. destruct x. destruct y. intuition. Qed.

  Global Instance eq_mint_trans k : Transitive (@eq_mint k).

  Proof.
    unfold eq_mint, Transitive. destruct x. destruct y. destruct z. intuition.
    trans const1; hyp. trans args1; hyp.
  Qed.

  (*REMOVE?*)
  Global Instance eq_mint_equiv k : Equivalence (@eq_mint k).

  Proof. constructor; class. Qed.
 
  Global Instance build_matrixInt_mor k :
    Proper (eq_vec ==> Vforall2 mat_eqA ==> @eq_mint k)
    (@Build_matrixInt dim k).

  Proof. intros v v' vv' ms ms' msms'. unfold eq_mint. intuition. Qed.

  Global Instance const_mor k :
    Proper (@eq_mint k ==> eq_vec) (@const dim k).

  Proof. destruct x. destruct y. simpl. intuition. Qed.

  Global Instance args_mor k :
    Proper (@eq_mint k ==> Vforall2 mat_eqA) (@args dim k).

  Proof. destruct x. destruct y. simpl. intuition. Qed.

  Section MBI.
        
    Definition dom := { v : vec | mic_vec_invariant v }.

    Definition dom2vec (d : dom) : vec := proj1_sig d.

    Definition add_matrices i m n (v : vector (matrix m n) i) := 
      Vfold_left (@mat_plus _ m n) (@zero_matrix _ m n) v.

    Definition mi_eval_aux n (mi : mint n) (v : vector vec n) : vec :=
      add_vectors (Vmap2 (@mat_vec_prod _ _ _) (args mi) v) [+] const mi.

    Global Instance mi_eval_aux_mor n :
      Proper (@eq_mint n ==> Vforall2 eq_vec ==> eq_vec) (@mi_eval_aux n).

    Proof.
      intros I I' II' v v' vv'. unfold mi_eval_aux. apply vector_plus_mor.
      apply add_vectors_mor. apply Vforall2_intro_nth. intros.
      rewrite !Vnth_map2.
      apply mat_vec_prod_mor. apply Vforall2_elim_nth. rewrite II'. refl.
      apply Vforall2_elim_nth. hyp. rewrite II'. refl.
    Qed.

    Variable mi_eval_ok : forall f v,
      mic_vec_invariant (mi_eval_aux (mi_trsInt f) (Vmap dom2vec v)).

    Definition mi_eval f (v : vector dom (arity f)) : dom :=
      exist mic_vec_invariant (mi_eval_aux (mi_trsInt f) (Vmap dom2vec v))
            (mi_eval_ok f v).

    Lemma mi_eval_cons : forall n (mi : mint (S n)) v vs,
      mi_eval_aux mi (Vcons v vs) =v
        mat_vec_prod (Vhead (args mi)) v [+] 
        mi_eval_aux (Build_matrixInt (const mi) (Vtail (args mi))) vs.

    Proof.
      intros. unfold mi_eval_aux. simpl. rewrite vector_plus_assoc.
      apply vector_plus_mor. apply vector_plus_comm. refl.
    Qed.
  
    Definition dom_zero : dom.

    Proof. exists (id_vec dim_pos). apply mic_inv_id_matrix. Defined.

    Definition I := @mkInterpretation Sig dom dom_zero mi_eval.

    Definition succeq := Rof (Vforall2 osr_ge) dom2vec.

    Global Instance refl_succeq : Reflexive succeq.
      
    Proof. intro x. unfold succeq, Rof. refl. Qed.

    Global Instance trans_succeq : Transitive succeq.
      
    Proof. apply Rof_trans. class. Qed.

    (** Monotonicity *)
  
    Section VecMonotonicity.
    
      Variable f : matrix dim dim -> vec -> vec.
      Variable f_mon : forall M v1 v2, v1 >=v v2 -> f M v1 >=v f M v2.
      Variables (a b : vec).

      Lemma vec_add_weak_monotone_map2 : forall n1 (v1 : vector vec n1) n2 
        (v2 : vector vec n2) n (M : vector (matrix dim dim) n) i_j, a >=v b ->
        add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons a v2)) i_j)) >=v 
        add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons b v2)) i_j)).

      Proof.
        induction v1; intros; simpl.
        destruct n; try solve [absurd_arith].
        unfold add_vectors, succeq. simpl. apply Vforall2_intro_nth. 
        intros. unfold vector_plus. do 2 rewrite Vnth_map2.
        assert (Vnth (f (Vhead M) a) ip >>= Vnth (f (Vhead M) b) ip).
        apply Vforall2_elim_nth. apply f_mon. hyp.
        apply osr_add_ge. apply osr_ge_refl. hyp.
        destruct n0; try solve [absurd_arith].
        unfold add_vectors, succeq. simpl. apply Vforall2_intro_nth. 
        intros. unfold vector_plus. do 2 rewrite Vnth_map2.
        apply osr_add_ge. 
        apply Vforall2_elim_nth. unfold add_vectors in IHv1. apply IHv1.
        hyp. apply osr_ge_refl.
      Qed.
  
    End VecMonotonicity.

    Lemma monotone_succeq : monotone I succeq.

    Proof.
      intros f i j i_j vi vj a b ab.
      simpl. unfold mi_eval, mi_eval_aux, succeq. simpl. 
      apply vec_plus_ge_compat_r.
      do 2 rewrite Vmap_cast. do 2 rewrite Vmap_app. simpl.
      apply vec_add_weak_monotone_map2; trivial.
      intros. unfold succeq. apply Vforall2_intro_nth. intros.
      unfold mat_vec_prod. do 2 rewrite Vnth_col_mat. apply mat_mult_mon.
      apply mat_ge_refl. intros x y xp yp.
      do 2 rewrite vec_to_col_mat_spec.
      apply Vforall2_elim_nth. hyp.
    Qed.

    Lemma succeq_dec : rel_dec succeq.
  
    Proof.
      intros x y. unfold succeq. apply Vforall2_dec.
      intros m n. apply osr_ge_dec.
    Defined.

    (** decidability of order on terms induced by matrix interpretations *)

    Section OrderDecidability.

      Require Import ABterm.

      Notation bterm := (bterm Sig).

      (** symbolic computation of term interpretation *)

      Definition mat_matrixInt_prod n M (mi : mint n) : mint n := 
        Build_matrixInt (mat_vec_prod M (const mi)) 
                    (Vmap (mat_mult M) (args mi)).

      Definition combine_matrices n k (v : vector (vector mat k) n) :=
        Vbuild (fun i ip => add_matrices (Vmap (fun v => Vnth v ip) v)).

      Lemma combine_matrices_nil : forall i,
        combine_matrices Vnil = Vconst (@zero_matrix _ dim dim) i.
      
      Proof.
        intros. apply Veq_nth. intros. unfold combine_matrices.
        rewrite Vnth_const. rewrite Vbuild_nth. trivial.
      Qed.

      Lemma combine_matrices_cons :
        forall k n v (vs : vector (vector mat k) n),
          combine_matrices (Vcons v vs) =
          Vmap2 (@mat_plus _ _ _) (combine_matrices vs) v.

      Proof.
        intros. apply Veq_nth. intros.
        unfold combine_matrices, add_matrices. simpl.
        rewrite Vnth_map2. do 2 rewrite Vbuild_nth. refl.
      Qed.

      Fixpoint mi_of_term k (t : bterm k) : mint (S k) :=
        match t with
          | BVar i ip => 
            let zero_int := Vconst (@zero_matrix _ dim dim) (S k) in
            let args_int := Vreplace zero_int (le_lt_S ip) (@id_matrix _ dim) in
            Build_matrixInt (@zero_vec _ dim) args_int
          | BFun f v => 
            let f_int := mi_trsInt f in
            let args_int := Vmap (@mi_of_term k) v in
            let args_int' := Vmap2 (@mat_matrixInt_prod (S k)) 
                                   (args f_int) args_int in
            let res_const := add_vectors (Vcons (const f_int) 
              (Vmap (@const dim (S k)) args_int')) in
            let res_args := combine_matrices (Vmap (@args _ _) args_int') in
            Build_matrixInt res_const res_args
        end.

      Require Import ATrs.

      Definition rule_mi r :=
        let mvl := maxvar (lhs r) in
        let mvr := maxvar (rhs r) in
        let m := max mvl mvr in
        let lt := inject_term (le_max_l mvl mvr) in
        let rt := inject_term (le_max_r mvl mvr) in
          (mi_of_term lt, mi_of_term rt).

      (** order characteristic for symbolically computed interpretation and 
       its decidability *)

      Notation mat_ge := (@mat_ge _ dim dim).

      Definition mint_ge n (l r : mint n) := 
        Vforall2 mat_ge (args l) (args r)
        /\ Vforall2 osr_ge (const l) (const r).

      (* Add: Boolean function of [mint_ge]. *)

      Require Import BoolUtil.

      Definition bmint_ge n (l r : mint n) : bool :=
        bVforall2 (bmat_ge (n:=dim))(args l) (args r) &&
                  bVforall2 (fun m n => bge _ m n) (const l) (const r).
      
      (** Add: Correctness proof of [mint_ge] over domain natural numbers. *)

      Lemma bmint_ge_ok : forall n (l r: mint n),
                            bmint_ge l r = true <-> mint_ge l r.
      
      Proof.
        intros n l r. intuition. 
        (* [1]. Proving the <- *)
        unfold bmint_ge in H. rewrite andb_eq in H. destruct H.
        unfold mint_ge. split.
        (* Left part. *)
        rewrite bVforall2_ok in H. apply H.
        (* Proving boolean function of [bmat_ge]. *)
        intros M N. split.
        (* -> *)
        intro H1. apply bmat_ge_ok. hyp.
        (* <- *)
        intro H1. rewrite bmat_ge_ok. hyp.
        (* Right part. *)
        rewrite bVforall2_ok in H0. apply H0.
        (* Proving boolean function of [bge]. *)
        intros x y. split.
        (* -> *)
        intro H1. apply bge_ok. hyp.
        (* <- *)
        intro H1. rewrite bge_ok. hyp.
        (* [2]. Proving the -> *)
        unfold bmint_ge. rewrite andb_eq. split.
        (* Left part. *)
        rewrite bVforall2_ok. unfold mint_ge in H.
        destruct H. apply H.
        (* Proving boolean function of [bmat_ge]. *)
        intros M N. split.
        (* -> *)
        intro H1. apply bmat_ge_ok. hyp.
        (* <- *)
        intro H1. rewrite bmat_ge_ok. hyp.
        (* Right part. *)
        rewrite bVforall2_ok. unfold mint_ge in H.
        destruct H. apply H0.
        (* Proving boolean function of [bge]. *)
        intros x y. split.
        (* -> *)
        intro H1. apply bge_ok. hyp.
        (* <- *)
        intro H1. rewrite bge_ok. hyp.
      Qed.

      Definition term_ord (ord : forall n, relation (mint n)) l r :=
        let (li, ri) := rule_mi (mkRule l r) in ord _ li ri.

      Variable mint_gt : forall n (l r : mint n), Prop.
      Variable mint_gt_dec : forall n, rel_dec (@mint_gt n).

      Definition term_ge := term_ord mint_ge.
      Definition term_gt := term_ord mint_gt.

      Lemma mint_ge_dec : forall n, rel_dec (@mint_ge n).

      Proof.
        intros n x y. unfold mint_ge.
        destruct (Vforall2_dec (@mat_ge_dec _ _ _) (args x) (args y)); 
          intuition.
        destruct (Vforall2_dec osr_ge_dec (const x) (const y)); intuition.
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
        add_vectors (Vcons (const mi) (Vmap2 (@mat_vec_prod _ _ _) (args mi) coefs)).

      Global Instance mint_eval_mor k val :
        Proper (@eq_mint k ==> eq_vec) (@mint_eval val k).

      Proof.
        intros [c1 args1] [c2 args2]. unfold eq_mint. intuition.
        unfold mint_eval. simpl. apply add_vectors_mor.
        rewrite Vforall2_cons_eq. intuition.
        apply Vmap2_proper with (R := mat_eqA) (S := eq_vec).
        apply mat_vec_prod_mor. hyp. refl.
      Qed.

      Lemma mint_eval_split : forall val k (mi : mint k),
        let coefs := Vbuild (fun i (ip : i < k) => dom2vec (val i)) in
          mint_eval val mi =v const mi [+] 
          add_vectors (Vmap2 (@mat_vec_prod _ _ _) (args mi) coefs).

      Proof.
        intros. unfold mint_eval, add_vectors. simpl.
        rewrite vector_plus_comm. refl.
      Qed.

      Lemma mint_eval_var_aux : forall M i k (v : vector vec k) (ip : i < k),
        add_vectors (Vmap2 (@mat_vec_prod _ _ _) (Vreplace (Vconst 
          (@zero_matrix _ dim dim) k) ip M) v) =v
          col_mat_to_vec (M <*> (vec_to_col_mat (Vnth v ip))).

      Proof.
        induction i; intros.
        destruct k. absurd_arith.
        unfold add_vectors. simpl.
        fold (add_vectors (Vmap2 (@mat_vec_prod _ _ _) 
                                 (Vconst (@zero_matrix _ dim dim) k) (Vtail v))).
        assert (add_vectors
          (Vmap2 (@mat_vec_prod _ _ _) (Vconst (@zero_matrix _ dim dim) k) (Vtail v))
          =v @zero_vec _ dim). Focus 2. rewrite H.
        rewrite vector_plus_zero_l.
        replace (Vhead v) with (Vnth v ip). refl.
        rewrite Vhead_nth. rewrite (lt_unique (lt_O_Sn k) ip). refl.
        apply add_vectors_zero. apply Vforall_nth_intro. intros.
        rewrite Vnth_map2. rewrite Vnth_const.
        unfold mat_vec_prod. rewrite zero_matrix_mult_l.
        apply Vforall2_intro_nth. intros. rewrite Vnth_col_mat.
        unfold zero_matrix, zero_vec.
        rewrite mat_build_elem. rewrite Vnth_const. refl.
        destruct k. absurd_arith.
        rewrite Vreplace_tail. simpl. rewrite add_vectors_cons.
        unfold mat_vec_prod at 1. rewrite zero_matrix_mult_l.
        assert (col_mat_to_vec (@zero_matrix _ dim 1) =v @zero_vec _ dim).
        apply Vforall2_intro_nth. intros. rewrite Vnth_col_mat.
        unfold zero_matrix, zero_vec.
        rewrite mat_build_elem. rewrite Vnth_const. refl. rewrite H.
        rewrite vector_plus_zero_l. rewrite IHi. rewrite Vnth_tail.
        rewrite (le_unique (lt_n_S (lt_S_n ip)) ip). refl.
      Qed.

      Lemma mint_eval_eq_term_int_var : forall v (val : valuation I) k 
                                               (t_b : maxvar_le k (Var v)),
        dom2vec (bterm_int val (inject_term t_b)) =v 
        mint_eval val (mi_of_term (inject_term t_b)).

      Proof.
        intros. rewrite mint_eval_split.
        change (const (mi_of_term (inject_term t_b))) with (@zero_vec _ dim).
        rewrite vector_plus_zero_l.
        change (args (mi_of_term (inject_term t_b))) with (Vreplace (Vconst 
          (@zero_matrix _ dim dim) (S k)) (le_lt_S (maxvar_var t_b)) 
          (@id_matrix _ dim)).
        rewrite mint_eval_var_aux. rewrite Vbuild_nth. simpl.
        trans (col_mat_to_vec (vec_to_col_mat (dom2vec (val v)))).
        rewrite col_mat_to_vec_idem. refl. apply get_col_mor.
        rewrite mat_mult_id_l. refl. ded dim_pos. auto.
      Qed.

      Lemma mint_eval_const : forall val k (c : vec),
        mint_eval (k:=k) val (Build_matrixInt c (combine_matrices Vnil)) =v c.

      Proof.
        intros. unfold mint_eval. simpl. autorewrite with arith.
        trans (c [+] @zero_vec _ dim). apply vector_plus_mor. refl.
        apply add_vectors_zero. apply Vforall_nth_intro. intros.
        rewrite Vnth_map2. rewrite combine_matrices_nil. rewrite Vnth_const.
        unfold mat_vec_prod. apply Vforall2_intro_nth. intros.
        rewrite Vnth_col_mat.
        trans (get_elem (@zero_matrix _ dim 1) ip0 access_0).
        apply get_elem_mor. apply zero_matrix_mult_l.
        unfold zero_matrix. rewrite mat_build_elem.
        unfold zero_vec. rewrite Vnth_const. refl.
        apply vector_plus_zero_r.
      Qed.

      Lemma mint_eval_cons : forall n k val c_hd c_tl a_hd 
                                    (a_tl : vector (vector mat k) n),
        mint_eval val (Build_matrixInt (c_hd [+] c_tl)
          (combine_matrices (Vcons a_hd a_tl))) =v
        mint_eval val (Build_matrixInt c_hd a_hd) [+]
        mint_eval val (Build_matrixInt c_tl (combine_matrices a_tl)).

      Proof.
        intros. unfold mint_eval. simpl.
        set (vali := Vbuild (A := vec) (fun i (_ : i < k) => dom2vec (val i))).
        rewrite combine_matrices_cons.
        autorewrite with arith. rewrite <- !vector_plus_assoc.
        apply vector_plus_mor. refl. rewrite vector_plus_assoc.
        rewrite (vector_plus_comm _ c_tl). rewrite <- vector_plus_assoc.
        apply vector_plus_mor. refl. apply add_vectors_split. intros.
        rewrite !Vnth_map2, vector_plus_comm. apply mat_vec_prod_distr_mat.
      Qed.

      Lemma mint_eval_mult_factor : forall k val M (mi : mint k),
        mint_eval val (mat_matrixInt_prod M mi) =v
        mat_vec_prod M (mint_eval val mi).

      Proof.
        unfold mint_eval. intros. simpl. autorewrite with arith.
        rewrite mat_vec_prod_distr_vec. apply vector_plus_mor. refl.
        set (gen := Vbuild (A:=vec) (fun i (_ : i < k) => dom2vec (val i))).
        rewrite (mat_vec_prod_distr_add_vectors M 
          (Vmap2 (@mat_vec_prod _ _ _) (args mi) gen)
          (Vmap2 (@mat_vec_prod _ _ _) (Vmap (mat_mult M) (args mi)) gen)).
        refl. intros. rewrite !Vnth_map2, Vnth_map.
        unfold mat_vec_prod. rewrite vec_to_col_mat_idem.
        apply get_col_mor. rewrite mat_mult_assoc. refl.
      Qed.

      Lemma mint_eval_eq_bterm_int_fapp : forall k i fi val 
                                                 (v : vector (bterm k) i),
        let arg_eval := Vmap2 (@mat_matrixInt_prod (S k)) (args fi) 
          (Vmap (@mi_of_term k) v) in
          mi_eval_aux fi (Vmap 
            (fun t : bterm k => mint_eval val (mi_of_term t)) v) =v
          mint_eval val (Build_matrixInt
            (add_vectors (Vcons (const fi) (Vmap 
              (@const dim (S k)) arg_eval)))
            (combine_matrices (Vmap (@args dim (S k)) arg_eval))).

      Proof.
        induction i; intros.
        (* i = 0 *)
        VOtac. simpl.
        unfold mi_eval_aux, add_vectors. simpl. autorewrite with arith.
        sym. apply mint_eval_const.
        (* i > 0 *)
        VSntac v. simpl mi_eval_aux.
        rewrite mi_eval_cons. rewrite IHi. simpl.
        (* FIXME: morphisms do work here ? *)
        trans (@mint_eval val (S k)
          (@Build_matrixInt dim (S k)
            (@mat_vec_prod _ dim dim
                       (@Vhead (matrix dim dim) i
                          (@args dim (S i) fi))
                       (@const dim (S k)
                          (@Vhead (mint (S k)) i
                             (@Vmap (ABterm.bterm Sig k)
                                (mint (S k))
                                (@mi_of_term k) (S i) v)))
                 [+] @add_vectors _ dim (S i) (@Vcons (vector _ dim)
                     (@const dim (S i) fi) i
                    (@Vmap (mint (S k)) 
                       (vector _ dim) (@const dim (S k)) i
                       (@Vmap2 (matrix dim dim)
                          (mint (S k))
                          (mint (S k))
                          (@mat_matrixInt_prod (S k)) i
                          (@Vtail (matrix dim dim) i
                             (@args dim (S i) fi))
                          (@Vtail (mint (S k)) i
                             (@Vmap (ABterm.bterm Sig k)
                                (mint (S k))
                                (@mi_of_term k) (S i) v))))))
           (@combine_matrices (S i) (S k)
              (@Vcons (vector (matrix dim dim) (S k))
                 (@Vmap (matrix dim dim) (matrix dim dim)
                    (@mat_mult _ dim dim dim
                       (@Vhead (matrix dim dim) i
                          (@args dim (S i) fi))) 
                    (S k)
                    (@args dim (S k)
                       (@Vhead (mint (S k)) i
                          (@Vmap (ABterm.bterm Sig k)
                             (mint (S k))
                             (@mi_of_term k) (S i) v)))) i
                 (@Vmap (mint (S k))
                    (vector (matrix dim dim) (S k))
                    (@args dim (S k)) i
                    (@Vmap2 (matrix dim dim)
                       (mint (S k))
                       (mint (S k))
                       (@mat_matrixInt_prod (S k)) i
                       (@Vtail (matrix dim dim) i
                          (@args dim (S i) fi))
                       (@Vtail (mint (S k)) i
                          (@Vmap (ABterm.bterm Sig k)
                             (mint (S k))
                             (@mi_of_term k) (S i) v)))))))).
        Focus 2. apply mint_eval_mor. split. rewrite add_vectors_perm.
        rewrite (add_vectors_cons (i := S i) (mat_vec_prod (Vhead (args fi))
          (const (Vhead (Vmap (mi_of_term (k:=k)) v))))). refl.
        refl.
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
        rewrite (@Vforall2_map_intro _ _ eq_vec
          (fun x => dom2vec (bterm_int val x)) 
          (fun (t : bterm k) => mint_eval val (mi_of_term t))).
        apply mint_eval_eq_bterm_int_fapp.
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
        add_vectors (Vmap2 (@mat_vec_prod _ _ _) (args mi) val) >=v 
        add_vectors (Vmap2 (@mat_vec_prod _ _ _) (args mi') val).

      Proof.
        destruct mi. gen val. clear val. induction args0. intros.
        destruct mi'. VOtac. 
        unfold mint_eval, add_vectors. simpl. refl.
        intros. destruct mi'. VSntac args1.
        unfold mint_eval, add_vectors. simpl.
        destruct H. apply (@vec_plus_ge_compat _ dim).
        apply (IHargs0 (Vtail val) (Build_matrixInt const1 (Vtail (args1)))).
        split. simpl. change args0 with (Vtail (Vcons h args0)). 
        apply Vforall2_tail. hyp. hyp.
        apply mat_vec_prod_ge_compat.
        change h with (Vhead (Vcons h args0)). do 2 rewrite Vhead_nth.
        apply Vforall2_elim_nth. hyp. refl.
      Qed.

      Lemma mint_eval_mon_succeq : forall (val : valuation I) k 
        (mi mi' : mint k), mint_ge mi mi' -> 
        mint_eval val mi >=v mint_eval val mi'.

      Proof.
        intros. unfold mint_eval, add_vectors. simpl.
        apply (@vec_plus_ge_compat _ dim).
        exact (mint_eval_mon_succeq_args _ H).
        destruct H. hyp.
      Qed.

      Lemma term_ge_incl_succeq : term_ge << IR_succeq.

      Proof.
        intros l r lr v. destruct (mint_eval_equiv l r v). simpl in * .
        unfold succeq, Rof. rewrite <- (vec_ge_mor H H0).
        apply mint_eval_mon_succeq. hyp.
      Qed.

      Definition succeq' := term_ge.
      Definition succeq'_sub := term_ge_incl_succeq.
      Definition succeq'_dec := term_ge_dec.

      (* FIXME: define MonotoneAlgebra for matrix *)

      (* REMARK: does not has succ *)    

    End OrderDecidability.

  End MBI.

End MatrixBasedInt.

End S.
