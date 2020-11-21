(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-23 (setoid)
- Adam Koprowski and Hans Zantema, 2007-03

* Matrices as a functor.
*)

Require Import VecUtil NatUtil LogicUtil Relations List
  Setoid VecEq VecOrd VecArith2 OrdSemiRing2.

Set Implicit Arguments.

Section Matrix.

(***********************************************************************)
(** ** Basic definitions of matrix over domain natural numbers. *)

  Notation A := AN.
  Notation eqA := eqAN.
  Notation sid_theoryA := sid_theoryAN.
  Notation "X =A= Y" := (eqA X Y) (at level 70).
  Notation "v1 =v v2" := (eq_vec v1 v2) (at level 70).
  Notation vec := (vector A).
  Add Setoid A eqA sid_theoryA as A_Setoid.
  Notation A_semi_ring := A_semi_ringN.
  Add Ring Aring : A_semi_ring.
  
  (** Matrix represented by a vector of vectors (in a row-wise fashion). *)

  Definition matrix m n := vector (vec n) m.

  (** Accessors over domain natural numbers. *)

  Definition get_row m n (M : matrix m n) i (ip : i < m) := Vnth M ip.
  Definition get_col m n (M : matrix m n) i (ip : i < n) := 
    Vmap (fun v => Vnth v ip) M.
  Definition get_elem m n (M : matrix m n) i j (ip : i < m) (jp : j < n) :=
    Vnth (get_row M ip) jp.

  Lemma get_elem_swap : forall m n (M : matrix m n) i j (ip : i < m) 
    (jp : j < n), Vnth (get_row M ip) jp = Vnth (get_col M jp) ip.

  Proof.
    induction M; intros. absurd_arith.
    destruct i.
    trivial.
    simpl. rewrite IHM. trivial.
  Qed.

  Add Parametric Relation n : (vec n) (@eq_vec n)
    reflexivity proved by (@eq_vec_refl A eqA sid_theoryA n)
    symmetry proved by (@eq_vec_sym A eqA sid_theoryA n)
      transitivity proved by (@eq_vec_trans A eqA sid_theoryA n)
        as eq_vec_rel.

  Definition mat_eqA m n (M N : matrix m n) :=
    forall i j (ip : i < m) (jp : j < n),
      get_elem M ip jp =A= get_elem N ip jp.

  Notation "M =m N" := (mat_eqA M N) (at level 70).

  Lemma mat_eqA_refl : forall m n (M : matrix m n), M =m M.

  Proof.
    unfold mat_eqA. refl.
  Qed.

  Lemma mat_eqA_sym : forall m n (M N : matrix m n), M =m N -> N =m M.

  Proof.
    unfold mat_eqA. intros. sym. apply H.
  Qed.

  Lemma mat_eqA_trans : forall m n (M N P : matrix m n),
    M =m N -> N =m P -> M =m P.

  Proof.
    unfold mat_eqA. intros. trans (get_elem N ip jp); auto.
  Qed.

  Definition mat_eqA_st : forall m n, Setoid_Theory (matrix m n) (@mat_eqA m n).

  Proof.
    constructor. unfold Reflexive. apply mat_eqA_refl.
    unfold Symmetric. apply mat_eqA_sym. unfold Transitive. apply mat_eqA_trans.
  Qed.

  Add Parametric Relation m n : (matrix m n) (@mat_eqA m n)
    reflexivity proved by (@mat_eqA_refl m n)
    symmetry proved by (@mat_eqA_sym m n)
      transitivity proved by (@mat_eqA_trans m n)
        as mat_eqA_rel.

  Lemma mat_eq : forall m n (M N : matrix m n), 
    (forall i j (ip : i < m) (jp : j < n), 
      get_elem M ip jp = get_elem N ip jp) -> M = N.

  Proof.
    unfold matrix. induction m; simpl; intros.
    VOtac. refl.
    unfold get_elem, get_row in H.
    VSntac M. VSntac N. apply Vcons_eq_intro.
    apply Veq_nth. intros.
    do 2 rewrite Vhead_nth. apply H.
    apply IHm. intros. 
    unfold get_elem, get_row. do 2 rewrite Vnth_tail. apply H.
  Qed.

  Add Parametric Morphism m n i (h:i<m) : (fun M => @get_row m n M i h)
    with signature (@mat_eqA m n) ==> (@eq_vec n)
      as get_row_mor.

  Proof.
    intros. apply Vforall2n_intro. intros. apply H.
  Qed.

  Add Parametric Morphism m n i (h:i<n) : (fun M => @get_col m n M i h)
    with signature (@mat_eqA m n) ==> (@eq_vec m)
      as get_col_mor.

  Proof.
    intros. apply Vforall2n_intro. intros.
    repeat rewrite <- get_elem_swap. apply H.
  Qed.

  Add Parametric Morphism m n i j (ip:i<m) (jp:j<n) :
    (fun M => @get_elem m n M i j ip jp)
    with signature (@mat_eqA m n) ==> eqA
      as get_elem_mor.

  Proof.
    unfold get_elem. intros. apply H.
  Qed.

  (** Matrix construction over domain natural numbers. *)

  Definition mat_build_spec : forall m n 
    (gen : forall i j, i < m -> j < n -> A), 
    { M : matrix m n | forall i j (ip : i < m) (jp : j < n), 
      get_elem M ip jp = gen i j ip jp }.

  Proof.
    induction m; intros.
    exists (Vnil (A:=vec n)). intros.
    elimtype False. exact (lt_n_O ip).
    set (gen_1 := fun j => gen 0 j (lt_O_Sn m)).
    set (gen' := fun i j H => gen (S i) j (lt_n_S H)).
    destruct (IHm n gen') as [Mtl Mtl_spec].
    destruct (Vbuild_spec gen_1) as [Mhd Mhd_spec].
    exists (Vcons Mhd Mtl). intros.    
    destruct i; unfold get_elem; simpl.
    rewrite Mhd_spec. unfold gen_1. rewrite (le_unique (lt_O_Sn m) ip). refl.
    unfold get_elem in Mtl_spec. rewrite Mtl_spec.
    unfold gen'. rewrite (le_unique (lt_n_S (lt_S_n ip)) ip). refl.
  Defined.

  Definition mat_build m n gen : matrix m n := proj1_sig (mat_build_spec gen).

  Lemma mat_build_elem : forall m n gen i j (ip : i < m) (jp : j < n), 
    get_elem (mat_build gen) ip jp = gen i j ip jp.

  Proof.
    intros. unfold mat_build. destruct (mat_build_spec gen). simpl. apply e.
  Qed.

  Lemma mat_build_nth : forall m n gen i j (ip : i < m) (jp : j < n),
    Vnth (Vnth (mat_build gen) ip) jp = gen i j ip jp.

  Proof.
    intros. fold (get_row (mat_build gen) ip).
    fold (get_elem (mat_build gen) ip jp).
    apply mat_build_elem.
  Qed.

  (** Some elementary matrices over domain natural numbers. *)

  Notation A0 := A0N.
  Definition zero_matrix m n : matrix m n := mat_build (fun i j ip jp => A0). 
  Definition id_matrix (n: nat) : matrix n n  := Vbuild (fun i ip => id_vec ip).
  Definition inverse_matrix inv m n (M : matrix m n) : matrix m n :=
    mat_build (fun i j ip jp => inv (get_elem M ip jp)).

  (** 1-row and 1-column matrices over domain natural numbers. *)

  Definition row_mat n := matrix 1 n.
  Definition col_mat n := matrix n 1.
  Definition vec_to_row_mat n (v : vec n) : row_mat n := Vcons v Vnil.
  Definition vec_to_col_mat n (v : vec n) : col_mat n := 
    Vmap (fun i => Vcons i Vnil) v.

  Add Parametric Morphism n : (@vec_to_col_mat n)
    with signature (@eq_vec n) ==> (@mat_eqA n 1)
      as vec_to_col_mat_mor.

  Proof.
    unfold vec_to_col_mat, mat_eqA, get_elem. intros.
    repeat rewrite get_elem_swap. unfold get_col. repeat rewrite Vnth_map.
    apply (Vnth_mor eqA). rewrite (eq_vec_cons eqA). intuition.
    apply (Vnth_mor eqA). hyp.
  Qed.

  Definition access_0 : 0 < 1 := le_n 1.
  Definition row_mat_to_vec n (m : row_mat n) := get_row m access_0.
  Definition col_mat_to_vec n (m : col_mat n) := get_col m access_0.

  Ltac mat_get_simpl :=
    repeat progress unfold get_elem, get_col, get_row, 
      vec_to_col_mat, vec_to_row_mat, col_mat_to_vec, row_mat_to_vec; 
      repeat progress ( try rewrite Vnth_map; try rewrite Vnth_map2);
        try refl.

  Lemma get_col_col_mat : forall n (v : vec n) (p : 0 < 1),
    get_col (vec_to_col_mat v) p = v.

  Proof.
    induction v; intros.
    trivial.
    simpl.
    rewrite IHv. trivial.
  Qed.

  Lemma vec_to_col_mat_spec : forall n (v : vec n) i (ip : i < n) j 
    (jp : j < 1), get_elem (vec_to_col_mat v) ip jp = Vnth v ip.
    
  Proof.
    intros. unfold get_elem.
    rewrite get_elem_swap.
    destruct j.
    rewrite get_col_col_mat. trivial.
    absurd_arith.
  Qed.

  Lemma vec_to_row_mat_spec : forall n (v : vec n) i (ip : i < 1) j 
    (jp : j < n), get_elem (vec_to_row_mat v) ip jp = Vnth v jp.

  Proof.
    intros. unfold get_elem.
    destruct i. trivial. absurd_arith.
  Qed.

  Lemma Vnth_col_mat : forall n (m : col_mat n) i (ip : i < n),
    Vnth (col_mat_to_vec m) ip = get_elem m ip access_0.

  Proof.
    induction m; intros. absurd_arith.
    destruct i.
    trivial.
    simpl. rewrite IHm. trivial.
  Qed.

  Lemma Vnth_row_mat : forall n (m : row_mat n) i (ip : i < n),
    Vnth (row_mat_to_vec m) ip = get_elem m access_0 ip.

  Proof.
    trivial.
  Qed.

  Lemma col_mat_to_vec_idem : forall n (v : vec n), 
    col_mat_to_vec (vec_to_col_mat v) = v.

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl.
  Qed.

  Lemma vec_to_col_mat_idem : forall n (M : col_mat n), 
    vec_to_col_mat (col_mat_to_vec M) = M.

  Proof.
    intros. apply mat_eq. intros.
    mat_get_simpl.
    destruct j. rewrite (lt_unique access_0 jp). refl.
    absurd_arith.
  Qed.

  Lemma row_mat_to_vec_idem : forall n (v : vec n), 
    row_mat_to_vec (vec_to_row_mat v) = v.

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl.
  Qed.

  Lemma vec_to_row_mat_idem : forall n (M : row_mat n), 
    vec_to_row_mat (row_mat_to_vec M) = M.

  Proof.
    intros. apply mat_eq. intros.
    mat_get_simpl.
    destruct i. simpl. rewrite (lt_unique access_0 ip). refl.
    absurd_arith.
  Qed.

  (** Matrix transposition over domain natural numbers. *)

  Definition mat_transpose m n (M : matrix m n) := 
    mat_build (fun _ _ i j => get_elem M j i).

  Lemma mat_transpose_row_col : forall m n (M : matrix m n) i (ip : i < m),
    get_col (mat_transpose M) ip = get_row M ip.

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl. unfold mat_transpose.
    rewrite mat_build_nth. trivial.
  Qed.

  Lemma mat_transpose_col_row : forall m n (M : matrix m n) i (ip : i < n),
    get_row (mat_transpose M) ip = get_col M ip.

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl. unfold mat_transpose.
    rewrite mat_build_nth. trivial.
  Qed.

  Lemma mat_transpose_idem : forall m n (M : matrix m n),
    mat_transpose (mat_transpose M) = M.

  Proof.
    intros. apply mat_eq . intros.
    unfold mat_transpose. do 2 rewrite mat_build_elem. refl.
  Qed.

  (** Matrix addition over domain natural numbers. *)
  
  Notation Aplus := AplusN.
  Notation Amult := AmultN.
  Notation "X + Y" := (Aplus X Y).
  Notation "X * Y" := (Amult X Y).
  Infix "[+]" := vector_plus (at level 50).

  Definition vec_plus n (L R : vec n) := Vmap2 Aplus L R.
  Definition mat_plus m n (L R : matrix m n) := Vmap2 (@vec_plus n) L R.
  Infix "<+>" := mat_plus (at level 50).

  Lemma mat_plus_comm : forall m n (L R : matrix m n), L <+> R =m R <+> L.

  Proof.
    unfold mat_eqA. intros. unfold mat_plus, vec_plus.
    mat_get_simpl. apply plus_comm.
  Qed.

  (** Matrix multiplication over domain natural numbers. *)

  Definition mat_mult m n p (L : matrix m n) (R : matrix n p) :=
    mat_build (fun i j ip jp => dot_product (get_row L ip) (get_col R jp)).
  Infix "<*>" := mat_mult (at level 40).

  Add Parametric Morphism m n p : (@mat_mult m n p)
    with signature (@mat_eqA m n) ==> (@mat_eqA n p) ==> (@mat_eqA m p)
      as mat_mult_mor.

  Proof.
    unfold mat_mult. intros. unfold mat_eqA. intros.
    repeat rewrite mat_build_elem. apply dot_product_mor.
    apply get_row_mor. hyp. apply get_col_mor. hyp.
  Qed.
  
  Lemma mat_mult_elem : forall m n p (M : matrix m n) (N : matrix n p) 
    i (ip : i < m) j (jp : j < p), 
    Vnth (Vnth (M <*> N) ip) jp = dot_product (get_row M ip) (get_col N jp).

  Proof.
    intros. unfold mat_mult. rewrite mat_build_nth. refl.
  Qed.

  Lemma mat_mult_spec : forall m n p (M : matrix m n) (N : matrix n p) 
    i (ip : i < m) j (jp : j < p), 
    get_elem (M <*> N) ip jp = dot_product (get_row M ip) (get_col N jp).

  Proof.
    intros.
    mat_get_simpl. rewrite mat_mult_elem. refl.
  Qed.

  Lemma mat_mult_row : forall m n p (M : matrix m n) (N : matrix n p) 
    i (ip : i < m),
    get_row (M <*> N) ip = 
    Vbuild (fun j jp => dot_product (get_row M ip) (get_col N jp)).

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl. 
    rewrite mat_mult_elem. rewrite Vbuild_nth. refl.
  Qed.

  Lemma mat_mult_col : forall m n p (M : matrix m n) (N : matrix n p) 
    j (jp : j < p),
    get_col (M <*> N) jp = 
    Vbuild (fun i ip => dot_product (get_row M ip) (get_col N jp)).

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl. 
    rewrite mat_mult_elem. rewrite Vbuild_nth. refl.
  Qed.

  Lemma mat_mult_id_l : forall n p (np : n >= p) (M : matrix n p), 
    id_matrix n <*> M =m M.

  Proof.
    unfold mat_eqA. intros. rewrite mat_mult_spec.
    unfold id_matrix, get_row. rewrite Vbuild_nth.
    rewrite (dot_product_id ip). mat_get_simpl.
  Qed.

  Lemma zero_matrix_mult_l : forall m n p (M : matrix n p), 
    zero_matrix m n <*> M =m zero_matrix m p.

  Proof.
    unfold mat_eqA. intros.
    unfold zero_matrix at 2.
    mat_get_simpl.
    fold (get_row (zero_matrix m n <*> M) ip).
    fold (get_elem (zero_matrix m n <*> M) ip jp).
    rewrite mat_mult_spec. rewrite dot_product_zero. 
    rewrite mat_build_nth. refl.
    apply Vforall_nth_intro. intros.
    unfold zero_matrix. mat_get_simpl. rewrite mat_build_nth. refl.
  Qed.

  Lemma dot_product_assoc : forall m n v v' (M : matrix m n),
    dot_product v (Vbuild (fun i (ip : i < m ) => 
      dot_product (get_row M ip) v')) =A=
    dot_product (Vbuild (fun j (jp : j < n) =>
      dot_product v (get_col M jp))) v'.
    
  Proof.
    induction m; intros.
    (* induction base *)
    VOtac. repeat rewrite dot_product_zero. 
    refl.
    apply Vforall_nth_intro. intros. rewrite Vbuild_nth.
    unfold SemiRing2.eqA. refl.
    apply Vforall_intro. intros. destruct H.
    (* induction case *)
    VSntac v.
    rewrite (VSn_eq (Vbuild (fun i ip => dot_product (get_row M ip) v'))).
    rewrite dot_product_cons. do 2 rewrite Vhead_nth. rewrite Vbuild_nth.
    rewrite Vbuild_tail. unfold matrix in M. VSntac M. simpl.
    match goal with
      |- _ + dot_product _ (Vbuild ?gen) =A= _ => replace (Vbuild gen) with 
        (Vbuild (fun i ip => dot_product (get_row (Vtail M) ip) v')) end.
    rewrite (IHm n (Vtail v) v' (Vtail M)).
    set (a := Vbuild (fun (j : nat) (jp : j < n) =>
      dot_product (Vtail v) (get_col (Vtail M) jp))).
    set (b := Vbuild (fun (j : nat) (jp : j < n) =>
      dot_product (Vcons (Vnth v (lt_O_Sn m)) (Vtail v))
      (Vcons (Vnth (Vhead M) jp) (get_col (Vtail M) jp)))).
    set (c := Vbuild (fun j jp => Vnth v (lt_O_Sn m) * (Vnth (Vhead M) jp))).
    set (d := Vbuild (fun j jp =>
      dot_product (Vtail v) (get_col (Vtail M) jp))).
    assert (b =v c [+] d). apply Vforall2n_intro. intros.
    rewrite vector_plus_nth. unfold b, c, d. do 3 rewrite Vbuild_nth.
    rewrite dot_product_cons. refl. trans (dot_product (c[+]d) v').
    rewrite dot_product_distr_l. rewrite dot_product_distr_mult. refl.
    apply dot_product_mor. sym. hyp. refl.
    apply Veq_nth. intros. do 2 rewrite Vbuild_nth. rewrite lt_Sn_nS. refl.
  Qed.

  Lemma mat_mult_assoc : forall m n p l 
    (M : matrix m n) (N : matrix n p) (P : matrix p l),
    M <*> (N <*> P) =m M <*> N <*> P.

  Proof.
    unfold mat_eqA. intros. 
    mat_get_simpl. repeat rewrite mat_mult_elem.
    rewrite mat_mult_row. rewrite mat_mult_col. apply dot_product_assoc.
  Qed.

  (** Matrix-col vector product over domain natural numbers. *)

  Definition mat_vec_prod m n (m : matrix m n) (v : vec n) :=
    col_mat_to_vec (m <*> (vec_to_col_mat v)).

  Add Parametric Morphism m n : (@mat_vec_prod m n)
    with signature (@mat_eqA m n) ==> (@eq_vec n) ==> (@eq_vec m)
      as mat_vec_prod_mor.

  Proof.
    unfold mat_vec_prod. intros. apply get_col_mor. rewrite H. rewrite H0.
    refl.
  Qed.

  Lemma mat_vec_prod_distr_vec : forall m n (M : matrix m n) v1 v2,
    mat_vec_prod M (v1 [+] v2) =v
    mat_vec_prod M v1 [+] mat_vec_prod M v2.

  Proof.
    intros. unfold mat_vec_prod. apply Vforall2n_intro. intros.
    rewrite vector_plus_nth. mat_get_simpl.
    repeat rewrite mat_mult_elem. rewrite <- dot_product_distr_r.
    apply dot_product_mor. refl.
    apply Vforall2n_intro. intros. unfold get_col.
    repeat rewrite Vnth_map. simpl. rewrite vector_plus_nth.
    unfold vector_plus. rewrite Vnth_map2. repeat rewrite Vnth_map. refl.
  Qed.

  Lemma mat_vec_prod_distr_mat : forall m n (Ml Mr : matrix m n) v,
    mat_vec_prod (Ml <+> Mr) v =v
    mat_vec_prod Ml v [+] mat_vec_prod Mr v.

  Proof.
    intros. unfold mat_vec_prod. apply Vforall2n_intro. intros.
    rewrite vector_plus_nth. mat_get_simpl.
    repeat rewrite mat_mult_elem.
    set (a := get_col (Vmap (fun i0 : A => Vcons i0 Vnil) v) access_0).
    rewrite (dot_product_comm (get_row Ml ip)).
    rewrite (dot_product_comm (get_row Mr ip)).
    rewrite <- dot_product_distr_r.
    rewrite dot_product_comm. apply dot_product_mor. refl. clear a.
    unfold get_row, mat_plus. rewrite Vnth_map2. refl.
  Qed.

  Lemma mat_vec_prod_distr_add_vectors : forall m n (M : matrix m n) k v1 v2,
    (forall i (ip : i < k), mat_vec_prod M (Vnth v1 ip) =v Vnth v2 ip) ->
    mat_vec_prod M (add_vectors v1) =v add_vectors v2.
    
  Proof.
    induction k; intros.
    (* induction base *)
    VOtac. unfold add_vectors. simpl.
    apply Vforall2n_intro. intros.
    unfold mat_vec_prod. rewrite Vnth_col_mat.
    unfold zero_vec. rewrite Vnth_const.
    rewrite mat_mult_spec. 
    rewrite dot_product_comm. rewrite dot_product_zero. refl.
    apply Vforall_nth_intro. intros.
    rewrite get_col_col_mat. rewrite Vnth_const. refl.
    (* induction step *)
    VSntac v1. VSntac v2. 
    do 2 rewrite add_vectors_cons. rewrite mat_vec_prod_distr_vec.
    do 2 rewrite Vhead_nth. apply vector_plus_mor. rewrite H. refl.
    rewrite (IHk (Vtail v1) (Vtail v2)). refl.
    intros. rewrite Vnth_tail. rewrite H.
    rewrite Vnth_tail. refl.
  Qed.

End Matrix.

(** forall over domain natural numbers. *)

Section Forall.

  Variables (P : AN -> Prop) (m n : nat) (M : matrix m n).
  
  Definition mat_forall := forall i j (ip : i < m) (jp : j < n), 
    P (get_elem M ip jp).
  
  (** Alternative definition. *)
  
  Definition mat_forall' := Vforall (@Vforall AN P n) M.
  
End Forall.

(** forall2 over domain natural numbers. *)

Section Forall2.

  Variables (P : relation AN) (m n : nat).
  
  Definition mat_forall2 (M N : matrix m n):= forall i j (ip : i < m) 
    (jp : j < n), P (get_elem M ip jp) (get_elem N ip jp).
  
  Definition mat_forall2_intro : forall M N,
    (forall i j (ip : i < m) (jp : j < n), 
      P (get_elem M ip jp) (get_elem N ip jp)) ->
    mat_forall2 M N := fun M N H => H.
  
  (* Alternative definition over domain natural numbers. *)

  Definition mat_forall2' (M N : matrix m n) := 
    Vforall2n (@Vforall2n AN AN P n) M N.
  
  Require Import RelMidex.
  
  Variable P_dec : rel_dec P.
  
  Lemma mat_forall2'_dec : rel_dec mat_forall2'.
    
  Proof.
    intros M N. unfold mat_forall2'. do 2 apply Vforall2n_dec. hyp.
  Defined.
  
  Lemma mat_forall2_equiv1 : forall M N, 
    mat_forall2 M N -> mat_forall2' M N.
    
  Proof.
    intros. unfold mat_forall2'. do 2 (apply Vforall2n_intro; intros). 
    exact (H i i0 ip ip0).
  Qed.
  
  Lemma mat_forall2_equiv2 : forall M N, 
    mat_forall2' M N -> mat_forall2 M N.
    
  Proof.
    intros. unfold mat_forall2, get_elem, get_row. intros.
    apply Vforall2n_nth. apply Vforall2n_nth. hyp.
  Qed.
  
  Lemma mat_forall2_dec : rel_dec mat_forall2.
    
  Proof.
    intros M N. destruct (mat_forall2'_dec M N).
    left. apply mat_forall2_equiv2. hyp.
    right. intro. apply n0. apply mat_forall2_equiv1. hyp.
  Defined.
  
End Forall2.

Hint Rewrite mat_mult_id_l zero_matrix_mult_l using simpl : arith.

(** 'monotonicity' of matrix multiplication over domain natural numbers. *)

Section MatMultMonotonicity.
  
  Notation ge := geN.
  
  Variables (m n p : nat) (M M' : matrix m n) (N N' : matrix n p).
  
  Definition mat_ge := mat_forall2 ge.
  Infix ">=m" := mat_ge (at level 70).
  
  Lemma mat_ge_refl : M >=m M.
    
  Proof.
    unfold mat_ge, mat_forall2. 
    intros. apply ge_reflN.
  Qed.
  
  Lemma mat_ge_dec : forall m n, rel_dec (@mat_ge m n).

  Proof.
    intros R Q. unfold mat_ge. apply mat_forall2_dec.
    exact NatUtil.ge_dec.
  Defined.
  
  Infix "<*>" := mat_mult (at level 40).
  Infix ">=v" := vec_ge (at level 70).
  Notation Aplus := AplusN.
  Notation Amult := AmultN.
  Notation "x >>= y" := (geN x y) (at level 70).
  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).
  Parameter plus_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m + n >>= m' + n'.
  Parameter mult_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m * n >>= m' * n'.
  Hint Resolve ge_reflN : arith.
  Notation vec := (vector AN).

  Lemma dot_product_mon : forall i (v v' w w' : vec i), v >=v v' -> 
    w >=v w' -> dot_product v w >>= dot_product v' w'.
    
  Proof.
    unfold dot_product. induction v. auto with arith. 
    intros. simpl.
    apply plus_ge_compat.
    apply IHv.
    change v with (Vtail (Vcons h v)). apply Vreln_tail_intro. hyp.
    apply Vreln_tail_intro. hyp.
    set (p0 := lt_O_Sn n0). apply mult_ge_compat.
    change h with (Vnth (Vcons h v) p0). rewrite Vhead_nth.
    apply Vforall2n_nth. hyp.
    do 2 rewrite Vhead_nth. apply Vforall2n_nth. hyp.
  Qed.
  
  Lemma mat_mult_mon : M >=m M' -> N >=m N' -> M <*> N >=m M' <*> N'.
    
  Proof.
    intros. unfold mat_ge, mat_forall2. intros.
    do 2 rewrite mat_mult_spec. apply dot_product_mon.
    apply Vforall2n_intro. intros.
    exact (H i i0 ip ip0).
    apply Vforall2n_intro. intros.
    do 2 rewrite <- get_elem_swap. exact (H0 i0 j ip0 jp).
  Qed.
  
End MatMultMonotonicity.

Infix ">=v" := vec_ge (at level 70).

Lemma mat_vec_prod_ge_compat : forall i j (M M' : matrix i j) m m', 
  mat_ge M M' -> m >=v m' -> mat_vec_prod M m >=v mat_vec_prod M' m'.
  
Proof.
  intros. unfold mat_vec_prod, vec_ge. apply Vforall2n_intro. 
  intros. do 2 rewrite Vnth_col_mat. apply mat_mult_mon. hyp.
  unfold mat_ge. intros k l pk pl. do 2 rewrite vec_to_col_mat_spec.
  apply Vforall2n_nth. hyp.
Qed.

Infix ">=m" := mat_ge (at level 70).

(** Matrix construction functions over natural numbers. *)

Section MatrixConstruction.

  Variable A : Set.

  Definition mkMatrix1 (v1 : A) := Vcons (vec_of_list (v1 :: nil)) Vnil.
  Definition mkMatrix2 (v1 v2 v3 v4 : A) := 
    Vcons (vec_of_list (v1 :: v2 :: nil)) 
    (Vcons (vec_of_list (v3 :: v4 :: nil)) Vnil).
  Definition mkMatrix3 (v1 v2 v3 v4 v5 v6 v7 v8 v9 : A) := 
    Vcons (vec_of_list (v1 :: v2 :: v3 :: nil)) 
    (Vcons (vec_of_list (v4 :: v5 :: v6 :: nil))
      (Vcons (vec_of_list (v7 :: v8 :: v9 :: nil)) Vnil)).
  Definition mkMatrix4 (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 
    v11 v12 v13 v14 v15 v16 : A) := 
  Vcons (vec_of_list ( v1 ::  v2 ::  v3 ::  v4 :: nil)) 
  (Vcons (vec_of_list ( v5 ::  v6 ::  v7 ::  v8 :: nil))
    (Vcons (vec_of_list ( v9 :: v10 :: v11 :: v12 :: nil))
      (Vcons (vec_of_list (v13 :: v14 :: v15 :: v16 :: nil)) Vnil))).

End MatrixConstruction.

(***********************************************************************)
(** ** Basic definitions of matrix over domain arctic natural numbers. *)

Section Matrix_arcnat.

  Notation A := Ar.
  Notation eqA := eqAr.
  Notation sid_theoryA := sid_theoryAr.
  Notation "X =A= Y" := (eqA X Y) (at level 70).
  Notation "v1 =v v2" := (eq_vec_arcnat v1 v2) (at level 70).
  Notation vec := (vector Ar).
 
  Add Setoid A eqA sid_theoryA as A_Setoid_arcnat.
  Notation A_semi_ring := A_semi_ringr.

  Add Ring Aring_arcnat : A_semi_ring.
  
  (** Matrix represented by a vector of vectors (in a row-wise
  fashion) over domain arctic natural numbers. *)

  Definition matrix_arcnat m n := vector (vec n) m.

  (** Accessors over domain arctic natural numbers. *)

  Definition get_row_arcnat m n
    (M : matrix_arcnat m n) i (ip : i < m) := Vnth M ip.

  Definition get_col_arcnat m n (M : matrix_arcnat m n) i (ip : i < n) := 
    Vmap (fun v => Vnth v ip) M.

  Definition get_elem_arcnat m n
    (M : matrix_arcnat m n) i j (ip : i < m) (jp : j < n) :=
    Vnth (get_row_arcnat M ip) jp.

  Lemma get_elem_swap_arcnat : forall m n (M : matrix_arcnat m n) i j (ip : i < m) 
    (jp : j < n), Vnth (get_row_arcnat M ip) jp = Vnth (get_col_arcnat M jp) ip.

  Proof.
    induction M; intros. absurd_arith.
    destruct i.
    trivial.
    simpl. rewrite IHM. trivial.
  Qed.

  Add Parametric Relation n : (vec n) (@eq_vec_arcnat n)
    reflexivity proved by (@eq_vec_refl A eqA sid_theoryA n)
    symmetry proved by (@eq_vec_sym A eqA sid_theoryA n)
      transitivity proved by (@eq_vec_trans A eqA sid_theoryA n)
        as eq_vec_rel_arcnat.

  Definition mat_eqA_arcnat m n (M N : matrix_arcnat m n) :=
    forall i j (ip : i < m) (jp : j < n),
      get_elem_arcnat M ip jp =A= get_elem_arcnat N ip jp.

  Notation "M =m N" := (mat_eqA_arcnat M N) (at level 70).

  Lemma mat_eqA_refl_arcnat : forall m n (M : matrix_arcnat m n),
    M =m M.

  Proof.
    unfold mat_eqA_arcnat. refl.
  Qed.

  Lemma mat_eqA_sym_arcnat : forall m n (M N : matrix_arcnat m n),
    M =m N -> N =m M.

  Proof.
    unfold mat_eqA_arcnat. intros. sym. apply H.
  Qed.

  Lemma mat_eqA_trans_arcnat: forall m n (M N P : matrix_arcnat m n),
    M =m N -> N =m P -> M =m P.

  Proof.
    unfold mat_eqA_arcnat. intros. trans (get_elem_arcnat N ip jp); auto.
  Qed.

  Definition mat_eqA_st_arcnat : forall m n,
    Setoid_Theory (matrix_arcnat m n) (@mat_eqA_arcnat m n).

  Proof.
    constructor. unfold Reflexive. apply mat_eqA_refl_arcnat.
    unfold Symmetric. apply mat_eqA_sym_arcnat. unfold Transitive.
    apply mat_eqA_trans_arcnat.
  Qed.

  Add Parametric Relation m n : (matrix_arcnat m n) (@mat_eqA_arcnat m n)
    reflexivity proved by (@mat_eqA_refl_arcnat m n)
    symmetry proved by (@mat_eqA_sym_arcnat m n)
      transitivity proved by (@mat_eqA_trans_arcnat m n)
        as mat_eqA_rel_arcnat.

  Lemma mat_eq_arcnat : forall m n (M N : matrix_arcnat m n), 
    (forall i j (ip : i < m) (jp : j < n), 
      get_elem_arcnat M ip jp = get_elem_arcnat N ip jp) -> M = N.

  Proof.
    unfold matrix_arcnat. induction m; simpl; intros.
    VOtac. refl.
    unfold get_elem_arcnat, get_row_arcnat in H.
    VSntac M. VSntac N. apply Vcons_eq_intro.
    apply Veq_nth. intros.
    do 2 rewrite Vhead_nth. apply H.
    apply IHm. intros. 
    unfold get_elem_arcnat, get_row_arcnat.
    do 2 rewrite Vnth_tail. apply H.
  Qed.

  Add Parametric Morphism m n i (h:i<m) :
    (fun M => @get_row_arcnat m n M i h)
    with signature (@mat_eqA_arcnat m n) ==> (@eq_vec_arcnat n)
      as get_row_mor_arcnat.

  Proof.
    intros. apply Vforall2n_intro. intros. apply H.
  Qed.

  Add Parametric Morphism m n i (h:i<n) :
    (fun M => @get_col_arcnat m n M i h)
    with signature (@mat_eqA_arcnat m n) ==> (@eq_vec_arcnat m)
      as get_col_mor_arcnat.

  Proof.
    intros. apply Vforall2n_intro. intros.
    repeat rewrite <- get_elem_swap_arcnat. apply H.
  Qed.

  Add Parametric Morphism m n i j (ip:i<m) (jp:j<n) :
    (fun M => @get_elem_arcnat m n M i j ip jp)
    with signature (@mat_eqA_arcnat m n) ==> eqA
      as get_elem_mor_arcnat.

  Proof.
    unfold get_elem_arcnat. intros. apply H.
  Qed.

  (** Matrix construction over domain natural numbers. *)

  Definition mat_build_spec_arcnat : forall m n 
    (gen : forall i j, i < m -> j < n -> A), 
    { M : matrix_arcnat m n | forall i j (ip : i < m) (jp : j < n), 
      get_elem_arcnat M ip jp = gen i j ip jp }.

  Proof.
    induction m; intros.
    exists (Vnil (A:=vec n)). intros.
    elimtype False. exact (lt_n_O ip).
    set (gen_1 := fun j => gen 0 j (lt_O_Sn m)).
    set (gen' := fun i j H => gen (S i) j (lt_n_S H)).
    destruct (IHm n gen') as [Mtl Mtl_spec].
    destruct (Vbuild_spec gen_1) as [Mhd Mhd_spec].
    exists (Vcons Mhd Mtl). intros.    
    destruct i; unfold get_elem_arcnat; simpl.
    rewrite Mhd_spec. unfold gen_1.
    rewrite (le_unique (lt_O_Sn m) ip). refl.
    unfold get_elem_arcnat in Mtl_spec. rewrite Mtl_spec.
    unfold gen'. rewrite (le_unique (lt_n_S (lt_S_n ip)) ip). refl.
  Defined.

  Definition mat_build_arcnat m n gen : matrix_arcnat m n :=
    proj1_sig (mat_build_spec_arcnat gen).

  Lemma mat_build_elem_arcnat : forall m n gen i j (ip : i < m) (jp : j < n), 
    get_elem_arcnat (mat_build_arcnat gen) ip jp = gen i j ip jp.

  Proof.
    intros. unfold mat_build_arcnat.
    destruct (mat_build_spec_arcnat gen). simpl. apply e.
  Qed.

  Lemma mat_build_nth_arcnat : forall m n gen i j (ip : i < m) (jp : j < n),
    Vnth (Vnth (mat_build_arcnat gen) ip) jp = gen i j ip jp.

  Proof.
    intros. fold (get_row_arcnat (mat_build_arcnat gen) ip).
    fold (get_elem_arcnat (mat_build_arcnat gen) ip jp).
    apply mat_build_elem_arcnat.
  Qed.

  (** Some elementary matrices over domain arctic natural numbers. *)

  Notation A0 := A0r.

  Definition zero_matrix_arcnat m n : matrix_arcnat m n :=
    mat_build_arcnat (fun i j ip jp => A0). 

  Definition id_matrix_arcnat (n: nat) : matrix_arcnat n n :=
    Vbuild (fun i ip => id_vec_arcnat ip).

  Definition inverse_matrix_arcnat inv m n (M : matrix_arcnat m n)
    : matrix_arcnat m n :=
    mat_build_arcnat (fun i j ip jp => inv (get_elem_arcnat M ip jp)).

  (** 1-row and 1-column matrices over domain arctic natural numbers. *)

  Definition row_mat_arcnat n := matrix_arcnat 1 n.
  Definition col_mat_arcnat n := matrix_arcnat n 1.

  Definition vec_to_row_mat_arcnat n (v : vec n)
    : row_mat_arcnat n := Vcons v Vnil.

  Definition vec_to_col_mat_arcnat n (v : vec n) : col_mat_arcnat n := 
    Vmap (fun i => Vcons i Vnil) v.

  Add Parametric Morphism n : (@vec_to_col_mat_arcnat n)
    with signature (@eq_vec_arcnat n) ==> (@mat_eqA_arcnat n 1)
      as vec_to_col_mat_mor_arcnat.

  Proof.
    unfold vec_to_col_mat_arcnat, mat_eqA_arcnat, get_elem_arcnat. intros.
    repeat rewrite get_elem_swap_arcnat. unfold get_col_arcnat.
    repeat rewrite Vnth_map.
    apply (Vnth_mor eqA). rewrite (eq_vec_cons eqA). intuition.
    apply (Vnth_mor eqA). hyp.
  Qed.

  Definition row_mat_to_vec_arcnat n (m : row_mat_arcnat n) :=
    get_row_arcnat m access_0.
  Definition col_mat_to_vec_arcnat n (m : col_mat_arcnat n) :=
    get_col_arcnat m access_0.

  Ltac mat_get_simpl_arcnat :=
    repeat progress unfold get_elem_arcnat, get_col_arcnat, get_row_arcnat, 
      vec_to_col_mat_arcnat, vec_to_row_mat_arcnat, col_mat_to_vec_arcnat,
      row_mat_to_vec_arcnat; 
      repeat progress ( try rewrite Vnth_map; try rewrite Vnth_map2);
        try refl.
  
  Lemma get_col_col_mat_arcnat : forall n (v : vec n) (p : 0 < 1),
    get_col_arcnat (vec_to_col_mat_arcnat v) p = v.

  Proof.
    induction v; intros.
    trivial.
    simpl.
    rewrite IHv. trivial.
  Qed.

  Lemma vec_to_col_mat_spec_arcnat : forall n (v : vec n) i (ip : i < n) j 
    (jp : j < 1), get_elem_arcnat (vec_to_col_mat_arcnat v) ip jp = Vnth v ip.
    
  Proof.
    intros. unfold get_elem_arcnat.
    rewrite get_elem_swap_arcnat.
    destruct j.
    rewrite get_col_col_mat_arcnat. trivial.
    absurd_arith.
  Qed.

  Lemma vec_to_row_mat_spec_arcnat : forall n (v : vec n) i (ip : i < 1) j 
    (jp : j < n), get_elem_arcnat (vec_to_row_mat_arcnat v) ip jp = Vnth v jp.

  Proof.
    intros. unfold get_elem_arcnat.
    destruct i. trivial. absurd_arith.
  Qed.

  Lemma Vnth_col_mat_arcnat : forall n (m : col_mat_arcnat n) i (ip : i < n),
    Vnth (col_mat_to_vec_arcnat m) ip = get_elem_arcnat m ip access_0.

  Proof.
    induction m; intros. absurd_arith.
    destruct i.
    trivial.
    simpl. rewrite IHm. trivial.
  Qed.

  Lemma Vnth_row_mat_arcnat : forall n (m : row_mat_arcnat n) i (ip : i < n),
    Vnth (row_mat_to_vec_arcnat m) ip = get_elem_arcnat m access_0 ip.

  Proof.
    trivial.
  Qed.

  Lemma col_mat_to_vec_idem_arcnat : forall n (v : vec n), 
    col_mat_to_vec_arcnat (vec_to_col_mat_arcnat v) = v.

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_arcnat.
  Qed.

  Lemma vec_to_col_mat_idem_arcnat : forall n (M : col_mat_arcnat n), 
    vec_to_col_mat_arcnat (col_mat_to_vec_arcnat M) = M.

  Proof.
    intros. apply mat_eq_arcnat. intros.
    mat_get_simpl_arcnat.
    destruct j. rewrite (lt_unique access_0 jp). refl.
    absurd_arith.
  Qed.

  Lemma row_mat_to_vec_idem_arcnat : forall n (v : vec n), 
    row_mat_to_vec_arcnat (vec_to_row_mat_arcnat v) = v.

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_arcnat.
  Qed.

  Lemma vec_to_row_mat_idem_arcnat : forall n (M : row_mat_arcnat n), 
    vec_to_row_mat_arcnat (row_mat_to_vec_arcnat M) = M.

  Proof.
    intros. apply mat_eq_arcnat. intros.
    mat_get_simpl_arcnat.
    destruct i. simpl. rewrite (lt_unique access_0 ip). refl.
    absurd_arith.
  Qed.

  (** Matrix transposition over domain arctic natural numbers. *)

  Definition mat_transpose_arcnat m n (M : matrix_arcnat m n) := 
    mat_build_arcnat (fun _ _ i j => get_elem_arcnat M j i).

  Lemma mat_transpose_row_col_arcnat : forall m n (M : matrix_arcnat m n) i
    (ip : i < m), 
    get_col_arcnat (mat_transpose_arcnat M) ip = get_row_arcnat M ip.

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_arcnat. unfold mat_transpose_arcnat.
    rewrite mat_build_nth_arcnat. trivial.
  Qed.

  Lemma mat_transpose_col_row_arcnat : forall m n (M : matrix_arcnat m n) i
    (ip : i < n),
    get_row_arcnat (mat_transpose_arcnat M) ip = get_col_arcnat M ip.

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_arcnat. unfold mat_transpose_arcnat.
    rewrite mat_build_nth_arcnat. trivial.
  Qed.

  Lemma mat_transpose_idem_arcnat : forall m n (M : matrix_arcnat m n),
    mat_transpose_arcnat (mat_transpose_arcnat M) = M.

  Proof.
    intros. apply mat_eq_arcnat. intros.
    unfold mat_transpose_arcnat.
    do 2 rewrite mat_build_elem_arcnat. refl.
  Qed.

  (** Matrix addition over domain arctic natural numbers. *)
  
  Notation Aplus := Aplusr.
  Notation Amult := Amultr.
  Notation "X + Y" := (Aplus X Y).
  Notation "X * Y" := (Amult X Y).
  Infix "[+]" := vector_plus_arcnat (at level 50).

  Definition vec_plus_arcnat n (L R : vec n) := Vmap2 Aplus L R.

  Definition mat_plus_arcnat m n (L R : matrix_arcnat m n) :=
    Vmap2 (@vec_plus_arcnat n) L R.

  Infix "<+>" := mat_plus_arcnat (at level 50).

  Lemma mat_plus_comm_arcnat : forall m n (L R : matrix_arcnat m n),
    L <+> R =m R <+> L.

  Proof.
    unfold mat_eqA_arcnat. intros. unfold mat_plus_arcnat, vec_plus_arcnat.
    mat_get_simpl_arcnat. apply A_plus_comm.
  Qed.

  (** Matrix multiplication over domain arctic natural numbers. *)

  Definition mat_mult_arcnat m n p (L : matrix_arcnat m n) (R : matrix_arcnat n p) :=
    mat_build_arcnat (fun i j ip jp => dot_product_arcnat (get_row_arcnat L ip)
      (get_col_arcnat R jp)).

  Infix "<*>" := mat_mult_arcnat (at level 40).

  Add Parametric Morphism m n p : (@mat_mult_arcnat m n p)
    with signature (@mat_eqA_arcnat m n) ==> (@mat_eqA_arcnat n p) ==> (@mat_eqA_arcnat m p)
      as mat_mult_mor_arcnat.

  Proof.
    unfold mat_mult_arcnat. intros. unfold mat_eqA_arcnat. intros.
    repeat rewrite mat_build_elem_arcnat. apply dot_product_mor_arcnat.
    apply get_row_mor_arcnat. hyp. apply get_col_mor_arcnat. hyp.
  Qed.
  
  Lemma mat_mult_elem_arcnat: forall m n p (M : matrix_arcnat m n)
    (N : matrix_arcnat n p) i (ip : i < m) j (jp : j < p), 
    Vnth (Vnth (M <*> N) ip) jp = dot_product_arcnat (get_row_arcnat M ip)
    (get_col_arcnat N jp).

  Proof.
    intros. unfold mat_mult_arcnat. rewrite mat_build_nth_arcnat. refl.
  Qed.

  Lemma mat_mult_spec_arcnat : forall m n p (M : matrix_arcnat m n)
    (N : matrix_arcnat n p) i (ip : i < m) j (jp : j < p), 
    get_elem_arcnat (M <*> N) ip jp = dot_product_arcnat (get_row_arcnat M ip)
    (get_col_arcnat N jp).

  Proof.
    intros.
    mat_get_simpl_arcnat. rewrite mat_mult_elem_arcnat. refl.
  Qed.

  Lemma mat_mult_row_arcnat : forall m n p (M : matrix_arcnat m n)
    (N : matrix_arcnat n p) i (ip : i < m),
    get_row_arcnat (M <*> N) ip = 
    Vbuild (fun j jp => dot_product_arcnat (get_row_arcnat M ip)
      (get_col_arcnat N jp)).

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_arcnat. 
    rewrite mat_mult_elem_arcnat. rewrite Vbuild_nth. refl.
  Qed.

  Lemma mat_mult_col_arcnat : forall m n p (M : matrix_arcnat m n)
    (N : matrix_arcnat n p) j (jp : j < p),
    get_col_arcnat (M <*> N) jp = 
    Vbuild (fun i ip => dot_product_arcnat (get_row_arcnat M ip)
      (get_col_arcnat N jp)).

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_arcnat. 
    rewrite mat_mult_elem_arcnat. rewrite Vbuild_nth. refl.
  Qed.

  Lemma mat_mult_id_l_arcnat : forall n p (np : n >= p) (M : matrix_arcnat n p), 
    id_matrix_arcnat n <*> M =m M.

  Proof.
    unfold mat_eqA_arcnat. intros. rewrite mat_mult_spec_arcnat.
    unfold id_matrix_arcnat, get_row_arcnat. rewrite Vbuild_nth.
    rewrite (dot_product_id_arcnat ip). mat_get_simpl_arcnat.
  Qed.

  Lemma zero_matrix_mult_l_arcnat : forall m n p (M : matrix_arcnat n p), 
    zero_matrix_arcnat m n <*> M =m zero_matrix_arcnat m p.

  Proof.
    unfold mat_eqA_arcnat. intros.
    unfold zero_matrix_arcnat at 2.
    mat_get_simpl_arcnat.
    fold (get_row_arcnat (zero_matrix_arcnat m n <*> M) ip).
    fold (get_elem_arcnat (zero_matrix_arcnat m n <*> M) ip jp).
    rewrite mat_mult_spec_arcnat. rewrite dot_product_zero_arcnat. 
    rewrite mat_build_nth_arcnat. refl.
    apply Vforall_nth_intro. intros.
    unfold zero_matrix_arcnat. mat_get_simpl_arcnat.
    rewrite mat_build_nth_arcnat. refl.
  Qed.

  Lemma dot_product_assoc_arcnat : forall m n v v' (M : matrix_arcnat m n),
    dot_product_arcnat v (Vbuild (fun i (ip : i < m ) => 
      dot_product_arcnat (get_row_arcnat M ip) v')) =A=
    dot_product_arcnat (Vbuild (fun j (jp : j < n) =>
      dot_product_arcnat v (get_col_arcnat M jp))) v'.
    
  Proof.
    induction m; intros.
    (* induction base *)
    VOtac. repeat rewrite dot_product_zero_arcnat. 
    refl.
    apply Vforall_nth_intro. intros. rewrite Vbuild_nth.
    unfold SemiRing2.eqAr. refl.
    apply Vforall_intro. intros. destruct H.
    (* induction case *)
    VSntac v.
    rewrite (VSn_eq (Vbuild (fun i ip => dot_product_arcnat (get_row_arcnat M ip) v'))).
    rewrite dot_product_cons_arcnat. do 2 rewrite Vhead_nth. rewrite Vbuild_nth.
    rewrite Vbuild_tail. unfold matrix_arcnat in M. VSntac M. simpl.
    match goal with
      |- _ + dot_product_arcnat _ (Vbuild ?gen) =A= _ => replace (Vbuild gen) with 
        (Vbuild (fun i ip => dot_product_arcnat (get_row_arcnat (Vtail M) ip) v')) end.
    rewrite (IHm n (Vtail v) v' (Vtail M)).
    set (a := Vbuild (fun (j : nat) (jp : j < n) =>
      dot_product_arcnat (Vtail v) (get_col_arcnat (Vtail M) jp))).
    set (b := Vbuild (fun (j : nat) (jp : j < n) =>
      dot_product_arcnat (Vcons (Vnth v (lt_O_Sn m)) (Vtail v))
      (Vcons (Vnth (Vhead M) jp) (get_col_arcnat (Vtail M) jp)))).
    set (c := Vbuild (fun j jp => Vnth v (lt_O_Sn m) * (Vnth (Vhead M) jp))).
    set (d := Vbuild (fun j jp =>
      dot_product_arcnat (Vtail v) (get_col_arcnat (Vtail M) jp))).
    assert (b =v c [+] d). apply Vforall2n_intro. intros.
    rewrite vector_plus_nth_arcnat. unfold b, c, d. do 3 rewrite Vbuild_nth.
    rewrite dot_product_cons_arcnat. refl. trans (dot_product_arcnat (c[+]d) v').
    rewrite dot_product_distr_l_arcnat. rewrite dot_product_distr_mult_arcnat. refl.
    apply dot_product_mor_arcnat. sym. hyp. refl.
    apply Veq_nth. intros. do 2 rewrite Vbuild_nth. rewrite lt_Sn_nS. refl.
  Qed.

  Lemma mat_mult_assoc_arcnat : forall m n p l 
    (M : matrix_arcnat m n) (N : matrix_arcnat n p) (P : matrix_arcnat p l),
    M <*> (N <*> P) =m M <*> N <*> P.

  Proof.
    unfold mat_eqA_arcnat. intros. 
    mat_get_simpl_arcnat. repeat rewrite mat_mult_elem_arcnat.
    rewrite mat_mult_row_arcnat. rewrite mat_mult_col_arcnat.
    apply dot_product_assoc_arcnat.
  Qed.

  (** Matrix-col vector product over domain arctic natural numbers. *)

  Definition mat_vec_prod_arcnat m n (m : matrix_arcnat m n) (v : vec n) :=
    col_mat_to_vec_arcnat (m <*> (vec_to_col_mat_arcnat v)).

  Add Parametric Morphism m n : (@mat_vec_prod_arcnat m n)
    with signature (@mat_eqA_arcnat m n) ==> (@eq_vec_arcnat n) ==> (@eq_vec_arcnat m)
      as mat_vec_prod_mor_arcnat.

  Proof.
    unfold mat_vec_prod_arcnat. intros. apply get_col_mor_arcnat.
    rewrite H. rewrite H0.
    refl.
  Qed.

  Lemma mat_vec_prod_distr_vec_arcnat : forall m n (M : matrix_arcnat m n) v1 v2,
    mat_vec_prod_arcnat M (v1 [+] v2) =v
    mat_vec_prod_arcnat M v1 [+] mat_vec_prod_arcnat M v2.

  Proof.
    intros. unfold mat_vec_prod_arcnat. apply Vforall2n_intro. intros.
    rewrite vector_plus_nth_arcnat. mat_get_simpl_arcnat.
    repeat rewrite mat_mult_elem_arcnat. rewrite <- dot_product_distr_r_arcnat.
    apply dot_product_mor_arcnat. refl.
    apply Vforall2n_intro. intros. unfold get_col_arcnat.
    repeat rewrite Vnth_map. simpl. rewrite vector_plus_nth_arcnat.
    unfold vector_plus_arcnat. rewrite Vnth_map2. repeat rewrite Vnth_map. refl.
  Qed.

  Lemma mat_vec_prod_distr_mat_arcnat : forall m n (Ml Mr : matrix_arcnat m n) v,
    mat_vec_prod_arcnat (Ml <+> Mr) v =v
    mat_vec_prod_arcnat Ml v [+] mat_vec_prod_arcnat Mr v.

  Proof.
    intros. unfold mat_vec_prod_arcnat. apply Vforall2n_intro. intros.
    rewrite vector_plus_nth_arcnat. mat_get_simpl_arcnat.
    repeat rewrite mat_mult_elem_arcnat.
    set (a := get_col_arcnat (Vmap (fun i0 : A => Vcons i0 Vnil) v) access_0).
    rewrite (dot_product_comm_arcnat (get_row_arcnat Ml ip)).
    rewrite (dot_product_comm_arcnat (get_row_arcnat Mr ip)).
    rewrite <- dot_product_distr_r_arcnat.
    rewrite dot_product_comm_arcnat. apply dot_product_mor_arcnat. refl. clear a.
    unfold get_row_arcnat, mat_plus_arcnat. rewrite Vnth_map2. refl.
  Qed.

  Lemma mat_vec_prod_distr_add_vectors_arcnat : forall m n (M : matrix_arcnat m n) 
    k v1 v2,(forall i (ip : i < k), mat_vec_prod_arcnat M (Vnth v1 ip) =v Vnth v2 ip) ->
    mat_vec_prod_arcnat M (add_vectors_arcnat v1) =v add_vectors_arcnat v2.
    
  Proof.
    induction k; intros.
    (* induction base *)
    VOtac. unfold add_vectors_arcnat. simpl.
    apply Vforall2n_intro. intros.
    unfold mat_vec_prod_arcnat. rewrite Vnth_col_mat_arcnat.
    unfold zero_vec_arcnat. rewrite Vnth_const.
    rewrite mat_mult_spec_arcnat. 
    rewrite dot_product_comm_arcnat. rewrite dot_product_zero_arcnat. refl.
    apply Vforall_nth_intro. intros.
    rewrite get_col_col_mat_arcnat. rewrite Vnth_const. refl.
    (* induction step *)
    VSntac v1. VSntac v2. 
    do 2 rewrite add_vectors_cons_arcnat. rewrite mat_vec_prod_distr_vec_arcnat.
    do 2 rewrite Vhead_nth. apply vector_plus_mor_arcnat. rewrite H. refl.
    rewrite (IHk (Vtail v1) (Vtail v2)). refl.
    intros. rewrite Vnth_tail. rewrite H.
    rewrite Vnth_tail. refl.
  Qed.

End Matrix_arcnat.

(** forall over domain arctic natural numbers. *)

Section Forall_arcnat.

  Variables (P : Ar -> Prop) (m n : nat) (M : matrix_arcnat m n).

  Definition mat_forall_arcnat := forall i j (ip : i < m) (jp : j < n), 
    P (get_elem_arcnat M ip jp).

  (** Alternative definition. *)

  Definition mat_forall_arcnat' := Vforall (@Vforall Ar P n) M.

End Forall_arcnat.

(** forall2 over domain arctic natural numbers. *)

Section Forall2_arcnat.

  Variables (P : relation Ar) (m n : nat).

  Definition mat_forall2_arcnat (M N : matrix_arcnat m n):= forall i j (ip : i < m) 
    (jp : j < n), P (get_elem_arcnat M ip jp) (get_elem_arcnat N ip jp).

  Definition mat_forall2_intro_arcnat : forall M N,
    (forall i j (ip : i < m) (jp : j < n), 
      P (get_elem_arcnat M ip jp) (get_elem_arcnat N ip jp)) ->
    mat_forall2_arcnat M N := fun M N H => H.

  (** Alternative definition. *)

  Definition mat_forall2'_arcnat (M N : matrix_arcnat m n) := 
    Vforall2n (@Vforall2n Ar Ar P n) M N.

  Require Import RelMidex.

  Variable P_dec : rel_dec P.

  Lemma mat_forall2'_dec_arcnat : rel_dec mat_forall2'_arcnat.

  Proof.
    intros M N. unfold mat_forall2'_arcnat. do 2 apply Vforall2n_dec. hyp.
  Defined.

  Lemma mat_forall2_equiv1_arcnat : forall M N, 
    mat_forall2_arcnat M N -> mat_forall2'_arcnat M N.

  Proof.
    intros. unfold mat_forall2'_arcnat. do 2 (apply Vforall2n_intro; intros). 
    exact (H i i0 ip ip0).
  Qed.

  Lemma mat_forall2_equiv2_arcnat : forall M N, 
    mat_forall2'_arcnat M N -> mat_forall2_arcnat M N.

  Proof.
    intros. unfold mat_forall2_arcnat, get_elem_arcnat, get_row_arcnat. intros.
    apply Vforall2n_nth. apply Vforall2n_nth. hyp.
  Qed.

  Lemma mat_forall2_dec_arcnat : rel_dec mat_forall2_arcnat.

  Proof.
    intros M N. destruct (mat_forall2'_dec_arcnat M N).
    left. apply mat_forall2_equiv2_arcnat. hyp.
    right. intro. apply n0. apply mat_forall2_equiv1_arcnat. hyp.
  Defined.

End Forall2_arcnat.

Hint Rewrite mat_mult_id_l_arcnat zero_matrix_mult_l_arcnat using simpl : arith.

(** 'monotonicity' of matrix multiplication over arctic naturals *)

Section MatMultMonotonicity_arcnat.

  Notation ge := ger.

  Variables (m n p : nat) (M M' : matrix_arcnat m n) (N N' : matrix_arcnat n p).

  Definition mat_ge_arcnat := mat_forall2_arcnat ger.
  Infix ">=m" := mat_ge_arcnat (at level 70).

  Lemma mat_ge_refl_arcnat : M >=m M.

  Proof.
    unfold mat_ge_arcnat, mat_forall2_arcnat. 
    intros. apply ge_reflr.
  Qed.

  Lemma mat_ge_dec_arcnat : forall m n, rel_dec (@mat_ge_arcnat m n).

  Proof.
    intros R Q. unfold mat_ge_arcnat. apply mat_forall2_dec_arcnat.
    exact ge_decr.
  Defined.

  Infix "<*>" := mat_mult_arcnat (at level 40).
  Infix ">=v" := vec_ge_arcnat (at level 70).
  Notation Aplus := Aplusr.
  Notation Amult := Amultr.
  Notation "x >>= y" := (ger x y) (at level 70).
  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).
  Parameter plus_ge_compat_arcnat : forall m n m' n',
    m >>= m' -> n >>= n' -> m + n >>= m' + n'.
  Parameter mult_ge_compat_arcnat : forall m n m' n',
    m >>= m' -> n >>= n' -> m * n >>= m' * n'.
  Hint Resolve ge_reflr : arith.
  Notation vec := (vector Ar).

  Lemma dot_product_mon_arcnat : forall i (v v' w w' : vec i), v >=v v' -> 
    w >=v w' -> dot_product_arcnat v w >>= dot_product_arcnat v' w'.

  Proof.
    unfold dot_product_arcnat. induction v. auto with arith. 
    intros. simpl.
    apply plus_ge_compat_arcnat.
    apply IHv.
    change v with (Vtail (Vcons h v)). apply Vreln_tail_intro. hyp.
    apply Vreln_tail_intro. hyp.
    set (p0 := lt_O_Sn n0). apply mult_ge_compat_arcnat.
    change h with (Vnth (Vcons h v) p0). rewrite Vhead_nth.
    apply Vforall2n_nth. hyp.
    do 2 rewrite Vhead_nth. apply Vforall2n_nth. hyp.
  Qed.

  Lemma mat_mult_mon_arcnat : M >=m M' -> N >=m N' -> M <*> N >=m M' <*> N'.

  Proof.
    intros. unfold mat_ge_arcnat, mat_forall2_arcnat. intros.
    do 2 rewrite mat_mult_spec_arcnat. apply dot_product_mon_arcnat.
    apply Vforall2n_intro. intros.
    exact (H i i0 ip ip0).
    apply Vforall2n_intro. intros.
    do 2 rewrite <- get_elem_swap_arcnat. exact (H0 i0 j ip0 jp).
  Qed.

End MatMultMonotonicity_arcnat.

Infix ">=v" := vec_ge_arcnat (at level 70).

Lemma mat_vec_prod_ge_compat_arcnat : forall i j (M M' : matrix_arcnat i j) m m', 
  mat_ge_arcnat M M' -> m >=v m' -> mat_vec_prod_arcnat M m >=v mat_vec_prod_arcnat M' m'.

Proof.
  intros. unfold mat_vec_prod_arcnat, vec_ge_arcnat. apply Vforall2n_intro.
  intros. do 2 rewrite Vnth_col_mat_arcnat. apply mat_mult_mon_arcnat. hyp.
  unfold mat_ge_arcnat. intros k l pk pl. do 2 rewrite vec_to_col_mat_spec_arcnat.
  apply Vforall2n_nth. hyp.
Qed.

Infix ">=m" := mat_ge_arcnat (at level 70).

(***********************************************************************)
(** ** Basic definitions of matrix over domain arctic integer numbers. *)

Section Matrix_arcbz.

  Notation A := Arbz.
  Notation eqA := eqArbz.
  Notation sid_theoryA := sid_theoryArbz.
  Notation "X =A= Y" := (eqA X Y) (at level 70).
  Notation "v1 =v v2" := (eq_vec_arcbz v1 v2) (at level 70).
  Notation vec := (vector Arbz).
  Add Setoid A eqA sid_theoryA as A_Setoid_arcbz.
  Notation A_semi_ring := A_semi_ringrbz.
  Add Ring Aring_arcbz : A_semi_ring.
  
  (** Matrix represented by a vector of vectors (in a row-wise
  fashion) over domain arctic integer numbers. *)

  Definition matrix_arcbz m n := vector (vec n) m.

  (** Accessors over domain arctic integer numbers. *)

  Definition get_row_arcbz m n (M : matrix_arcbz m n) i (ip : i < m) := Vnth M ip.
  Definition get_col_arcbz m n (M : matrix_arcbz m n) i (ip : i < n) := 
    Vmap (fun v => Vnth v ip) M.
  Definition get_elem_arcbz m n (M : matrix_arcbz m n) i j (ip : i < m) (jp : j < n) :=
    Vnth (get_row_arcbz M ip) jp.

  Lemma get_elem_swap_arcbz : forall m n (M : matrix_arcbz m n) i j (ip : i < m) 
    (jp : j < n), Vnth (get_row_arcbz M ip) jp = Vnth (get_col_arcbz M jp) ip.

  Proof.
    induction M; intros. absurd_arith.
    destruct i.
    trivial.
    simpl. rewrite IHM. trivial.
  Qed.
  
  Add Parametric Relation n : (vec n) (@eq_vec_arcbz n)
    reflexivity proved by (@eq_vec_refl A eqA sid_theoryA n)
    symmetry proved by (@eq_vec_sym A eqA sid_theoryA n)
      transitivity proved by (@eq_vec_trans A eqA sid_theoryA n)
        as eq_vec_rel_arcbz.

  Definition mat_eqA_arcbz m n (M N : matrix_arcbz m n) :=
    forall i j (ip : i < m) (jp : j < n),
      get_elem_arcbz M ip jp =A= get_elem_arcbz N ip jp.

  Notation "M =m N" := (mat_eqA_arcbz M N) (at level 70).

  Lemma mat_eqA_refl_arcbz : forall m n (M : matrix_arcbz m n), M =m M.

  Proof.
    unfold mat_eqA_arcbz. refl.
  Qed.

  Lemma mat_eqA_sym_arcbz : forall m n (M N : matrix_arcbz m n),
    M =m N -> N =m M.

  Proof.
    unfold mat_eqA_arcbz. intros. sym. apply H.
  Qed.

  Lemma mat_eqA_trans_arcbz: forall m n (M N P : matrix_arcbz m n),
    M =m N -> N =m P -> M =m P.

  Proof.
    unfold mat_eqA_arcbz. intros. trans (get_elem_arcbz N ip jp); auto.
  Qed.

  Definition mat_eqA_st_arcbz : forall m n,
    Setoid_Theory (matrix_arcbz m n) (@mat_eqA_arcbz m n).

  Proof.
    constructor. unfold Reflexive. apply mat_eqA_refl_arcbz.
    unfold Symmetric. apply mat_eqA_sym_arcbz. unfold Transitive.
    apply mat_eqA_trans_arcbz.
  Qed.

  Add Parametric Relation m n : (matrix_arcbz m n) (@mat_eqA_arcbz m n)
    reflexivity proved by (@mat_eqA_refl_arcbz m n)
    symmetry proved by (@mat_eqA_sym_arcbz m n)
      transitivity proved by (@mat_eqA_trans_arcbz m n)
        as mat_eqA_rel_arcbz.

  Lemma mat_eq_arcbz : forall m n (M N : matrix_arcbz m n), 
    (forall i j (ip : i < m) (jp : j < n), 
      get_elem_arcbz M ip jp = get_elem_arcbz N ip jp) -> M = N.

  Proof.
    unfold matrix_arcbz. induction m; simpl; intros.
    VOtac. refl.
    unfold get_elem_arcbz, get_row_arcbz in H.
    VSntac M. VSntac N. apply Vcons_eq_intro.
    apply Veq_nth. intros.
    do 2 rewrite Vhead_nth. apply H.
    apply IHm. intros. 
    unfold get_elem_arcbz, get_row_arcbz. do 2 rewrite Vnth_tail. apply H.
  Qed.

  Add Parametric Morphism m n i (h:i<m) : (fun M => @get_row_arcbz m n M i h)
    with signature (@mat_eqA_arcbz m n) ==> (@eq_vec_arcbz n)
      as get_row_mor_arcbz.

  Proof.
    intros. apply Vforall2n_intro. intros. apply H.
  Qed.

  Add Parametric Morphism m n i (h:i<n) : (fun M => @get_col_arcbz m n M i h)
    with signature (@mat_eqA_arcbz m n) ==> (@eq_vec_arcbz m)
      as get_col_mor_arcbz.

  Proof.
    intros. apply Vforall2n_intro. intros.
    repeat rewrite <- get_elem_swap_arcbz. apply H.
  Qed.

  Add Parametric Morphism m n i j (ip:i<m) (jp:j<n) :
    (fun M => @get_elem_arcbz m n M i j ip jp)
    with signature (@mat_eqA_arcbz m n) ==> eqA
      as get_elem_mor_arcbz.

  Proof.
    unfold get_elem_arcbz. intros. apply H.
  Qed.

  (** Matrix construction over domain arctic integer numbers. *)

  Definition mat_build_spec_arcbz : forall m n 
    (gen : forall i j, i < m -> j < n -> A), 
    { M : matrix_arcbz m n | forall i j (ip : i < m) (jp : j < n), 
      get_elem_arcbz M ip jp = gen i j ip jp }.

  Proof.
    induction m; intros.
    exists (Vnil (A:=vec n)). intros.
    elimtype False. exact (lt_n_O ip).
    set (gen_1 := fun j => gen 0 j (lt_O_Sn m)).
    set (gen' := fun i j H => gen (S i) j (lt_n_S H)).
    destruct (IHm n gen') as [Mtl Mtl_spec].
    destruct (Vbuild_spec gen_1) as [Mhd Mhd_spec].
    exists (Vcons Mhd Mtl). intros.    
    destruct i; unfold get_elem_arcbz; simpl.
    rewrite Mhd_spec. unfold gen_1. rewrite (le_unique (lt_O_Sn m) ip). refl.
    unfold get_elem_arcbz in Mtl_spec. rewrite Mtl_spec.
    unfold gen'. rewrite (le_unique (lt_n_S (lt_S_n ip)) ip). refl.
  Defined.

  Definition mat_build_arcbz m n gen : matrix_arcbz m n :=
    proj1_sig (mat_build_spec_arcbz gen).

  Lemma mat_build_elem_arcbz : forall m n gen i j (ip : i < m) (jp : j < n), 
    get_elem_arcbz (mat_build_arcbz gen) ip jp = gen i j ip jp.

  Proof.
    intros. unfold mat_build_arcbz. destruct (mat_build_spec_arcbz gen). simpl. apply e.
  Qed.

  Lemma mat_build_nth_arcbz : forall m n gen i j (ip : i < m) (jp : j < n),
    Vnth (Vnth (mat_build_arcbz gen) ip) jp = gen i j ip jp.

  Proof.
    intros. fold (get_row_arcbz (mat_build_arcbz gen) ip).
    fold (get_elem_arcbz (mat_build_arcbz gen) ip jp).
    apply mat_build_elem_arcbz.
  Qed.

  (** Some elementary matrices over domain arctic integer numbers. *)

  Notation A0 := A0rbz.

  Definition zero_matrix_arcbz m n : matrix_arcbz m n :=
    mat_build_arcbz (fun i j ip jp => A0). 

  Definition id_matrix_arcbz (n: nat) : matrix_arcbz n n :=
    Vbuild (fun i ip => id_vec_arcbz ip).

  Definition inverse_matrix_arcbz inv m n (M : matrix_arcbz m n)
    : matrix_arcbz m n :=
    mat_build_arcbz (fun i j ip jp => inv (get_elem_arcbz M ip jp)).

  (** 1-row and 1-column matrices over domain integer numbers. *)

  Definition row_mat_arcbz n := matrix_arcbz 1 n.
  Definition col_mat_arcbz n := matrix_arcbz n 1.
  Definition vec_to_row_mat_arcbz n (v : vec n)
    : row_mat_arcbz n := Vcons v Vnil.
  Definition vec_to_col_mat_arcbz n (v : vec n) : col_mat_arcbz n := 
    Vmap (fun i => Vcons i Vnil) v.

  Add Parametric Morphism n : (@vec_to_col_mat_arcbz n)
    with signature (@eq_vec_arcbz n) ==> (@mat_eqA_arcbz n 1)
      as vec_to_col_mat_mor_arcbz.

  Proof.
    unfold vec_to_col_mat_arcbz, mat_eqA_arcbz, get_elem_arcbz. intros.
    repeat rewrite get_elem_swap_arcbz. unfold get_col_arcbz.
    repeat rewrite Vnth_map.
    apply (Vnth_mor eqA). rewrite (eq_vec_cons eqA). intuition.
    apply (Vnth_mor eqA). hyp.
  Qed.

  Definition row_mat_to_vec_arcbz n (m : row_mat_arcbz n) :=
    get_row_arcbz m access_0.
  Definition col_mat_to_vec_arcbz n (m : col_mat_arcbz n) :=
    get_col_arcbz m access_0.

  Ltac mat_get_simpl_arcbz :=
    repeat progress unfold get_elem_arcbz, get_col_arcbz, get_row_arcbz, 
      vec_to_col_mat_arcbz, vec_to_row_mat_arcbz, col_mat_to_vec_arcbz,
      row_mat_to_vec_arcbz;
      repeat progress ( try rewrite Vnth_map; try rewrite Vnth_map2);
        try refl.

  Lemma get_col_col_mat_arcbz : forall n (v : vec n) (p : 0 < 1),
    get_col_arcbz (vec_to_col_mat_arcbz v) p = v.

  Proof.
    induction v; intros.
    trivial.
    simpl.
    rewrite IHv. trivial.
  Qed.

  Lemma vec_to_col_mat_spec_arcbz : forall n (v : vec n) i (ip : i < n) j 
    (jp : j < 1), get_elem_arcbz (vec_to_col_mat_arcbz v) ip jp = Vnth v ip.
    
  Proof.
    intros. unfold get_elem_arcbz.
    rewrite get_elem_swap_arcbz.
    destruct j.
    rewrite get_col_col_mat_arcbz. trivial.
    absurd_arith.
  Qed.

  Lemma vec_to_row_mat_spec_arcbz : forall n (v : vec n) i (ip : i < 1) j 
    (jp : j < n), get_elem_arcbz (vec_to_row_mat_arcbz v) ip jp = Vnth v jp.

  Proof.
    intros. unfold get_elem_arcbz.
    destruct i. trivial. absurd_arith.
  Qed.

  Lemma Vnth_col_mat_arcbz : forall n (m : col_mat_arcbz n) i (ip : i < n),
    Vnth (col_mat_to_vec_arcbz m) ip = get_elem_arcbz m ip access_0.

  Proof.
    induction m; intros. absurd_arith.
    destruct i.
    trivial.
    simpl. rewrite IHm. trivial.
  Qed.

  Lemma Vnth_row_mat_arcbz : forall n (m : row_mat_arcbz n) i (ip : i < n),
    Vnth (row_mat_to_vec_arcbz m) ip = get_elem_arcbz m access_0 ip.

  Proof.
    trivial.
  Qed.

  Lemma col_mat_to_vec_idem_arcbz : forall n (v : vec n), 
    col_mat_to_vec_arcbz (vec_to_col_mat_arcbz v) = v.

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_arcbz.
  Qed.

  Lemma vec_to_col_mat_idem_arcbz : forall n (M : col_mat_arcbz n), 
    vec_to_col_mat_arcbz (col_mat_to_vec_arcbz M) = M.

  Proof.
    intros. apply mat_eq_arcbz. intros.
    mat_get_simpl_arcbz.
    destruct j. rewrite (lt_unique access_0 jp). refl.
    absurd_arith.
  Qed.

  Lemma row_mat_to_vec_idem_arcbz : forall n (v : vec n), 
    row_mat_to_vec_arcbz (vec_to_row_mat_arcbz v) = v.

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_arcbz.
  Qed.

  Lemma vec_to_row_mat_idem_arcbz : forall n (M : row_mat_arcbz n), 
    vec_to_row_mat_arcbz (row_mat_to_vec_arcbz M) = M.

  Proof.
    intros. apply mat_eq_arcbz. intros.
    mat_get_simpl_arcbz.
    destruct i. simpl. rewrite (lt_unique access_0 ip). refl.
    absurd_arith.
  Qed.

  (** Matrix transposition over domain integer numbers. *)

  Definition mat_transpose_arcbz m n (M : matrix_arcbz m n) := 
    mat_build_arcbz (fun _ _ i j => get_elem_arcbz M j i).

  Lemma mat_transpose_row_col_arcbz : forall m n (M : matrix_arcbz m n) i
    (ip : i < m), get_col_arcbz (mat_transpose_arcbz M) ip = get_row_arcbz M ip.

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_arcbz. unfold mat_transpose_arcbz.
    rewrite mat_build_nth_arcbz. trivial.
  Qed.

  Lemma mat_transpose_col_row_arcbz : forall m n (M : matrix_arcbz m n) i
    (ip : i < n), get_row_arcbz (mat_transpose_arcbz M) ip = get_col_arcbz M ip.

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_arcbz. unfold mat_transpose_arcbz.
    rewrite mat_build_nth_arcbz. trivial.
  Qed.

  Lemma mat_transpose_idem_arcbz : forall m n (M : matrix_arcbz m n),
    mat_transpose_arcbz (mat_transpose_arcbz M) = M.

  Proof.
    intros. apply mat_eq_arcbz. intros.
    unfold mat_transpose_arcbz. do 2 rewrite mat_build_elem_arcbz. refl.
  Qed.

  (** Matrix addition over domain arctic integer numbers. *)
  
  Notation Aplus := Aplusrbz.
  Notation Amult := Amultrbz.
  Notation "X + Y" := (Aplus X Y).
  Notation "X * Y" := (Amult X Y).
  Infix "[+]" := vector_plus_arcbz (at level 50).

  Definition vec_plus_arcbz n (L R : vec n) := Vmap2 Aplus L R.
  Definition mat_plus_arcbz m n (L R : matrix_arcbz m n) :=
    Vmap2 (@vec_plus_arcbz n) L R.
  Infix "<+>" := mat_plus_arcbz (at level 50).

  Lemma mat_plus_comm_arcbz : forall m n (L R : matrix_arcbz m n),
    L <+> R =m R <+> L.

  Proof.
    unfold mat_eqA_arcbz. intros. unfold mat_plus_arcbz, vec_plus_arcbz.
    mat_get_simpl_arcbz. ring.
  Qed.

  (** Matrix multiplication over domain arctic integer numbers. *)

  Definition mat_mult_arcbz m n p (L : matrix_arcbz m n) (R : matrix_arcbz n p) :=
    mat_build_arcbz (fun i j ip jp => dot_product_arcbz (get_row_arcbz L ip)
      (get_col_arcbz R jp)).

  Infix "<*>" := mat_mult_arcbz (at level 40).

  Add Parametric Morphism m n p : (@mat_mult_arcbz m n p)
    with signature (@mat_eqA_arcbz m n) ==> (@mat_eqA_arcbz n p) ==> (@mat_eqA_arcbz m p)
      as mat_mult_mor_arcbz.

  Proof.
    unfold mat_mult_arcbz. intros. unfold mat_eqA_arcbz. intros.
    repeat rewrite mat_build_elem_arcbz. apply dot_product_mor_arcbz.
    apply get_row_mor_arcbz. hyp. apply get_col_mor_arcbz. hyp.
  Qed.
  
  Lemma mat_mult_elem_arcbz: forall m n p (M : matrix_arcbz m n)
    (N : matrix_arcbz n p) i (ip : i < m) j (jp : j < p), 
    Vnth (Vnth (M <*> N) ip) jp = dot_product_arcbz (get_row_arcbz M ip)
    (get_col_arcbz N jp).

  Proof.
    intros. unfold mat_mult_arcbz. rewrite mat_build_nth_arcbz. refl.
  Qed.

  Lemma mat_mult_spec_arcbz : forall m n p (M : matrix_arcbz m n)
    (N : matrix_arcbz n p) i (ip : i < m) j (jp : j < p), 
    get_elem_arcbz (M <*> N) ip jp = dot_product_arcbz (get_row_arcbz M ip)
    (get_col_arcbz N jp).

  Proof.
    intros.
    mat_get_simpl_arcbz. rewrite mat_mult_elem_arcbz. refl.
  Qed.

  Lemma mat_mult_row_arcbz : forall m n p (M : matrix_arcbz m n)
    (N : matrix_arcbz n p) i (ip : i < m),
    get_row_arcbz (M <*> N) ip = 
    Vbuild (fun j jp => dot_product_arcbz (get_row_arcbz M ip)
      (get_col_arcbz N jp)).

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_arcbz. 
    rewrite mat_mult_elem_arcbz. rewrite Vbuild_nth. refl.
  Qed.

  Lemma mat_mult_col_arcbz : forall m n p (M : matrix_arcbz m n)
    (N : matrix_arcbz n p) j (jp : j < p),
    get_col_arcbz (M <*> N) jp = 
    Vbuild (fun i ip => dot_product_arcbz (get_row_arcbz M ip)
      (get_col_arcbz N jp)).

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_arcbz. 
    rewrite mat_mult_elem_arcbz. rewrite Vbuild_nth. refl.
  Qed.

  Lemma mat_mult_id_l_arcbz : forall n p (np : n >= p) (M : matrix_arcbz n p), 
    id_matrix_arcbz n <*> M =m M.

  Proof.
    unfold mat_eqA_arcbz. intros. rewrite mat_mult_spec_arcbz.
    unfold id_matrix_arcbz, get_row_arcbz. rewrite Vbuild_nth.
    rewrite (dot_product_id_arcbz ip). mat_get_simpl_arcbz.
  Qed.

  Lemma zero_matrix_mult_l_arcbz : forall m n p (M : matrix_arcbz n p), 
    zero_matrix_arcbz m n <*> M =m zero_matrix_arcbz m p.

  Proof.
    unfold mat_eqA_arcbz. intros.
    unfold zero_matrix_arcbz at 2.
    mat_get_simpl_arcbz.
    fold (get_row_arcbz (zero_matrix_arcbz m n <*> M) ip).
    fold (get_elem_arcbz (zero_matrix_arcbz m n <*> M) ip jp).
    rewrite mat_mult_spec_arcbz. rewrite dot_product_zero_arcbz. 
    rewrite mat_build_nth_arcbz. refl.
    apply Vforall_nth_intro. intros.
    unfold zero_matrix_arcbz. mat_get_simpl_arcbz.
    rewrite mat_build_nth_arcbz. refl.
  Qed.

  Lemma dot_product_assoc_arcbz : forall m n v v' (M : matrix_arcbz m n),
    dot_product_arcbz v (Vbuild (fun i (ip : i < m ) => 
      dot_product_arcbz (get_row_arcbz M ip) v')) =A=
    dot_product_arcbz (Vbuild (fun j (jp : j < n) =>
      dot_product_arcbz v (get_col_arcbz M jp))) v'.
    
  Proof.
    induction m; intros.
    (* induction base *)
    VOtac. repeat rewrite dot_product_zero_arcbz. 
    refl.
    apply Vforall_nth_intro. intros. rewrite Vbuild_nth.
    unfold SemiRing2.eqAr. refl.
    apply Vforall_intro. intros. destruct H.
    (* induction case *)
    VSntac v.
    rewrite (VSn_eq (Vbuild (fun i ip => dot_product_arcbz (get_row_arcbz M ip) v'))).
    rewrite dot_product_cons_arcbz. do 2 rewrite Vhead_nth. rewrite Vbuild_nth.
    rewrite Vbuild_tail. unfold matrix_arcbz in M. VSntac M. simpl.
    match goal with
      |- _ + dot_product_arcbz _ (Vbuild ?gen) =A= _ => replace (Vbuild gen) with 
        (Vbuild (fun i ip => dot_product_arcbz (get_row_arcbz (Vtail M) ip) v')) end.
    rewrite (IHm n (Vtail v) v' (Vtail M)).
    set (a := Vbuild (fun (j : nat) (jp : j < n) =>
      dot_product_arcbz (Vtail v) (get_col_arcbz (Vtail M) jp))).
    set (b := Vbuild (fun (j : nat) (jp : j < n) =>
      dot_product_arcbz (Vcons (Vnth v (lt_O_Sn m)) (Vtail v))
      (Vcons (Vnth (Vhead M) jp) (get_col_arcbz (Vtail M) jp)))).
    set (c := Vbuild (fun j jp => Vnth v (lt_O_Sn m) * (Vnth (Vhead M) jp))).
    set (d := Vbuild (fun j jp =>
      dot_product_arcbz (Vtail v) (get_col_arcbz (Vtail M) jp))).
    assert (b =v c [+] d). apply Vforall2n_intro. intros.
    rewrite vector_plus_nth_arcbz. unfold b, c, d. do 3 rewrite Vbuild_nth.
    rewrite dot_product_cons_arcbz. refl. trans (dot_product_arcbz (c[+]d) v').
    rewrite dot_product_distr_l_arcbz. rewrite dot_product_distr_mult_arcbz. refl.
    apply dot_product_mor_arcbz. sym. hyp. refl.
    apply Veq_nth. intros. do 2 rewrite Vbuild_nth. rewrite lt_Sn_nS. refl.
  Qed.

  Lemma mat_mult_assoc_arcbz : forall m n p l 
    (M : matrix_arcbz m n) (N : matrix_arcbz n p) (P : matrix_arcbz p l),
    M <*> (N <*> P) =m M <*> N <*> P.

  Proof.
    unfold mat_eqA_arcbz. intros. 
    mat_get_simpl_arcbz. repeat rewrite mat_mult_elem_arcbz.
    rewrite mat_mult_row_arcbz. rewrite mat_mult_col_arcbz.
    apply dot_product_assoc_arcbz.
  Qed.

  (** Matrix-col vector product over domain arctic integer numbers. *)

  Definition mat_vec_prod_arcbz m n (m : matrix_arcbz m n) (v : vec n) :=
    col_mat_to_vec_arcbz (m <*> (vec_to_col_mat_arcbz v)).

  Add Parametric Morphism m n : (@mat_vec_prod_arcbz m n)
    with signature (@mat_eqA_arcbz m n) ==> (@eq_vec_arcbz n) ==> (@eq_vec_arcbz m)
      as mat_vec_prod_mor_arcbz.

  Proof.
    unfold mat_vec_prod_arcbz. intros. apply get_col_mor_arcbz.
    rewrite H. rewrite H0.
    refl.
  Qed.

  Lemma mat_vec_prod_distr_vec_arcbz : forall m n (M : matrix_arcbz m n) v1 v2,
    mat_vec_prod_arcbz M (v1 [+] v2) =v
    mat_vec_prod_arcbz M v1 [+] mat_vec_prod_arcbz M v2.

  Proof.
    intros. unfold mat_vec_prod_arcbz. apply Vforall2n_intro. intros.
    rewrite vector_plus_nth_arcbz. mat_get_simpl_arcbz.
    repeat rewrite mat_mult_elem_arcbz. rewrite <- dot_product_distr_r_arcbz.
    apply dot_product_mor_arcbz. refl.
    apply Vforall2n_intro. intros. unfold get_col_arcbz.
    repeat rewrite Vnth_map. simpl. rewrite vector_plus_nth_arcbz.
    unfold vector_plus_arcbz. rewrite Vnth_map2. repeat rewrite Vnth_map. refl.
  Qed.

  Lemma mat_vec_prod_distr_mat_arcbz : forall m n (Ml Mr : matrix_arcbz m n) v,
    mat_vec_prod_arcbz (Ml <+> Mr) v =v
    mat_vec_prod_arcbz Ml v [+] mat_vec_prod_arcbz Mr v.

  Proof.
    intros. unfold mat_vec_prod_arcbz. apply Vforall2n_intro. intros.
    rewrite vector_plus_nth_arcbz. mat_get_simpl_arcbz.
    repeat rewrite mat_mult_elem_arcbz.
    set (a := get_col_arcbz (Vmap (fun i0 : A => Vcons i0 Vnil) v) access_0).
    rewrite (dot_product_comm_arcbz (get_row_arcbz Ml ip)).
    rewrite (dot_product_comm_arcbz (get_row_arcbz Mr ip)).
    rewrite <- dot_product_distr_r_arcbz.
    rewrite dot_product_comm_arcbz. apply dot_product_mor_arcbz. refl. clear a.
    unfold get_row_arcbz, mat_plus_arcbz. rewrite Vnth_map2. refl.
  Qed.

  Lemma mat_vec_prod_distr_add_vectors_arcbz : forall m n (M : matrix_arcbz m n) 
    k v1 v2,(forall i (ip : i < k), mat_vec_prod_arcbz M (Vnth v1 ip) =v Vnth v2 ip) ->
    mat_vec_prod_arcbz M (add_vectors_arcbz v1) =v add_vectors_arcbz v2.
    
  Proof.
    induction k; intros.
    (* induction base *)
    VOtac. unfold add_vectors_arcbz. simpl.
    apply Vforall2n_intro. intros.
    unfold mat_vec_prod_arcbz. rewrite Vnth_col_mat_arcbz.
    unfold zero_vec_arcbz. rewrite Vnth_const.
    rewrite mat_mult_spec_arcbz. 
    rewrite dot_product_comm_arcbz. rewrite dot_product_zero_arcbz. refl.
    apply Vforall_nth_intro. intros.
    rewrite get_col_col_mat_arcbz. rewrite Vnth_const. refl.
     (* induction step *)
    VSntac v1. VSntac v2. 
    do 2 rewrite add_vectors_cons_arcbz. rewrite mat_vec_prod_distr_vec_arcbz.
    do 2 rewrite Vhead_nth. apply vector_plus_mor_arcbz. rewrite H. refl.
    rewrite (IHk (Vtail v1) (Vtail v2)). refl.
    intros. rewrite Vnth_tail. rewrite H.
    rewrite Vnth_tail. refl.
  Qed.

End Matrix_arcbz.

(** forall over domain arctic integer numbers. *)

Section Forall_arcbz.

  Variables (P : Arbz -> Prop) (m n : nat) (M : matrix_arcbz m n).

  Definition mat_forall_arcbz := forall i j (ip : i < m) (jp : j < n), 
    P (get_elem_arcbz M ip jp).

    (* alternative definition *)
  Definition mat_forall_arcbz' := Vforall (@Vforall Arbz P n) M.

End Forall_arcbz.

(** forall2 over domain arctic integer numbers. *)

Section Forall2_arcbz.

  Variables (P : relation Arbz) (m n : nat).

  Definition mat_forall2_arcbz (M N : matrix_arcbz m n):= forall i j (ip : i < m) 
    (jp : j < n), P (get_elem_arcbz M ip jp) (get_elem_arcbz N ip jp).

  Definition mat_forall2_intro_arcbz : forall M N,
    (forall i j (ip : i < m) (jp : j < n), 
      P (get_elem_arcbz M ip jp) (get_elem_arcbz N ip jp)) ->
    mat_forall2_arcbz M N := fun M N H => H.

  (* Alternative definition. *)
  
  Definition mat_forall2'_arcbz (M N : matrix_arcbz m n) := 
    Vforall2n (@Vforall2n Arbz Arbz P n) M N.

  Require Import RelMidex.

  Variable P_dec : rel_dec P.

  Lemma mat_forall2'_dec_arcbz : rel_dec mat_forall2'_arcbz.

  Proof.
    intros M N. unfold mat_forall2'_arcbz. do 2 apply Vforall2n_dec. hyp.
  Defined.

  Lemma mat_forall2_equiv1_arcbz : forall M N, 
    mat_forall2_arcbz M N -> mat_forall2'_arcbz M N.

  Proof.
    intros. unfold mat_forall2'_arcbz. do 2 (apply Vforall2n_intro; intros). 
    exact (H i i0 ip ip0).
  Qed.

  Lemma mat_forall2_equiv2_arcbz : forall M N, 
    mat_forall2'_arcbz M N -> mat_forall2_arcbz M N.

  Proof.
    intros. unfold mat_forall2_arcbz, get_elem_arcbz, get_row_arcbz. intros.
    apply Vforall2n_nth. apply Vforall2n_nth. hyp.
  Qed.

  Lemma mat_forall2_dec_arcbz : rel_dec mat_forall2_arcbz.

  Proof.
    intros M N. destruct (mat_forall2'_dec_arcbz M N).
    left. apply mat_forall2_equiv2_arcbz. hyp.
    right. intro. apply n0. apply mat_forall2_equiv1_arcbz. hyp.
  Defined.

End Forall2_arcbz.

Hint Rewrite mat_mult_id_l_arcbz zero_matrix_mult_l_arcbz using simpl : arith.

(** 'monotonicity' of matrix multiplication over arctic integer numbers. *)

Section MatMultMonotonicity_arcbz.

  Notation ge := gerbz.
  Variables (m n p : nat) (M M' : matrix_arcbz m n) (N N' : matrix_arcbz n p).

  Definition mat_ge_arcbz := mat_forall2_arcbz gerbz.
  Infix ">=m" := mat_ge_arcbz (at level 70).

  Lemma mat_ge_refl_arcbz : M >=m M.

  Proof.
    unfold mat_ge_arcbz, mat_forall2_arcbz. 
    intros. apply ge_reflrbz.
  Qed.

  Lemma mat_ge_dec_arcbz : forall m n, rel_dec (@mat_ge_arcbz m n).

  Proof.
    intros R Q. unfold mat_ge_arcbz. apply mat_forall2_dec_arcbz.
    exact ge_decrbz.
  Defined.

  Infix "<*>" := mat_mult_arcbz (at level 40).
  Infix ">=v" := vec_ge_arcbz (at level 70).
  Notation Aplus := Aplusrbz.
  Notation Amult := Amultrbz.
  Notation "x >>= y" := (gerbz x y) (at level 70).
  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).

  Parameter plus_ge_compat_arcbz : forall m n m' n',
    m >>= m' -> n >>= n' -> m + n >>= m' + n'.
  Parameter mult_ge_compat_arcbz : forall m n m' n',
    m >>= m' -> n >>= n' -> m * n >>= m' * n'.
  Hint Resolve ge_reflrbz : arith.
  Notation vec := (vector Arbz).

  Lemma dot_product_mon_arcbz : forall i (v v' w w' : vec i), v >=v v' -> 
    w >=v w' -> dot_product_arcbz v w >>= dot_product_arcbz v' w'.

  Proof.
    unfold dot_product_arcbz. induction v. auto with arith. 
    intros. simpl.
    apply plus_ge_compat_arcbz.
    apply IHv.
    change v with (Vtail (Vcons h v)). apply Vreln_tail_intro. hyp.
    apply Vreln_tail_intro. hyp.
    set (p0 := lt_O_Sn n0). apply mult_ge_compat_arcbz.
    change h with (Vnth (Vcons h v) p0). rewrite Vhead_nth.
    apply Vforall2n_nth. hyp.
    do 2 rewrite Vhead_nth. apply Vforall2n_nth. hyp.
  Qed.

  Lemma mat_mult_mon_arcbz : M >=m M' -> N >=m N' -> M <*> N >=m M' <*> N'.

  Proof.
    intros. unfold mat_ge_arcbz, mat_forall2_arcbz. intros.
    do 2 rewrite mat_mult_spec_arcbz. apply dot_product_mon_arcbz.
    apply Vforall2n_intro. intros.
    exact (H i i0 ip ip0).
    apply Vforall2n_intro. intros.
    do 2 rewrite <- get_elem_swap_arcbz. exact (H0 i0 j ip0 jp).
  Qed.

End MatMultMonotonicity_arcbz.

Infix ">=v" := vec_ge_arcbz (at level 70).

Lemma mat_vec_prod_ge_compat_arcbz : forall i j (M M' : matrix_arcbz i j) m m', 
  mat_ge_arcbz M M' -> m >=v m' -> mat_vec_prod_arcbz M m >=v mat_vec_prod_arcbz M' m'.

Proof.
  intros. unfold mat_vec_prod_arcbz, vec_ge_arcbz. apply Vforall2n_intro.
  intros. do 2 rewrite Vnth_col_mat_arcbz. apply mat_mult_mon_arcbz. hyp.
  unfold mat_ge_arcbz. intros k l pk pl. do 2 rewrite vec_to_col_mat_spec_arcbz.
  apply Vforall2n_nth. hyp.
Qed.

Infix ">=m" := mat_ge_arcbz (at level 70).

(***********************************************************************)
(** ** Basic definitions of matrix over domain tropical. *)

Section Matrix_tropic.

  Notation A := At.
  Notation eqA := eqAt.
  Notation sid_theoryA := sid_theoryAt.
  Notation "X =A= Y" := (eqA X Y) (at level 70).
  Notation "v1 =v v2" := (eq_vec_trop v1 v2) (at level 70).
  Notation vec := (vector At).
  Add Setoid A eqA sid_theoryA as A_Setoid_trop.
  Notation A_semi_ring := A_semi_ringt.
  Add Ring Aring_trop : A_semi_ring.
  
  (** Matrix represented by a vector of vectors (in a row-wise fashion)
  over domain tropical. *)

  Definition matrix_trop m n := vector (vec n) m.

  (** Accessors over domain tropical. *)

  Definition get_row_trop m n (M : matrix_trop m n) i (ip : i < m) := Vnth M ip.
  Definition get_col_trop m n (M : matrix_trop m n) i (ip : i < n) := 
    Vmap (fun v => Vnth v ip) M.
  Definition get_elem_trop m n (M : matrix_trop m n) i j (ip : i < m) (jp : j < n) :=
    Vnth (get_row_trop M ip) jp.

  Lemma get_elem_swap_trop : forall m n (M : matrix_trop m n) i j (ip : i < m) 
    (jp : j < n), Vnth (get_row_trop M ip) jp = Vnth (get_col_trop M jp) ip.

  Proof.
    induction M; intros. absurd_arith.
    destruct i.
    trivial.
    simpl. rewrite IHM. trivial.
  Qed.
  
  Add Parametric Relation n : (vec n) (@eq_vec_trop n)
    reflexivity proved by (@eq_vec_refl A eqA sid_theoryA n)
    symmetry proved by (@eq_vec_sym A eqA sid_theoryA n)
      transitivity proved by (@eq_vec_trans A eqA sid_theoryA n)
        as eq_vec_rel_trop.

  Definition mat_eqA_trop m n (M N : matrix_trop m n) :=
    forall i j (ip : i < m) (jp : j < n),
      get_elem_trop M ip jp =A= get_elem_trop N ip jp.

  Notation "M =m N" := (mat_eqA_trop M N) (at level 70).

  Lemma mat_eqA_refl_trop : forall m n (M : matrix_trop m n), M =m M.

  Proof.
    unfold mat_eqA_trop. refl.
  Qed.

  Lemma mat_eqA_sym_trop : forall m n (M N : matrix_trop m n),
    M =m N -> N =m M.

  Proof.
    unfold mat_eqA_trop. intros. sym. apply H.
  Qed.

  Lemma mat_eqA_trans_trop: forall m n (M N P : matrix_trop m n),
    M =m N -> N =m P -> M =m P.

  Proof.
    unfold mat_eqA_trop. intros. trans (get_elem_trop N ip jp); auto.
  Qed.

  Definition mat_eqA_st_trop : forall m n,
    Setoid_Theory (matrix_trop m n) (@mat_eqA_trop m n).

  Proof.
    constructor. unfold Reflexive. apply mat_eqA_refl_trop.
    unfold Symmetric. apply mat_eqA_sym_trop. unfold Transitive.
    apply mat_eqA_trans_trop.
  Qed.

  Add Parametric Relation m n : (matrix_trop m n) (@mat_eqA_trop m n)
    reflexivity proved by (@mat_eqA_refl_trop m n)
    symmetry proved by (@mat_eqA_sym_trop m n)
      transitivity proved by (@mat_eqA_trans_trop m n)
        as mat_eqA_rel_trop.

  Lemma mat_eq_trop : forall m n (M N : matrix_trop m n), 
    (forall i j (ip : i < m) (jp : j < n), 
      get_elem_trop M ip jp = get_elem_trop N ip jp) -> M = N.

  Proof.
    unfold matrix_trop. induction m; simpl; intros.
    VOtac. refl.
    unfold get_elem_trop, get_row_trop in H.
    VSntac M. VSntac N. apply Vcons_eq_intro.
    apply Veq_nth. intros.
    do 2 rewrite Vhead_nth. apply H.
    apply IHm. intros. 
    unfold get_elem_trop, get_row_trop. do 2 rewrite Vnth_tail. apply H.
  Qed.

  Add Parametric Morphism m n i (h:i<m) : (fun M => @get_row_trop m n M i h)
    with signature (@mat_eqA_trop m n) ==> (@eq_vec_trop n)
      as get_row_mor_trop.

  Proof.
    intros. apply Vforall2n_intro. intros. apply H.
  Qed.

  Add Parametric Morphism m n i (h:i<n) : (fun M => @get_col_trop m n M i h)
    with signature (@mat_eqA_trop m n) ==> (@eq_vec_trop m)
      as get_col_mor_trop.

  Proof.
    intros. apply Vforall2n_intro. intros.
    repeat rewrite <- get_elem_swap_trop. apply H.
  Qed.

  Add Parametric Morphism m n i j (ip:i<m) (jp:j<n) :
    (fun M => @get_elem_trop m n M i j ip jp)
    with signature (@mat_eqA_trop m n) ==> eqA
      as get_elem_mor_trop.

  Proof.
    unfold get_elem_trop. intros. apply H.
  Qed.

  (** Matrix construction over domain tropical. *)

  Definition mat_build_spec_trop : forall m n 
    (gen : forall i j, i < m -> j < n -> A), 
    { M : matrix_trop m n | forall i j (ip : i < m) (jp : j < n), 
      get_elem_trop M ip jp = gen i j ip jp }.

  Proof.
    induction m; intros.
    exists (Vnil (A:=vec n)). intros.
    elimtype False. exact (lt_n_O ip).
    set (gen_1 := fun j => gen 0 j (lt_O_Sn m)).
    set (gen' := fun i j H => gen (S i) j (lt_n_S H)).
    destruct (IHm n gen') as [Mtl Mtl_spec].
    destruct (Vbuild_spec gen_1) as [Mhd Mhd_spec].
    exists (Vcons Mhd Mtl). intros.    
    destruct i; unfold get_elem_trop; simpl.
    rewrite Mhd_spec. unfold gen_1. rewrite (le_unique (lt_O_Sn m) ip). refl.
    unfold get_elem_trop in Mtl_spec. rewrite Mtl_spec.
    unfold gen'. rewrite (le_unique (lt_n_S (lt_S_n ip)) ip). refl.
  Defined.

  Definition mat_build_trop m n gen : matrix_trop m n :=
    proj1_sig (mat_build_spec_trop gen).

  Lemma mat_build_elem_trop : forall m n gen i j (ip : i < m) (jp : j < n), 
    get_elem_trop (mat_build_trop gen) ip jp = gen i j ip jp.

  Proof.
    intros. unfold mat_build_trop. destruct (mat_build_spec_trop gen).
    simpl. apply e.
  Qed.

  Lemma mat_build_nth_trop : forall m n gen i j (ip : i < m) (jp : j < n),
    Vnth (Vnth (mat_build_trop gen) ip) jp = gen i j ip jp.

  Proof.
    intros. fold (get_row_trop (mat_build_trop gen) ip).
    fold (get_elem_trop (mat_build_trop gen) ip jp).
    apply mat_build_elem_trop.
  Qed.

  (** Some elementary matrices over domain tropical. *)

  Notation A0 := A0t.

  Definition zero_matrix_trop m n : matrix_trop m n :=
    mat_build_trop (fun i j ip jp => A0). 
  Definition id_matrix_trop (n: nat) : matrix_trop n n :=
    Vbuild (fun i ip => id_vec_trop ip).
  Definition inverse_matrix_trop inv m n (M : matrix_trop m n)
    : matrix_trop m n :=
    mat_build_trop (fun i j ip jp => inv (get_elem_trop M ip jp)).

  (** 1-row and 1-column matrices over domain tropical. *)

  Definition row_mat_trop n := matrix_trop 1 n.
  Definition col_mat_trop n := matrix_trop n 1.
  Definition vec_to_row_mat_trop n (v : vec n)
    : row_mat_trop n := Vcons v Vnil.
  Definition vec_to_col_mat_trop n (v : vec n) : col_mat_trop n := 
    Vmap (fun i => Vcons i Vnil) v.

  Add Parametric Morphism n : (@vec_to_col_mat_trop n)
    with signature (@eq_vec_trop n) ==> (@mat_eqA_trop n 1)
      as vec_to_col_mat_mor_trop.

  Proof.
    unfold vec_to_col_mat_trop, mat_eqA_trop, get_elem_trop. intros.
    repeat rewrite get_elem_swap_trop. unfold get_col_trop.
    repeat rewrite Vnth_map.
    apply (Vnth_mor eqA). rewrite (eq_vec_cons eqA). intuition.
    apply (Vnth_mor eqA). hyp.
  Qed.

  Definition row_mat_to_vec_trop n (m : row_mat_trop n) :=
    get_row_trop m access_0.
  Definition col_mat_to_vec_trop n (m : col_mat_trop n) :=
    get_col_trop m access_0.

  Ltac mat_get_simpl_trop :=
    repeat progress unfold get_elem_trop, get_col_trop, get_row_trop, 
      vec_to_col_mat_trop, vec_to_row_mat_trop, col_mat_to_vec_trop,
      row_mat_to_vec_trop;
      repeat progress ( try rewrite Vnth_map; try rewrite Vnth_map2);
        try refl.

  Lemma get_col_col_mat_trop : forall n (v : vec n) (p : 0 < 1),
    get_col_trop (vec_to_col_mat_trop v) p = v.

  Proof.
    induction v; intros.
    trivial.
    simpl.
    rewrite IHv. trivial.
  Qed.

  Lemma vec_to_col_mat_spec_trop : forall n (v : vec n) i (ip : i < n) j 
    (jp : j < 1), get_elem_trop (vec_to_col_mat_trop v) ip jp = Vnth v ip.
    
  Proof.
    intros. unfold get_elem_trop.
    rewrite get_elem_swap_trop.
    destruct j.
    rewrite get_col_col_mat_trop. trivial.
    absurd_arith.
  Qed.

  Lemma vec_to_row_mat_spec_trop : forall n (v : vec n) i (ip : i < 1) j 
    (jp : j < n), get_elem_trop (vec_to_row_mat_trop v) ip jp = Vnth v jp.

  Proof.
    intros. unfold get_elem_trop.
    destruct i. trivial. absurd_arith.
  Qed.

  Lemma Vnth_col_mat_trop : forall n (m : col_mat_trop n) i (ip : i < n),
    Vnth (col_mat_to_vec_trop m) ip = get_elem_trop m ip access_0.

  Proof.
    induction m; intros. absurd_arith.
    destruct i.
    trivial.
    simpl. rewrite IHm. trivial.
  Qed.

  Lemma Vnth_row_mat_trop : forall n (m : row_mat_trop n) i (ip : i < n),
    Vnth (row_mat_to_vec_trop m) ip = get_elem_trop m access_0 ip.

  Proof.
    trivial.
  Qed.

  Lemma col_mat_to_vec_idem_trop : forall n (v : vec n), 
    col_mat_to_vec_trop (vec_to_col_mat_trop v) = v.

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_trop.
  Qed.

  Lemma vec_to_col_mat_idem_trop : forall n (M : col_mat_trop n), 
    vec_to_col_mat_trop (col_mat_to_vec_trop M) = M.

  Proof.
    intros. apply mat_eq_trop. intros.
    mat_get_simpl_trop.
    destruct j. rewrite (lt_unique access_0 jp). refl.
    absurd_arith.
  Qed.

  Lemma row_mat_to_vec_idem_trop : forall n (v : vec n), 
    row_mat_to_vec_trop (vec_to_row_mat_trop v) = v.

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_trop.
  Qed.

  Lemma vec_to_row_mat_idem_trop : forall n (M : row_mat_trop n), 
    vec_to_row_mat_trop (row_mat_to_vec_trop M) = M.

  Proof.
    intros. apply mat_eq_trop. intros.
    mat_get_simpl_trop.
    destruct i. simpl. rewrite (lt_unique access_0 ip). refl.
    absurd_arith.
  Qed.

  (** Matrix transposition over domain tropical. *)

  Definition mat_transpose_trop m n (M : matrix_trop m n) := 
    mat_build_trop (fun _ _ i j => get_elem_trop M j i).

  Lemma mat_transpose_row_col_trop : forall m n (M : matrix_trop m n) i
    (ip : i < m), get_col_trop (mat_transpose_trop M) ip = get_row_trop M ip.

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_trop. unfold mat_transpose_trop.
    rewrite mat_build_nth_trop. trivial.
  Qed.

  Lemma mat_transpose_col_row_trop : forall m n (M : matrix_trop m n) i
    (ip : i < n), get_row_trop (mat_transpose_trop M) ip = get_col_trop M ip.

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_trop. unfold mat_transpose_trop.
    rewrite mat_build_nth_trop. trivial.
  Qed.

  Lemma mat_transpose_idem_trop : forall m n (M : matrix_trop m n),
    mat_transpose_trop (mat_transpose_trop M) = M.

  Proof.
    intros. apply mat_eq_trop. intros.
    unfold mat_transpose_trop. do 2 rewrite mat_build_elem_trop. refl.
  Qed.

  (** Matrix addition over domain tropical. *)
  
  Notation Aplus := Aplust.
  Notation Amult := Amultt.
  Notation "X + Y" := (Aplus X Y).
  Notation "X * Y" := (Amult X Y).
  Infix "[+]" := vector_plus_trop (at level 50).

  Definition vec_plus_trop n (L R : vec n) := Vmap2 Aplus L R.
  Definition mat_plus_trop m n (L R : matrix_trop m n) :=
    Vmap2 (@vec_plus_trop n) L R.
  Infix "<+>" := mat_plus_trop (at level 50).

  Lemma mat_plus_comm_trop : forall m n (L R : matrix_trop m n),
    L <+> R =m R <+> L.

  Proof.
    unfold mat_eqA_trop. intros. unfold mat_plus_trop, vec_plus_trop.
    mat_get_simpl_trop. ring.
  Qed.

  (** Matrix multiplication over tropical domain. *)

  Definition mat_mult_trop m n p (L : matrix_trop m n) (R : matrix_trop n p) :=
    mat_build_trop (fun i j ip jp => dot_product_trop (get_row_trop L ip)
      (get_col_trop R jp)).

  Infix "<*>" := mat_mult_trop (at level 40).

  Add Parametric Morphism m n p : (@mat_mult_trop m n p)
    with signature (@mat_eqA_trop m n) ==> (@mat_eqA_trop n p) ==> (@mat_eqA_trop m p)
      as mat_mult_mor_trop.

  Proof.
    unfold mat_mult_trop. intros. unfold mat_eqA_trop. intros.
    repeat rewrite mat_build_elem_trop. apply dot_product_mor_trop.
    apply get_row_mor_trop. hyp. apply get_col_mor_trop. hyp.
  Qed.
  
  Lemma mat_mult_elem_trop: forall m n p (M : matrix_trop m n)
    (N : matrix_trop n p) i (ip : i < m) j (jp : j < p), 
    Vnth (Vnth (M <*> N) ip) jp = dot_product_trop (get_row_trop M ip)
    (get_col_trop N jp).

  Proof.
    intros. unfold mat_mult_trop. rewrite mat_build_nth_trop. refl.
  Qed.

  Lemma mat_mult_spec_trop : forall m n p (M : matrix_trop m n)
    (N : matrix_trop n p) i (ip : i < m) j (jp : j < p), 
    get_elem_trop (M <*> N) ip jp = dot_product_trop (get_row_trop M ip)
    (get_col_trop N jp).

  Proof.
    intros.
    mat_get_simpl_trop. rewrite mat_mult_elem_trop. refl.
  Qed.

  Lemma mat_mult_row_trop : forall m n p (M : matrix_trop m n)
    (N : matrix_trop n p) i (ip : i < m),
    get_row_trop (M <*> N) ip = 
    Vbuild (fun j jp => dot_product_trop (get_row_trop M ip)
      (get_col_trop N jp)).

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_trop. 
    rewrite mat_mult_elem_trop. rewrite Vbuild_nth. refl.
  Qed.

  Lemma mat_mult_col_trop : forall m n p (M : matrix_trop m n)
    (N : matrix_trop n p) j (jp : j < p),
    get_col_trop (M <*> N) jp = 
    Vbuild (fun i ip => dot_product_trop (get_row_trop M ip)
      (get_col_trop N jp)).

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl_trop. 
    rewrite mat_mult_elem_trop. rewrite Vbuild_nth. refl.
  Qed.

  Lemma mat_mult_id_l_trop : forall n p (np : n >= p) (M : matrix_trop n p), 
    id_matrix_trop n <*> M =m M.

  Proof.
    unfold mat_eqA_trop. intros. rewrite mat_mult_spec_trop.
    unfold id_matrix_trop, get_row_trop. rewrite Vbuild_nth.
    rewrite (dot_product_id_trop ip). mat_get_simpl_trop.
  Qed.

  Lemma zero_matrix_mult_l_trop : forall m n p (M : matrix_trop n p), 
    zero_matrix_trop m n <*> M =m zero_matrix_trop m p.

  Proof.
    unfold mat_eqA_trop. intros.
    unfold zero_matrix_trop at 2.
    mat_get_simpl_trop.
    fold (get_row_trop (zero_matrix_trop m n <*> M) ip).
    fold (get_elem_trop (zero_matrix_trop m n <*> M) ip jp).
    rewrite mat_mult_spec_trop. rewrite dot_product_zero_trop. 
    rewrite mat_build_nth_trop. refl.
    apply Vforall_nth_intro. intros.
    unfold zero_matrix_trop. mat_get_simpl_trop.
    rewrite mat_build_nth_trop. refl.
  Qed.

  Lemma dot_product_assoc_trop : forall m n v v' (M : matrix_trop m n),
    dot_product_trop v (Vbuild (fun i (ip : i < m ) => 
      dot_product_trop (get_row_trop M ip) v')) =A=
    dot_product_trop (Vbuild (fun j (jp : j < n) =>
      dot_product_trop v (get_col_trop M jp))) v'.
    
  Proof.
    induction m; intros.
    (* induction base *)
    VOtac. repeat rewrite dot_product_zero_trop. 
    refl.
    apply Vforall_nth_intro. intros. rewrite Vbuild_nth.
    unfold SemiRing2.eqAr. refl.
    apply Vforall_intro. intros. destruct H.
    (* induction case *)
    VSntac v.
    rewrite (VSn_eq (Vbuild (fun i ip => dot_product_trop (get_row_trop M ip) v'))).
    rewrite dot_product_cons_trop. do 2 rewrite Vhead_nth. rewrite Vbuild_nth.
    rewrite Vbuild_tail. unfold matrix_trop in M. VSntac M. simpl.
    match goal with
      |- _ + dot_product_trop _ (Vbuild ?gen) =A= _ => replace (Vbuild gen) with 
        (Vbuild (fun i ip => dot_product_trop (get_row_trop (Vtail M) ip) v')) end.
    rewrite (IHm n (Vtail v) v' (Vtail M)).
    set (a := Vbuild (fun (j : nat) (jp : j < n) =>
      dot_product_trop (Vtail v) (get_col_trop (Vtail M) jp))).
    set (b := Vbuild (fun (j : nat) (jp : j < n) =>
      dot_product_trop (Vcons (Vnth v (lt_O_Sn m)) (Vtail v))
      (Vcons (Vnth (Vhead M) jp) (get_col_trop (Vtail M) jp)))).
    set (c := Vbuild (fun j jp => Vnth v (lt_O_Sn m) * (Vnth (Vhead M) jp))).
    set (d := Vbuild (fun j jp =>
      dot_product_trop (Vtail v) (get_col_trop (Vtail M) jp))).
    assert (b =v c [+] d). apply Vforall2n_intro. intros.
    rewrite vector_plus_nth_trop. unfold b, c, d. do 3 rewrite Vbuild_nth.
    rewrite dot_product_cons_trop. refl. trans (dot_product_trop (c[+]d) v').
    rewrite dot_product_distr_l_trop. rewrite dot_product_distr_mult_trop. refl.
    apply dot_product_mor_trop. sym. hyp. refl.
    apply Veq_nth. intros. do 2 rewrite Vbuild_nth. rewrite lt_Sn_nS. refl.
  Qed.

  Lemma mat_mult_assoc_trop : forall m n p l 
    (M : matrix_trop m n) (N : matrix_trop n p) (P : matrix_trop p l),
    M <*> (N <*> P) =m M <*> N <*> P.

  Proof.
    unfold mat_eqA_trop. intros. 
    mat_get_simpl_trop. repeat rewrite mat_mult_elem_trop.
    rewrite mat_mult_row_trop. rewrite mat_mult_col_trop.
    apply dot_product_assoc_trop.
  Qed.

  (** Matrix-col vector product over domain tropical. *)

  Definition mat_vec_prod_trop m n (m : matrix_trop m n) (v : vec n) :=
    col_mat_to_vec_trop (m <*> (vec_to_col_mat_trop v)).

  Add Parametric Morphism m n : (@mat_vec_prod_trop m n)
    with signature (@mat_eqA_trop m n) ==> (@eq_vec_trop n) ==> (@eq_vec_trop m)
      as mat_vec_prod_mor_trop.

  Proof.
    unfold mat_vec_prod_trop. intros. apply get_col_mor_trop.
    rewrite H. rewrite H0.
    refl.
  Qed.

  Lemma mat_vec_prod_distr_vec_trop : forall m n (M : matrix_trop m n) v1 v2,
    mat_vec_prod_trop M (v1 [+] v2) =v
    mat_vec_prod_trop M v1 [+] mat_vec_prod_trop M v2.

  Proof.
    intros. unfold mat_vec_prod_trop. apply Vforall2n_intro. intros.
    rewrite vector_plus_nth_trop. mat_get_simpl_trop.
    repeat rewrite mat_mult_elem_trop. rewrite <- dot_product_distr_r_trop.
    apply dot_product_mor_trop. refl.
    apply Vforall2n_intro. intros. unfold get_col_trop.
    repeat rewrite Vnth_map. simpl. rewrite vector_plus_nth_trop.
    unfold vector_plus_trop. rewrite Vnth_map2. repeat rewrite Vnth_map. refl.
  Qed.

  Lemma mat_vec_prod_distr_mat_trop : forall m n (Ml Mr : matrix_trop m n) v,
    mat_vec_prod_trop (Ml <+> Mr) v =v
    mat_vec_prod_trop Ml v [+] mat_vec_prod_trop Mr v.

  Proof.
    intros. unfold mat_vec_prod_trop. apply Vforall2n_intro. intros.
    rewrite vector_plus_nth_trop. mat_get_simpl_trop.
    repeat rewrite mat_mult_elem_trop.
    set (a := get_col_trop (Vmap (fun i0 : A => Vcons i0 Vnil) v) access_0).
    rewrite (dot_product_comm_trop (get_row_trop Ml ip)).
    rewrite (dot_product_comm_trop (get_row_trop Mr ip)).
    rewrite <- dot_product_distr_r_trop.
    rewrite dot_product_comm_trop. apply dot_product_mor_trop. refl. clear a.
    unfold get_row_trop, mat_plus_trop. rewrite Vnth_map2. refl.
  Qed.

  Lemma mat_vec_prod_distr_add_vectors_trop : forall m n (M : matrix_trop m n) 
    k v1 v2,(forall i (ip : i < k), mat_vec_prod_trop M (Vnth v1 ip) =v Vnth v2 ip) ->
    mat_vec_prod_trop M (add_vectors_trop v1) =v add_vectors_trop v2.
    
  Proof.
    induction k; intros.
    (* induction base *)
    VOtac. unfold add_vectors_trop. simpl.
    apply Vforall2n_intro. intros.
    unfold mat_vec_prod_trop. rewrite Vnth_col_mat_trop.
    unfold zero_vec_trop. rewrite Vnth_const.
    rewrite mat_mult_spec_trop. 
    rewrite dot_product_comm_trop. rewrite dot_product_zero_trop. refl.
    apply Vforall_nth_intro. intros.
    rewrite get_col_col_mat_trop. rewrite Vnth_const. refl.
    (* induction step *)
    VSntac v1. VSntac v2. 
    do 2 rewrite add_vectors_cons_trop. rewrite mat_vec_prod_distr_vec_trop.
    do 2 rewrite Vhead_nth. apply vector_plus_mor_trop. rewrite H. refl.
    rewrite (IHk (Vtail v1) (Vtail v2)). refl.
    intros. rewrite Vnth_tail. rewrite H.
    rewrite Vnth_tail. refl.
  Qed.

End Matrix_tropic.

(** forall over domain tropical. *)

Section Forall_trop.

  Variables (P : At -> Prop) (m n : nat) (M : matrix_trop m n).

  Definition mat_forall_trop := forall i j (ip : i < m) (jp : j < n), 
    P (get_elem_trop M ip jp).

  (* Alternative definition. *)

  Definition mat_forall_trop' := Vforall (@Vforall At P n) M.

End Forall_trop.

(** forall2 over domain tropical. *)

Section Forall2_trop.

  Variables (P : relation At) (m n : nat).

  Definition mat_forall2_trop (M N : matrix_trop m n):= forall i j (ip : i < m) 
    (jp : j < n), P (get_elem_trop M ip jp) (get_elem_trop N ip jp).

  Definition mat_forall2_intro_trop : forall M N,
    (forall i j (ip : i < m) (jp : j < n), 
      P (get_elem_trop M ip jp) (get_elem_trop N ip jp)) ->
    mat_forall2_trop M N := fun M N H => H.

  (** Alternative definition. *)

  Definition mat_forall2'_trop (M N : matrix_trop m n) := 
    Vforall2n (@Vforall2n At At P n) M N.

  Require Import RelMidex.

  Variable P_dec : rel_dec P.

  Lemma mat_forall2'_dec_trop : rel_dec mat_forall2'_trop.

  Proof.
    intros M N. unfold mat_forall2'_trop. do 2 apply Vforall2n_dec. hyp.
  Defined.

  Lemma mat_forall2_equiv1_trop : forall M N, 
    mat_forall2_trop M N -> mat_forall2'_trop M N.

  Proof.
    intros. unfold mat_forall2'_trop. do 2 (apply Vforall2n_intro; intros). 
    exact (H i i0 ip ip0).
  Qed.

  Lemma mat_forall2_equiv2_trop : forall M N, 
    mat_forall2'_trop M N -> mat_forall2_trop M N.

  Proof.
    intros. unfold mat_forall2_trop, get_elem_trop, get_row_trop. intros.
    apply Vforall2n_nth. apply Vforall2n_nth. hyp.
  Qed.

  Lemma mat_forall2_dec_trop : rel_dec mat_forall2_trop.

  Proof.
    intros M N. destruct (mat_forall2'_dec_trop M N).
    left. apply mat_forall2_equiv2_trop. hyp.
    right. intro. apply n0. apply mat_forall2_equiv1_trop. hyp.
  Defined.

End Forall2_trop.

Hint Rewrite mat_mult_id_l_trop zero_matrix_mult_l_trop using simpl : arith.

(** 'monotonicity' of matrix multiplication over domain tropical. *)

Section MatMultMonotonicity_trop.

  Notation ge := get.

  Variables (m n p : nat) (M M' : matrix_trop m n) (N N' : matrix_trop n p).

  Definition mat_ge_trop := mat_forall2_trop get.
  Infix ">=m" := mat_ge_trop (at level 70).

  Lemma mat_ge_refl_trop : M >=m M.

  Proof.
    unfold mat_ge_trop, mat_forall2_trop. 
    intros. apply ge_reflt.
  Qed.

  Lemma mat_ge_dec_trop : forall m n, rel_dec (@mat_ge_trop m n).

  Proof.
    intros R Q. unfold mat_ge_trop. apply mat_forall2_dec_trop.
    exact ge_dect.
  Defined.

  Infix "<*>" := mat_mult_trop (at level 40).
  Infix ">=v" := vec_ge_trop (at level 70).
  Notation Aplus := Aplust.
  Notation Amult := Amultt.
  Notation "x >>= y" := (get x y) (at level 70).
  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).
  Parameter plus_ge_compat_trop : forall m n m' n',
    m >>= m' -> n >>= n' -> m + n >>= m' + n'.
  Parameter mult_ge_compat_trop : forall m n m' n',
    m >>= m' -> n >>= n' -> m * n >>= m' * n'.
  Hint Resolve ge_reflt : arith.
  Notation vec := (vector At).

  Lemma dot_product_mon_trop : forall i (v v' w w' : vec i), v >=v v' -> 
    w >=v w' -> dot_product_trop v w >>= dot_product_trop v' w'.

  Proof.
    unfold dot_product_trop. induction v. auto with arith. 
    intros. simpl.
    apply plus_ge_compat_trop.
    apply IHv.
    change v with (Vtail (Vcons h v)). apply Vreln_tail_intro. hyp.
    apply Vreln_tail_intro. hyp.
    set (p0 := lt_O_Sn n0). apply mult_ge_compat_trop.
    change h with (Vnth (Vcons h v) p0). rewrite Vhead_nth.
    apply Vforall2n_nth. hyp.
    do 2 rewrite Vhead_nth. apply Vforall2n_nth. hyp.
  Qed.

  Lemma mat_mult_mon_trop : M >=m M' -> N >=m N' -> M <*> N >=m M' <*> N'.

  Proof.
    intros. unfold mat_ge_trop, mat_forall2_trop. intros.
    do 2 rewrite mat_mult_spec_trop. apply dot_product_mon_trop.
    apply Vforall2n_intro. intros.
    exact (H i i0 ip ip0).
    apply Vforall2n_intro. intros.
    do 2 rewrite <- get_elem_swap_trop. exact (H0 i0 j ip0 jp).
  Qed.

End MatMultMonotonicity_trop.

Infix ">=v" := vec_ge_trop (at level 70).

Lemma mat_vec_prod_ge_compat_trop : forall i j (M M' : matrix_trop i j) m m', 
  mat_ge_trop M M' -> m >=v m' -> mat_vec_prod_trop M m >=v mat_vec_prod_trop M' m'.

Proof.
  intros. unfold mat_vec_prod_trop, vec_ge_trop. apply Vforall2n_intro.
  intros. do 2 rewrite Vnth_col_mat_trop. apply mat_mult_mon_trop. hyp.
  unfold mat_ge_trop. intros k l pk pl. do 2 rewrite vec_to_col_mat_spec_trop.
  apply Vforall2n_nth. hyp.
Qed.

Infix ">=m" := mat_ge_trop (at level 70).