(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frédéric Blanqui, 2009-03-23 (setoid), 2014-02-19 (classes)
- Adam Koprowski and Hans Zantema, 2007-03

Matrices.
*)

Require Import VecArith2 OrdSemiRing2 VecUtil NatUtil LogicUtil Relations List
  Setoid Morphisms RelUtil RelMidex.

Set Implicit Arguments.

(***********************************************************************)
(** ** Definitions of constants and operations. *)

Section def.

  Context {OSR : OrderedSemiRing}. Import OSR_Notations.

  Notation vec := (vector s_typ).

  (** Matrices are represented by a vector of row vectors. *)

  Definition matrix m n := vector (vec n) m.

  (** Accessors. *)

  Definition get_row m n (M : matrix m n) i (ip : i < m) := Vnth M ip.

  Definition get_col m n (M : matrix m n) i (ip : i < n) := 
    Vmap (fun v => Vnth v ip) M.

  Definition get_elem m n (M : matrix m n) i j (ip : i < m) (jp : j < n) :=
    Vnth (get_row M ip) jp.

  (** Equality. *)

  Definition mat_eqA m n (M N : matrix m n) :=
    forall i j (ip : i < m) (jp : j < n),
      get_elem M ip jp == get_elem N ip jp.

  (** Constructor. *)

  Definition mat_build_spec : forall m n 
    (gen : forall i j, i < m -> j < n -> s_typ), 
    { M : matrix m n | forall i j (ip : i < m) (jp : j < n), 
      get_elem M ip jp = gen i j ip jp }.

  Proof.
    induction m; intros.
    exists (Vnil (A:=vec n)). intros.
    elimtype False. exact (lt_n_O ip).
    set (gen_1 := fun j => gen 0%nat j (lt_O_Sn m)).
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

  (** Some elementary matrices. *)

  Definition zero_matrix m n : matrix m n := mat_build (fun i j ip jp => 0).

  Definition id_matrix n : matrix n n := Vbuild (fun i ip => id_vec ip).

  (** Map function. *)

  Definition map_matrix f m n (M : matrix m n) : matrix m n :=
    mat_build (fun _ _ ip jp => f (get_elem M ip jp)).

  (** Row and column matrices, and their conversion to vectors. *)

  Definition row_mat n := matrix 1 n.
  Definition col_mat n := matrix n 1.

  Definition vec_to_row_mat n (v : vec n) : row_mat n := Vcons v Vnil.

  Definition vec_to_col_mat n (v : vec n) : col_mat n := 
    Vmap (fun i => Vcons i Vnil) v.

  Lemma access_0 : 0 < 1. Proof. omega. Qed.

  Definition row_mat_to_vec n (m : row_mat n) := get_row m access_0.
  Definition col_mat_to_vec n (m : col_mat n) := get_col m access_0.

  (** Transposition. *)

  Definition mat_transpose m n (M : matrix m n) := 
    mat_build (fun _ _ i j => get_elem M j i).

  (** Addition. *)

  Definition mat_plus m n (L R : matrix m n) := Vmap2 (vector_plus (n:=n)) L R.

  (** Multiplication. *)

  Definition mat_mult m n p (L : matrix m n) (R : matrix n p) :=
    mat_build (fun i j ip jp => dot_product (get_row L ip) (get_col R jp)).

  (** Matrix-vector product. *)

  Definition mat_vec_prod m n (M : matrix m n) (v : vec n) :=
    col_mat_to_vec (mat_mult M (vec_to_col_mat v)).

End def.

Arguments mat_eqA {OSR} m n _ _.
Arguments id_matrix {OSR} [n].
Arguments zero_matrix {OSR} [m n].

(** Notations. *)

Infix "=m" := (mat_eqA _ _) (at level 70).
Infix "<+>" := mat_plus (at level 50).
Infix "<*>" := mat_mult (at level 40).

(** Tactics. *)

Ltac mat_get_simpl :=
  repeat progress unfold get_elem, get_col, get_row, 
    vec_to_col_mat, vec_to_row_mat, col_mat_to_vec, row_mat_to_vec; 
  repeat progress ( try rewrite Vnth_map; try rewrite Vnth_map2 );
  ring_simplify; try refl.

(***********************************************************************)
(** ** Properties of operations. *)

Section props.

  Context {OSR : OrderedSemiRing}. Import OSR_Notations. Add Ring OSR : sr_th.

  Notation vec := (vector s_typ).

  Notation veq := (Vforall2 s_eq). Infix "=v" := veq (at level 70).

  Notation vge := (Vforall2 osr_ge). Infix ">=v" := vge (at level 70).

  (***********************************************************************)
  (** Equality. *)

  Global Instance mat_eqA_refl m n : Reflexive (mat_eqA m n).

  Proof. intros M i j hi hj. refl. Qed.

  Global Instance mat_eqA_sym m n : Symmetric (mat_eqA m n).

  Proof. intros M N MN i j hi hj. sym. apply MN. Qed.

  Global Instance mat_eqA_trans m n : Transitive (mat_eqA m n).

  Proof.
    intros M N P MN NP i j hi hj. trans (get_elem N hi hj). apply MN. apply NP.
  Qed.

  (*REMOVE?*)
  Global Instance mat_eqA_equiv m n : Equivalence (mat_eqA m n).

  Proof. constructor; class. Qed.

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

  (***********************************************************************)
  (** Accessors. *)

  Lemma get_elem_swap : forall m n (M : matrix m n) i j (ip : i < m) 
    (jp : j < n), Vnth (get_row M ip) jp = Vnth (get_col M jp) ip.

  Proof.
    induction M; intros. absurd_arith.
    destruct i.
    trivial.
    simpl. rewrite IHM. trivial.
  Qed.

  Global Instance get_row_mor m n i (h:i<m) :
    Proper (mat_eqA m n ==> veq) (fun M => get_row M h).

  Proof. intros M N MN. apply Vforall2_intro_nth. intros. apply MN. Qed.

  Global Instance get_col_mor m n i (h:i<n) :
    Proper (mat_eqA m n ==> veq) (fun M => get_col M h).

  Proof.
    intros M N MN. apply Vforall2_intro_nth. intros. rewrite <- !get_elem_swap.
    apply MN.
  Qed.

  Global Instance get_elem_mor m n i j (ip:i<m) (jp:j<n) :
    Proper (mat_eqA m n ==> s_eq) (fun M => get_elem M ip jp).

  Proof. intros M N MN. apply MN. Qed.

  (***********************************************************************)
  (** [mat_build]. *)

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

  (***********************************************************************)
  (** Row and column matrices. *)

  Global Instance vec_to_col_mat_mor n :
    Proper (veq ==> mat_eqA n 1) (vec_to_col_mat (n:=n)).

  Proof.
    unfold vec_to_col_mat, mat_eqA, get_elem. intros u u' uu' i j ip jp.
    rewrite !get_elem_swap. unfold get_col. rewrite !Vnth_map.
    apply Vforall2_elim_nth. rewrite Vforall2_cons_eq. intuition.
    apply Vforall2_elim_nth. hyp.
  Qed.

  Lemma get_col_col_mat : forall n (v : vec n) (p : 0 < 1),
    get_col (vec_to_col_mat v) p = v.

  Proof. induction v; intros. trivial. simpl. rewrite IHv. trivial. Qed.

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

  Proof. intros. unfold get_elem. destruct i. trivial. absurd_arith. Qed.

  Lemma Vnth_col_mat : forall n (m : col_mat n) i (ip : i < n),
    Vnth (col_mat_to_vec m) ip = get_elem m ip access_0.

  Proof.
    induction m; intros. absurd_arith.
    destruct i. trivial. simpl. rewrite IHm. trivial.
  Qed.

  Lemma Vnth_row_mat : forall n (m : row_mat n) i (ip : i < n),
    Vnth (row_mat_to_vec m) ip = get_elem m access_0 ip.

  Proof. trivial. Qed.

  Lemma col_mat_to_vec_idem : forall n (v : vec n), 
    col_mat_to_vec (vec_to_col_mat v) = v.

  Proof. intros. apply Veq_nth. intros. mat_get_simpl. Qed.

  Lemma vec_to_col_mat_idem : forall n (M : col_mat n), 
    vec_to_col_mat (col_mat_to_vec M) = M.

  Proof.
    intros. apply mat_eq. intros. mat_get_simpl.
    destruct j. rewrite (lt_unique access_0 jp). refl.
    absurd_arith.
  Qed.

  Lemma row_mat_to_vec_idem : forall n (v : vec n), 
    row_mat_to_vec (vec_to_row_mat v) = v.

  Proof. intros. apply Veq_nth. intros. mat_get_simpl. Qed.

  Lemma vec_to_row_mat_idem : forall n (M : row_mat n), 
    vec_to_row_mat (row_mat_to_vec M) = M.

  Proof.
    intros. apply mat_eq. intros. mat_get_simpl.
    destruct i. simpl. rewrite (lt_unique access_0 ip). refl.
    absurd_arith.
  Qed.

  (***********************************************************************)
  (** Transposition. *)

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

  (***********************************************************************)
  (** Addition. *)

  Lemma mat_plus_comm : forall m n (L R : matrix m n), L <+> R =m R <+> L.

  Proof.
    unfold mat_eqA. intros. unfold mat_plus, vector_plus. mat_get_simpl.
  Qed.

  (***********************************************************************)
  (** Multiplication. *)

  Global Instance mat_mult_mor m n p :
    Proper (mat_eqA m n ==> mat_eqA n p ==> mat_eqA m p)
           (mat_mult (m:=m) (n:=n) (p:=p)).

  Proof.
    intros M M' MM' N N' NN'. unfold mat_mult. intros. unfold mat_eqA. intros.
    rewrite !mat_build_elem. apply dot_product_mor.
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
    intros. mat_get_simpl. rewrite mat_mult_elem. refl.
  Qed.

  Lemma mat_mult_row : forall m n p (M : matrix m n) (N : matrix n p) 
    i (ip : i < m),
    get_row (M <*> N) ip = 
    Vbuild (fun j jp => dot_product (get_row M ip) (get_col N jp)).

  Proof.
    intros. apply Veq_nth. intros. mat_get_simpl. 
    rewrite mat_mult_elem. rewrite Vbuild_nth. refl.
  Qed.

  Lemma mat_mult_col : forall m n p (M : matrix m n) (N : matrix n p) 
    j (jp : j < p),
    get_col (M <*> N) jp = 
    Vbuild (fun i ip => dot_product (get_row M ip) (get_col N jp)).

  Proof.
    intros. apply Veq_nth. intros. mat_get_simpl. 
    rewrite mat_mult_elem. rewrite Vbuild_nth. refl.
  Qed.

  Lemma mat_mult_id_l : forall n p (np : n >= p) (M : matrix n p), 
    id_matrix <*> M =m M.

  Proof.
    unfold mat_eqA. intros. rewrite mat_mult_spec.
    unfold id_matrix, get_row. rewrite Vbuild_nth.
    rewrite (dot_product_id ip). mat_get_simpl.
  Qed.

  Lemma zero_matrix_mult_l : forall m n p (M : matrix n p), 
    zero_matrix <*> M =m zero_matrix (m:=m).

  Proof.
    unfold mat_eqA. intros.
    unfold zero_matrix at 2. mat_get_simpl.
    fold (get_row (zero_matrix <*> M) ip).
    fold (get_elem (zero_matrix <*> M) ip jp).
    rewrite mat_mult_spec. rewrite dot_product_zero. 
    rewrite mat_build_nth. refl.
    apply Vforall_nth_intro. intros.
    unfold zero_matrix. mat_get_simpl. rewrite mat_build_nth. refl.
  Qed.

  Lemma dot_product_assoc : forall m n v v' (M : matrix m n),
    dot_product v (Vbuild (fun i (ip : i < m ) => 
      dot_product (get_row M ip) v')) ==
    dot_product (Vbuild (fun j (jp : j < n) =>
      dot_product v (get_col M jp))) v'.
  
  Proof.
    induction m; intros.
     (* induction base *)
    VOtac. rewrite !dot_product_zero. refl.
    apply Vforall_nth_intro. intros. rewrite Vbuild_nth. 
    unfold dot_product. refl.
    apply Vforall_intro. intros. destruct H.
     (* induction case *)
    VSntac v.
    rewrite (VSn_eq (Vbuild (fun i ip => dot_product (get_row M ip) v'))).
    rewrite dot_product_cons. do 2 rewrite Vhead_nth. rewrite Vbuild_nth.
    rewrite Vbuild_tail. unfold matrix in M. VSntac M. simpl.
    match goal with
    |- _ + dot_product _ (Vbuild ?gen) == _ => replace (Vbuild gen) with 
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
    assert (b =v c [+] d). apply Vforall2_intro_nth. intros.
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
    unfold mat_eqA. intros. mat_get_simpl.
    rewrite !mat_mult_elem, mat_mult_row, mat_mult_col.
    apply dot_product_assoc.
  Qed.

  (***********************************************************************)
  (** Matrix-vector product. *)

  Global Instance mat_vec_prod_mor m n :
    Proper (mat_eqA m n ==> veq ==> veq) (mat_vec_prod (m:=m) (n:=n)).

  Proof.
    intros M M' MM' v v' vv'. unfold mat_vec_prod. apply get_col_mor.
    rewrite MM', vv'. refl.
  Qed.

  Lemma mat_vec_prod_distr_vec : forall m n (M : matrix m n) v1 v2,
    mat_vec_prod M (v1 [+] v2) =v
    mat_vec_prod M v1 [+] mat_vec_prod M v2.

  Proof.
    intros. unfold mat_vec_prod. apply Vforall2_intro_nth. intros.
    rewrite vector_plus_nth. mat_get_simpl.
    rewrite !mat_mult_elem, <- dot_product_distr_r.
    apply dot_product_mor. refl.
    apply Vforall2_intro_nth. intros. unfold get_col.
    rewrite !Vnth_map. simpl. rewrite vector_plus_nth.
    unfold vector_plus. rewrite Vnth_map2, !Vnth_map. refl.
  Qed.

  Lemma mat_vec_prod_distr_mat : forall m n (Ml Mr : matrix m n) v,
    mat_vec_prod (Ml <+> Mr) v =v
    mat_vec_prod Ml v [+] mat_vec_prod Mr v.

  Proof.
    intros. unfold mat_vec_prod. apply Vforall2_intro_nth. intros.
    rewrite vector_plus_nth. mat_get_simpl. rewrite !mat_mult_elem.
    set (a := get_col (Vmap (fun i => Vcons i Vnil) v) access_0).
    rewrite (dot_product_comm (get_row Ml ip)),
      (dot_product_comm (get_row Mr ip)), <- dot_product_distr_r,
      (dot_product_comm a). apply dot_product_mor. 2: refl. clear a.
    unfold get_row, mat_plus. rewrite Vnth_map2. refl.
  Qed.

  Lemma mat_vec_prod_distr_add_vectors : forall m n (M : matrix m n) k v1 v2,
    (forall i (ip : i < k), mat_vec_prod M (Vnth v1 ip) =v Vnth v2 ip) ->
    mat_vec_prod M (add_vectors v1) =v add_vectors v2.
    
  Proof.
    induction k; intros.
     (* induction base *)
    VOtac. unfold add_vectors. simpl.
    apply Vforall2_intro_nth. intros.
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

  Hint Rewrite mat_mult_id_l zero_matrix_mult_l using simpl : arith.

  (***********************************************************************)
  (** Forall. *)

  Section Forall.

    Variables (P : s_typ -> Prop) (m n : nat) (M : matrix m n).

    Definition mat_forall := forall i j (ip : i < m) (jp : j < n), 
      P (get_elem M ip jp).

    (* Alternative definition. *)
    Definition mat_forall' := Vforall (Vforall P (n:=n)) M.

  End Forall.

  (***********************************************************************)
  (** Forall2. *)

  Section Forall2.

    Variables (P : relation s_typ) (m n : nat).

    Definition mat_forall2 (M N : matrix m n):= forall i j (ip : i < m) 
      (jp : j < n), P (get_elem M ip jp) (get_elem N ip jp).

    Definition mat_forall2_intro : forall M N,
      (forall i j (ip : i < m) (jp : j < n), 
        P (get_elem M ip jp) (get_elem N ip jp)) ->
      mat_forall2 M N := fun M N H => H.

    (* Alternative definition. *)
    Definition mat_forall2' (M N : matrix m n) := 
      Vforall2 (Vforall2 P (n:=n)) M N.

    Variable P_dec : rel_dec P.

    Lemma mat_forall2'_dec : rel_dec mat_forall2'.

    Proof.
      intros M N. unfold mat_forall2'. do 2 apply Vforall2_dec. hyp.
    Defined.

    Lemma mat_forall2_equiv1 : forall M N, 
      mat_forall2 M N -> mat_forall2' M N.

    Proof.
      intros. unfold mat_forall2'. do 2 (apply Vforall2_intro_nth; intros). 
      exact (H i i0 ip ip0).
    Qed.

    Lemma mat_forall2_equiv2 : forall M N, 
      mat_forall2' M N -> mat_forall2 M N.

    Proof.
      intros. unfold mat_forall2, get_elem, get_row. intros.
      apply Vforall2_elim_nth. apply Vforall2_elim_nth. hyp.
    Qed.

    Lemma mat_forall2_dec : rel_dec mat_forall2.

    Proof.
      intros M N. destruct (mat_forall2'_dec M N).
      left. apply mat_forall2_equiv2. hyp.
      right. intro. apply n0. apply mat_forall2_equiv1. hyp.
    Defined.

  End Forall2.

  (***********************************************************************)
  (** Monotonicity of matrix multiplication over naturals. *)

  Section MatMultMonotonicity.

    Variables (m n p : nat) (M M' : matrix m n) (N N' : matrix n p).

    Definition mat_ge := mat_forall2 osr_ge.

    Infix ">=m" := mat_ge (at level 70).

    Lemma mat_ge_refl : M >=m M.

    Proof. unfold mat_ge, mat_forall2. refl. Qed.

    Lemma mat_ge_dec : forall m n, rel_dec (@mat_ge m n).

    Proof.
      intros R Q. unfold mat_ge. apply mat_forall2_dec. exact osr_ge_dec.
    Defined.

    (* Add: Define boolean function [mat_ge] of type [s_typ]. *)

    Definition bmat_ge (m n: nat) (M N: matrix m n) :=
      match mat_ge_dec M N with
        | left _ => true
        | right _ => false
      end.
    
    (* Add: Correctness proof of [mat_ge]. *)
    
    Lemma bmat_ge_ok : forall (m n: nat) (M N : matrix m n),
                         bmat_ge M N = true <-> mat_ge M N.
    Proof.
      intros m0 n0 M0 N0. unfold bmat_ge. case_eq (mat_ge_dec M0 N0); intuition.
    Qed.

    Lemma dot_product_mon : forall i (v v' w w' : vec i),
      v >=v v' -> w >=v w' -> dot_product v w >>= dot_product v' w'.

    Proof.
      unfold dot_product. induction v; intros; simpl. refl.
      apply osr_add_ge. apply IHv.
      change v with (Vtail (Vcons h v)). apply Vforall2_tail. hyp.
      apply Vforall2_tail. hyp.
      set (p0 := lt_O_Sn n0). apply osr_mul_ge.
      change h with (Vnth (Vcons h v) p0). rewrite Vhead_nth.
      apply Vforall2_elim_nth. hyp.
      do 2 rewrite Vhead_nth. apply Vforall2_elim_nth. hyp.
    Qed.

    Lemma mat_mult_mon : M >=m M' -> N >=m N' -> M <*> N >=m M' <*> N'.

    Proof.
      intros. unfold mat_ge, mat_forall2. intros.
      do 2 rewrite mat_mult_spec. apply dot_product_mon.
      apply Vforall2_intro_nth. intros.
      exact (H i i0 ip ip0).
      apply Vforall2_intro_nth. intros.
      do 2 rewrite <- get_elem_swap. exact (H0 i0 j ip0 jp).
    Qed.

  End MatMultMonotonicity.

  (*FIXME: Proper*)
  Lemma mat_vec_prod_ge_compat : forall i j (M M' : matrix i j) m m', 
    mat_ge M M' -> m >=v m' -> mat_vec_prod M m >=v mat_vec_prod M' m'.

  Proof.
    intros. unfold mat_vec_prod. apply Vforall2_intro_nth. 
    intros. do 2 rewrite Vnth_col_mat. apply mat_mult_mon. hyp.
    unfold mat_ge. intros k l pk pl. do 2 rewrite vec_to_col_mat_spec.
    apply Vforall2_elim_nth. hyp.
  Qed.

  Infix ">=m" := mat_ge (at level 70).

End props.
