
(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski, 2007-04-02

* Arithmetic over vectors on some semiring.

*)

Set Implicit Arguments.

Require Import VecUtil RelUtil SemiRing2 RelExtras2 OrdSemiRing2
  NatUtil LogicUtil VecEq Setoid VecOrd ArithRing.

(***********************************************************************)
(** ** Vector arith with type natural numbers. *)

Section VectorArith_nat.

  Notation eqA := eqAN.
  Notation sid_theoryA := sid_theoryAN.
  Notation A_semi_ring := A_semi_ringN.
  Notation "X =A= Y" := (eqAN X Y) (at level 70).
  Notation A := AN.
  Notation A0 := A0N.
  Notation A1 := A1N.
  Notation Aplus := AplusN.
  Notation Amult := AmultN.
  Notation "x + y" := (Aplus x y).

  Add Setoid AN eqAN sid_theoryAN as A_Setoid'.
  Add Ring Aring : A_semi_ringN.

  Notation vec := (vector AN).

  Definition zero_vec := Vconst A0.
  Definition id_vec n i (ip : i < n) := Vreplace (zero_vec n) ip A1.
  Definition eq_vec := @eq_vec AN eqA.
  Notation "v1 =v v2" := (eq_vec v1 v2) (at level 70).

  Add Parametric Relation n : (vec n) (@eq_vec n)
    reflexivity proved by (@eq_vec_refl A eqA sid_theoryA n)
    symmetry proved by (@eq_vec_sym A eqA sid_theoryA n)
      transitivity proved by (@eq_vec_trans A eqA sid_theoryA n)
        as eq_vec_rel.

  (** Addition *)

  Definition vector_plus n (v1 v2 : vec n): vector A n := Vmap2 Aplus v1 v2.

  Infix "[+]" := vector_plus (at level 50).

  Add Parametric Morphism n : (@vector_plus n)
    with signature (@eq_vec n) ==> (@eq_vec n) ==> (@eq_vec n)
      as vector_plus_mor.

  Proof.
    intros. apply Vforall2n_intro. intros. unfold vector_plus.
    repeat rewrite Vnth_map2.
    (*FIXME: rewrite H does not work even if Vnth is declared as morphism *)
    apply Aplus_morN; apply (Vnth_mor eqA); hyp.
  Qed.

  Require Import ArithRing Ring_theory.

  Lemma vector_plus_nth : forall n (vl vr : vec n) i (ip : i < n),
    Vnth (vl [+] vr) ip =A= Vnth vl ip + Vnth vr ip.

  Proof.
    intros. unfold vector_plus. rewrite Vnth_map2. 
    refl.
  Qed.   

  Lemma vector_plus_comm : forall n (v1 v2 : vec n), v1 [+] v2 =v v2 [+] v1.

  Proof.
    intros. apply Vforall2n_intro. intros.
    do 2 rewrite vector_plus_nth. apply plus_comm.
  Qed.

  Lemma vector_plus_assoc : forall n (v1 v2 v3 : vec n),
    v1 [+] (v2 [+] v3) =v v1 [+] v2 [+] v3.

  Proof.
    intros. apply Vforall2n_intro. intros.
    do 4 rewrite vector_plus_nth. apply plus_assoc.
  Qed.

  Lemma vector_plus_zero_r : forall n (v : vec n), v [+] zero_vec n =v v.

  Proof.
    intros. apply Vforall2n_intro. intros. 
    rewrite vector_plus_nth.
    set (w := Vnth_const A0 ip). fold zero_vec in w.
    rewrite w at 1. apply plus_0_r.
  Qed.

  Lemma vector_plus_zero_l : forall n (v : vec n), zero_vec n [+] v =v v.

  Proof.
    intros. rewrite vector_plus_comm. apply vector_plus_zero_r.
  Qed.

  (** Sum of a vector of vectors. *)

  Definition add_vectors n k (v : vector (vec n) k) := 
    Vfold_left (@vector_plus n) (zero_vec n) v.

  Add Parametric Morphism n k : (@add_vectors n k)
    with signature (@VecEq.eq_vec _ (@eq_vec n) k) ==> (@eq_vec n)
      as add_vectors_mor.

  Proof.
    induction x; simpl; intros. VOtac. refl. revert H. VSntac y.
    unfold add_vectors. simpl. rewrite (eq_vec_cons (@eq_vec n)). intuition.
    rewrite H1. apply vector_plus_mor. 2: refl.
    eapply Vfold_left_mor with (b := zero_vec n) (b' := zero_vec n)
      (v := x) (v' := Vtail y). apply vector_plus_mor. refl. hyp.
  Qed.

  Lemma add_vectors_cons : forall n i (a : vec n) (v : vector (vec n) i),
    add_vectors (Vcons a v) =v a [+] add_vectors v.

  Proof.
    intros. unfold add_vectors. simpl. rewrite vector_plus_comm. refl.
  Qed.

  Lemma add_vectors_zero : forall n k (v : vector (vec n) k), 
    Vforall (fun v => v =v zero_vec n) v -> add_vectors v =v zero_vec n.

  Proof.
    induction v. refl. rewrite add_vectors_cons. simpl. intuition.
    rewrite H0. rewrite vector_plus_zero_l. hyp.
  Qed.

  Lemma add_vectors_perm : forall n i v v' (vs : vector (vec n) i),
    add_vectors (Vcons v (Vcons v' vs)) =v add_vectors (Vcons v' (Vcons v vs)).

  Proof.
    intros. repeat rewrite add_vectors_cons. repeat rewrite vector_plus_assoc.
    rewrite (vector_plus_comm v v'). refl.
  Qed.

  Lemma add_vectors_nth : forall n k (vs : vector (vec n) k) i (ip : i < n),
    Vnth (add_vectors vs) ip
    =A= Vfold_left Aplus A0 (Vmap (fun v => Vnth v ip) vs).

  Proof.
    induction vs; simpl; intros.
    unfold add_vectors, zero_vec; simpl. rewrite Vnth_const. 
    refl. rewrite Vnth_mor. 2: rewrite add_vectors_cons; refl.
    rewrite vector_plus_nth. rewrite IHvs. rewrite plus_comm. refl.
  Qed.

  Lemma add_vectors_split : forall n k (v vl vr : vector (vec n) k),
    (forall i (ip : i < k), Vnth v ip =v Vnth vl ip [+] Vnth vr ip) ->
    add_vectors v =v add_vectors vl [+] add_vectors vr.

  Proof.
    induction k; intros.
    VOtac. unfold add_vectors. simpl. rewrite vector_plus_zero_r. refl.
    VSntac v. VSntac vl. VSntac vr. do 3 rewrite add_vectors_cons.
    rewrite (IHk (Vtail v) (Vtail vl) (Vtail vr)). do 3 rewrite Vhead_nth.
    rewrite (H 0 (Lt.lt_O_Sn k)).
    match goal with
      |- (?A [+] ?B) [+] (?C [+] ?D) =v (?A [+] ?C) [+] (?B [+] ?D) =>
        set (X := A); set (Y := B); set (W := C); set (V := D) end.
    do 2 rewrite <- vector_plus_assoc. rewrite (vector_plus_assoc W Y V).
    rewrite (vector_plus_comm W Y). do 4 rewrite vector_plus_assoc. refl.
    intros. do 3 rewrite Vnth_tail. apply H.
  Qed.

  (** Point-wise product. *)

  Definition dot_product n (l r : vec n) :=
    Vfold_left Aplus A0 (Vmap2 Amult l r).

  Add Parametric Morphism n : (@dot_product n)
    with signature (@eq_vec n) ==> (@eq_vec n) ==> eqAN
      as dot_product_mor.

  Proof.
    induction n; intros. VOtac. 
    refl. revert H H0.
    VSntac x. VSntac y. VSntac x0. VSntac y0. intros.
    rewrite (eq_vec_cons eqA) in H3. rewrite (eq_vec_cons eqA) in H4. intuition.
    unfold dot_product. simpl. unfold dot_product in IHn.
    rewrite (IHn _ _ H6 _ _ H7). rewrite H5. rewrite H3. refl.
  Qed.

  Lemma dot_product_zero : forall n (v v' : vec n),
    Vforall (fun el => el =A= A0) v -> dot_product v v' =A= A0.

  Proof.
    induction n; intros.
    VOtac.
    refl.
    VSntac v. VSntac v'. unfold dot_product. simpl.
    fold (dot_product (Vtail v) (Vtail v')). rewrite IHn.
    assert (Vhead v =A= A0). rewrite Vhead_nth. apply Vforall_nth. hyp.
    rewrite H2. apply plus_0_l.
    apply Vforall_incl with (S n) v. intros.
    apply Vin_tail. hyp. hyp.
  Qed.

  Lemma dot_product_id : forall i n (ip : i < n) v,
    dot_product (id_vec ip) v =A= Vnth v ip.

  Proof.
    induction i. intros. 
    destruct n. NatUtil.absurd_arith.
    (* induction base *)
    VSntac v. unfold id_vec, dot_product. simpl.
    fold (dot_product (Vconst A0 n) (Vtail v)).
    rewrite dot_product_zero. apply plus_0_r.
    apply Vforall_nth_intro. intros.
    rewrite Vnth_const. refl.
    (* induction step *)
    intros. destruct n. NatUtil.absurd_arith.
    VSntac v. unfold dot_product. simpl.
    rewrite <- (IHi n (Lt.lt_S_n ip) (Vtail v)).
    ring_simplify. unfold dot_product. apply plus_0_r.
  Qed.

  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).

  Lemma dot_product_comm : forall n (u v : vec n),
    dot_product u v =A= dot_product v u.

  Proof.
    induction n.
    refl. intros. VSntac u. VSntac v. unfold dot_product. simpl.
    unfold dot_product in IHn. rewrite IHn at 1. rewrite mult_comm at 1.
    refl.
  Qed.

  Lemma dot_product_distr_r : forall n (v vl vr : vec n),
    dot_product v (vl [+] vr) =A= dot_product v vl + dot_product v vr.

  Proof.
    induction n; intros.
    VOtac. unfold dot_product. simpl. refl.
    VSntac v. VSntac vl. VSntac vr. unfold dot_product. simpl.
    fold (Vtail vl [+] Vtail vr).
    fold (dot_product (Vtail v) (Vtail vl [+] Vtail vr)).
    rewrite IHn. unfold dot_product. unfold Aplus. 
    unfold A0. unfold Amult. ring_simplify.
    refl.
  Qed.

  Lemma dot_product_distr_l : forall n (v vl vr : vec n),
    dot_product (vl [+] vr) v =A= dot_product vl v + dot_product vr v.

  Proof.
    intros. 
    rewrite dot_product_comm. rewrite dot_product_distr_r. 
    rewrite (dot_product_comm v vl). rewrite (dot_product_comm v vr). refl.
  Qed.

  Lemma dot_product_cons : forall n al ar (vl vr : vec n),
    dot_product (Vcons al vl) (Vcons ar vr) =A= al * ar + dot_product vl vr.

  Proof.
    intros. unfold dot_product. simpl.
    apply plus_comm.
  Qed.

  Lemma dot_product_distr_mult : forall n a (v v' : vec n),
    a * dot_product v v'
    =A= dot_product (Vbuild (fun i ip => a * Vnth v ip)) v'.

  Proof.
    induction n; intros.
    VOtac. unfold dot_product. simpl. apply mult_0_r.
    rewrite (VSn_eq (Vbuild (fun i (ip : i < S n) => a * Vnth v ip))).
    VSntac v. VSntac v'. do 2 rewrite dot_product_cons. unfold Aplus.
    rewrite mult_plus_distr_l. ring_simplify.
    rewrite IHn. 
    rewrite Vbuild_tail. rewrite Vbuild_head. unfold Amult. simpl; (try ring_simplify).
    (*match goal with
      |- _ + dot_product ?X _ =A= _ + dot_product ?Y _ => replace X with Y end.
    refl. apply Veq_nth. intros. 
    do 2 rewrite Vbuild_nth. rewrite NatUtil.lt_Sn_nS. refl.
  Qed.*)
  Admitted.

  (** Hints and tactics. *)

  Hint Rewrite vector_plus_zero_l vector_plus_zero_r add_vectors_cons : arith.

  Ltac Vplus_eq := simpl; (try ring_simplify);
    match goal with
      | |- ?vl [+] ?vr = ?vl' [+] ?vr' => 
        replace vl with vl'; [replace vr with vr'; try refl | try refl]
    end.

End VectorArith_nat.

(***********************************************************************)
(** ** Functor OrdVectorArith over domain natural numbers. *)

Section OrdVectorArith_nat.

  Notation A := AN.
  Notation eqA := eqAN.
  Notation sid_theoryA := sid_theoryAN.
  Notation vec := (vector A).
  Notation ge := geN.
  Notation ge_refl := ge_reflN.
  Notation ge_trans := ge_transN.
  Notation "x >>= y" := (ge x y) (at level 70).

  Add Setoid AN eqAN sid_theoryA as A_SetoidN.

  Add Relation AN ge 
  reflexivity proved by ge_refl
  transitivity proved by ge_trans
    as ge_rel.

  Notation "x =A= y" := (eqA x y) (at level 70).
  Parameter eq_ge_compatN : forall x y, x =A= y -> x >>= y.

  Definition vec_ge {n} := Vreln (n:=n) ge.
  Infix ">=v" := vec_ge (at level 70).
  Definition vec_ge_refl := Vreln_refl ge_refl.
  Definition vec_ge_trans := Vreln_trans ge_trans.
  Definition vec_ge_dec := Vreln_dec ge_dec.

  Add Parametric Morphism n : (@vec_ge n)
    with signature (@eq_vec n) ==> (@eq_vec n) ==> iff
      as vec_ge_mor.

  Proof.
    unfold vec_ge. intros. apply (Vforall2n_mor sid_theoryAN). intuition.
    trans a1. apply eq_ge_compatN. sym. hyp.
    trans a2. hyp. apply eq_ge_compatN. hyp.
    trans a1'. apply eq_ge_compatN. hyp.
    trans a2'. hyp. apply eq_ge_compatN. sym. hyp.
    hyp. hyp.
  Qed.

  Implicit Arguments vec_ge_mor [n x y x0 y0].
  Infix "[+]" := (vector_plus) (at level 50).

  Lemma vec_plus_ge_compat : forall n (vl vl' vr vr' : vec n), 
    vl >=v vl' -> vr >=v vr' -> vl [+] vr >=v vl' [+] vr'.

  Proof.
    unfold vector_plus, vec_ge. intros. apply Vforall2n_intro.
    intros. simpl. do 2 rewrite Vnth_map2.
    apply plus_ge_compatN.
    apply Vforall2n_nth. hyp.
    apply Vforall2n_nth. hyp.
  Qed.

  Lemma vec_plus_ge_compat_r : forall n (vl vl' vr : vec n), 
    vl >=v vl' -> vl [+] vr >=v vl' [+] vr.

  Proof.
    intros. apply vec_plus_ge_compat. hyp. exact (vec_ge_refl vr).
  Qed.

  Lemma vec_plus_ge_compat_l : forall n (vl vr vr' : vec n), 
    vr >=v vr' -> vl [+] vr >=v vl [+] vr'.

  Proof.
    intros. apply vec_plus_ge_compat. exact (vec_ge_refl vl). hyp.
  Qed.

End OrdVectorArith_nat.

(***********************************************************************)
(** ** Vector with type [ArcticDom] *)

Section VectorArith_arcnat.

  Notation eqA := eqAr.
  Notation sid_theoryA := sid_theoryAr.
  Notation A_semi_ring := A_semi_ringr.
  Notation "X =A= Y" := (eqA X Y) (at level 70).
  Notation A := Ar.
  Notation A0 := A0r.
  Notation A1 := A1r.
  Notation Aplus := Aplusr.
  Notation Amult := Amultr.
  Notation "x + y" := (Aplus x y).

  Add Setoid A eqA sid_theoryA as A_Setoid_arcnat.
  Add Ring Aring_arith : A_semi_ringr.
  Notation vec := (vector Ar).

  Definition zero_vec_arcnat := Vconst A0r.
  Definition id_vec_arcnat n i (ip : i < n) := Vreplace (zero_vec_arcnat n) ip A1r.
  Definition eq_vec_arcnat := @VecEq.eq_vec Ar eqAr.
  Notation "v1 =v v2" := (eq_vec_arcnat v1 v2) (at level 70).

  Add Parametric Relation n : (vec n) (@eq_vec_arcnat n)
    reflexivity proved by (@eq_vec_refl A eqA sid_theoryA n)
    symmetry proved by (@eq_vec_sym A eqA sid_theoryA n)
      transitivity proved by (@eq_vec_trans A eqA sid_theoryA n)
        as eq_vec_rel_arcnat.

  (** Addition *)

  Definition vector_plus_arcnat n (v1 v2 : vec n): vector Ar n := Vmap2 Aplus v1 v2.

  Infix "[+]" := vector_plus_arcnat (at level 50).

  Add Parametric Morphism n : (@vector_plus_arcnat n)
    with signature (@eq_vec_arcnat n) ==> (@eq_vec_arcnat n) ==> (@eq_vec_arcnat n)
      as vector_plus_mor_arcnat.

  Proof.
    intros. apply Vforall2n_intro. intros. unfold vector_plus_arcnat.
    repeat rewrite Vnth_map2.
    (*FIXME: rewrite H does not work even if Vnth is declared as morphism *)
    apply Aplus_morr; apply (Vnth_mor eqA); hyp.
  Qed.

  Lemma vector_plus_nth_arcnat : forall n (vl vr : vec n) i (ip : i < n),
    Vnth (vl [+] vr) ip =A= Vnth vl ip + Vnth vr ip.

  Proof.
    intros. unfold vector_plus_arcnat. rewrite Vnth_map2.
    refl.
  Qed.   

  Lemma vector_plus_comm_arcnat : forall n (v1 v2 : vec n), v1 [+] v2 =v v2 [+] v1.

  Proof.
    intros. apply Vforall2n_intro. intros.
    do 2 rewrite vector_plus_nth_arcnat. apply A_plus_comm.
  Qed.

  Lemma vector_plus_assoc_arcnat : forall n (v1 v2 v3 : vec n),
    v1 [+] (v2 [+] v3) =v v1 [+] v2 [+] v3.

  Proof.
    intros. apply Vforall2n_intro. intros.
    do 4 rewrite vector_plus_nth_arcnat. ring.
  Qed.

  Lemma vector_plus_zero_r_arcnat : forall n (v : vec n), v [+] zero_vec_arcnat n =v v.

  Proof.
    intros. apply Vforall2n_intro. intros. 
    rewrite vector_plus_nth_arcnat.
    set (w := Vnth_const A0 ip). fold zero_vec in w.
    rewrite w at 1. ring.
  Qed.

  Lemma vector_plus_zero_l_arcnat : forall n (v : vec n), zero_vec_arcnat n [+] v =v v.

  Proof.
    intros. rewrite vector_plus_comm_arcnat. apply vector_plus_zero_r_arcnat.
  Qed.

  (** Sum of a vector of vectors. *)

  Definition add_vectors_arcnat n k (v : vector (vec n) k) := 
    Vfold_left (@vector_plus_arcnat n) (zero_vec_arcnat n) v.

  Add Parametric Morphism n k : (@add_vectors_arcnat n k)
    with signature (@VecEq.eq_vec _ (@eq_vec_arcnat n) k) ==> (@eq_vec_arcnat n)
      as add_vectors_mor_arcnat.

  Proof.
    induction x; simpl; intros. VOtac. refl. revert H. VSntac y.
    unfold add_vectors_arcnat. simpl. rewrite (eq_vec_cons (@eq_vec_arcnat n)). intuition.
    rewrite H1. apply vector_plus_mor_arcnat. 2: refl.
    eapply Vfold_left_mor with (b := zero_vec_arcnat n) (b' := zero_vec_arcnat n)
      (v := x) (v' := Vtail y). apply vector_plus_mor_arcnat. refl. hyp.
  Qed.

  Lemma add_vectors_cons_arcnat : forall n i (a : vec n) (v : vector (vec n) i),
    add_vectors_arcnat (Vcons a v) =v a [+] add_vectors_arcnat v.

  Proof.
    intros. unfold add_vectors_arcnat. simpl. rewrite vector_plus_comm_arcnat. refl.
  Qed.

  Lemma add_vectors_zero_arcnat : forall n k (v : vector (vec n) k), 
    Vforall (fun v => v =v zero_vec_arcnat n) v -> add_vectors_arcnat v =v zero_vec_arcnat n.

  Proof.
    induction v. refl. rewrite add_vectors_cons_arcnat. simpl. intuition.
    rewrite H0. rewrite vector_plus_zero_l_arcnat. hyp.
  Qed.

  Lemma add_vectors_perm_arcnat : forall n i v v' (vs : vector (vec n) i),
    add_vectors_arcnat (Vcons v (Vcons v' vs)) =v add_vectors_arcnat (Vcons v' (Vcons v vs)).

  Proof.
    intros. repeat rewrite add_vectors_cons_arcnat. repeat rewrite vector_plus_assoc_arcnat.
    rewrite (vector_plus_comm_arcnat v v'). refl.
  Qed.

  Lemma add_vectors_nth_arcnat : forall n k (vs : vector (vec n) k) i (ip : i < n),
    Vnth (add_vectors_arcnat vs) ip
    =A= Vfold_left Aplus A0 (Vmap (fun v => Vnth v ip) vs).

  Proof.
    induction vs; simpl; intros.
    unfold add_vectors_arcnat, zero_vec_arcnat; simpl. rewrite Vnth_const. 
    refl. rewrite Vnth_mor. 2: rewrite add_vectors_cons_arcnat; refl.
    rewrite vector_plus_nth_arcnat. rewrite IHvs. rewrite A_plus_comm. refl.
  Qed.

  Lemma add_vectors_split_arcnat : forall n k (v vl vr : vector (vec n) k),
    (forall i (ip : i < k), Vnth v ip =v Vnth vl ip [+] Vnth vr ip) ->
    add_vectors_arcnat v =v add_vectors_arcnat vl [+] add_vectors_arcnat vr.

  Proof.
    induction k; intros.
    VOtac. unfold add_vectors_arcnat. simpl. rewrite vector_plus_zero_r_arcnat. refl.
    VSntac v. VSntac vl. VSntac vr. do 3 rewrite add_vectors_cons_arcnat.
    rewrite (IHk (Vtail v) (Vtail vl) (Vtail vr)). do 3 rewrite Vhead_nth.
    rewrite (H 0 (Lt.lt_O_Sn k)).
    match goal with
      |- (?A [+] ?B) [+] (?C [+] ?D) =v (?A [+] ?C) [+] (?B [+] ?D) =>
        set (X := A); set (Y := B); set (W := C); set (V := D) end.
    do 2 rewrite <- vector_plus_assoc_arcnat. rewrite (vector_plus_assoc_arcnat W Y V).
    rewrite (vector_plus_comm_arcnat W Y). do 4 rewrite vector_plus_assoc_arcnat. refl.
    intros. do 3 rewrite Vnth_tail. apply H.
  Qed.

  (** Point-wise product. *)

  Definition dot_product_arcnat n (l r : vec n) :=
    Vfold_left Aplus A0 (Vmap2 Amult l r).

  Add Parametric Morphism n : (@dot_product_arcnat n)
    with signature (@eq_vec_arcnat n) ==> (@eq_vec_arcnat n) ==> eqA
      as dot_product_mor_arcnat.

  Proof.
    induction n; intros. VOtac. 
    refl. revert H H0.
    VSntac x. VSntac y. VSntac x0. VSntac y0. intros.
    rewrite (eq_vec_cons eqA) in H3. rewrite (eq_vec_cons eqA) in H4. intuition.
    unfold dot_product_arcnat. simpl. unfold dot_product_arcnat in IHn.
    rewrite (IHn _ _ H6 _ _ H7). rewrite H5. rewrite H3. refl.
  Qed.

  Lemma dot_product_zero_arcnat : forall n (v v' : vec n),
    Vforall (fun el => el =A= A0) v -> dot_product_arcnat v v' =A= A0.

  Proof.
    induction n; intros.
    VOtac.
    refl.
    VSntac v. VSntac v'. unfold dot_product_arcnat. simpl.
    fold (dot_product_arcnat (Vtail v) (Vtail v')). rewrite IHn.
    assert (Vhead v =A= A0). rewrite Vhead_nth. apply Vforall_nth. hyp.
    rewrite H2. ring. 
    apply Vforall_incl with (S n) v. intros.
    apply Vin_tail. hyp. hyp.
  Qed.

  Lemma A_plus_0_r : forall n, (n + A0) =A= n.
  Proof.
    intros n. ring.
  Qed.

  Lemma dot_product_id_arcnat : forall i n (ip : i < n) v,
    dot_product_arcnat (id_vec_arcnat ip) v =A= Vnth v ip.

  Proof.
    induction i. intros. 
    destruct n. absurd_arith.
    (* induction base *)
    VSntac v. unfold id_vec, dot_product_arcnat. destruct (Vhead v);
    try discr; simpl in *.
    fold (dot_product_arcnat (Vconst A0 n) (Vtail v)).
    rewrite dot_product_zero_arcnat. ring.
    apply Vforall_nth_intro. intros.
    rewrite Vnth_const. refl.
    fold (dot_product_arcnat (Vconst A0 n) (Vtail v)).
    rewrite dot_product_zero_arcnat. ring. 
    apply Vforall_nth_intro. intros.
    rewrite Vnth_const. refl.
    (* induction step *)
    intros. destruct n. NatUtil.absurd_arith.
    VSntac v. unfold dot_product_arcnat. simpl.
    rewrite <- (IHi n (Lt.lt_S_n ip) (Vtail v)).
    ring_simplify. unfold dot_product_arcnat. ring_simplify. apply A_plus_0_r.
  Qed.

  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).

  Lemma dot_product_comm_arcnat : forall n (u v : vec n),
    dot_product_arcnat u v =A= dot_product_arcnat v u.

  Proof.
    induction n.
    refl. intros. VSntac u. VSntac v. unfold dot_product_arcnat. simpl.
    unfold dot_product_arcnat in IHn. rewrite IHn at 1. ring.
  Qed.

  Lemma dot_product_distr_r_arcnat : forall n (v vl vr : vec n),
    dot_product_arcnat v (vl [+] vr) =A= dot_product_arcnat v vl + dot_product_arcnat v vr.

  Proof.
    induction n; intros.
    VOtac. unfold dot_product_arcnat. simpl. refl.
    VSntac v. VSntac vl. VSntac vr. unfold dot_product_arcnat. simpl.
    fold (Vtail vl [+] Vtail vr).
    fold (dot_product_arcnat (Vtail v) (Vtail vl [+] Vtail vr)).
    rewrite IHn. unfold dot_product_arcnat. ring_simplify. ring.
  Qed.

  Lemma dot_product_distr_l_arcnat : forall n (v vl vr : vec n),
    dot_product_arcnat (vl [+] vr) v =A= dot_product_arcnat vl v + dot_product_arcnat vr v.

  Proof.
    intros. 
    rewrite dot_product_comm_arcnat. rewrite dot_product_distr_r_arcnat. 
    rewrite (dot_product_comm_arcnat v vl). rewrite (dot_product_comm_arcnat v vr). refl.
  Qed.

  Lemma dot_product_cons_arcnat : forall n al ar (vl vr : vec n),
    dot_product_arcnat (Vcons al vl) (Vcons ar vr) =A= al * ar + dot_product_arcnat vl vr.

  Proof.
    intros. unfold dot_product_arcnat. simpl.
    apply A_plus_comm.
  Qed.

  Lemma A_mult_plus_distr_l_r : forall m n p, n * (m + p) = (n * m) + (n * p).
  Proof.
    intros. ring_simplify. refl.
  Qed.
    
  Lemma dot_product_distr_mult_arcnat : forall n a (v v' : vec n),
    a * dot_product_arcnat v v'
    =A= dot_product_arcnat (Vbuild (fun i ip => a * Vnth v ip)) v'.

  Proof.
    induction n; intros.
    VOtac. unfold dot_product_arcnat. simpl. ring.
    rewrite (VSn_eq (Vbuild (fun i (ip : i < S n) => a * Vnth v ip))).
    VSntac v. VSntac v'. do 2 rewrite dot_product_cons_arcnat. ring_simplify.
    rewrite IHn. 
    rewrite Vbuild_tail. rewrite Vbuild_head. simpl. ring_simplify.
    match goal with
      |- _ + dot_product_arcnat ?X _ =A= _ + dot_product_arcnat ?Y _ => replace X with Y end.
    refl. apply Veq_nth. intros. 
    do 2 rewrite Vbuild_nth. rewrite NatUtil.lt_Sn_nS. refl.
  Qed.

  (** Hints and tactics. *)

  Hint Rewrite vector_plus_zero_l vector_plus_zero_r add_vectors_cons : arith.

  Ltac Vplus_eq := simpl; (try ring_simplify);
    match goal with
      | |- ?vl [+] ?vr = ?vl' [+] ?vr' => 
        replace vl with vl'; [replace vr with vr'; try refl | try refl]
    end.

End VectorArith_arcnat.

(***********************************************************************)
(** ** Functor ordering vector of type [ArcticDom] *)

Section OrdVectorArith_arcnat.

  Notation A := Ar.
  Notation eqA := eqAr.
  Notation sid_theoryA := sid_theoryAr.
  Notation vec := (vector A).
  Notation ge := ger.
  Notation ge_refl := ge_reflr.
  Notation ge_trans := ge_transr.
  Notation "x >>= y" := (ge x y) (at level 70).
  Add Setoid A eqA sid_theoryA as A_Setoidr.

  Add Relation Ar ge 
  reflexivity proved by ge_refl
  transitivity proved by ge_trans
    as ge_rel_arcint.

  Notation "x =A= y" := (eqA x y) (at level 70).
  Parameter eq_ge_compatr : forall x y, x =A= y -> x >>= y.

  Definition vec_ge_arcnat {n} := Vreln (n:=n) ger.
  Infix ">=v" := vec_ge_arcnat (at level 70).
  Definition vec_ge_refl_arcnat := Vreln_refl ge_refl.
  Definition vec_ge_trans_arcnat := Vreln_trans ge_trans.
  Definition vec_ge_dec_arcnat := Vreln_dec ge_decr.

  Add Parametric Morphism n : (@vec_ge_arcnat n)
    with signature (@eq_vec_arcnat n) ==> (@eq_vec_arcnat n) ==> iff
      as vec_ge_mor_arcnat.

  Proof.
    unfold vec_ge_arcnat. intros. apply (Vforall2n_mor sid_theoryAr). intuition.
    trans a1. apply eq_ge_compatr. sym. hyp.
    trans a2. hyp. apply eq_ge_compatr. hyp.
    trans a1'. apply eq_ge_compatr. hyp.
    trans a2'. hyp. apply eq_ge_compatr. sym. hyp.
    hyp. hyp.
  Qed.

  Implicit Arguments vec_ge_mor_arcnat [n x y x0 y0].
  Infix "[+]" := (vector_plus_arcnat) (at level 50).

  Lemma vec_plus_ge_compat_arcnat : forall n (vl vl' vr vr' : vec n), 
    vl >=v vl' -> vr >=v vr' -> vl [+] vr >=v vl' [+] vr'.

  Proof.
    unfold vector_plus_arcnat, vec_ge_arcnat. intros. apply Vforall2n_intro.
    intros. simpl. do 2 rewrite Vnth_map2.
    apply plus_ge_compatr.
    apply Vforall2n_nth. hyp.
    apply Vforall2n_nth. hyp.
  Qed.

  Lemma vec_plus_ge_compat_r_arcnat : forall n (vl vl' vr : vec n), 
    vl >=v vl' -> vl [+] vr >=v vl' [+] vr.

  Proof.
    intros. apply vec_plus_ge_compat_arcnat. hyp. exact (vec_ge_refl_arcnat vr).
  Qed.

  Lemma vec_plus_ge_compat_l_arcnat : forall n (vl vr vr' : vec n), 
    vr >=v vr' -> vl [+] vr >=v vl [+] vr'.

  Proof.
    intros. apply vec_plus_ge_compat_arcnat. exact (vec_ge_refl_arcnat vl). hyp.
  Qed.

End OrdVectorArith_arcnat.

(***********************************************************************)
(** ** Vector over domain arctic integer numbers with type [ArcticBZDom] *)

Section VectorArith_arcbz.

  Notation eqA := eqArbz.
  Notation sid_theoryA := sid_theoryArbz.
  Notation A_semi_ring := A_semi_ringrbz.
  Notation "X =A= Y" := (eqA X Y) (at level 70).
  Notation A := Arbz.
  Notation A0 := A0rbz.
  Notation A1 := A1rbz.
  Notation Aplus := Aplusrbz.
  Notation Amult := Amultrbz.
  Notation "x + y" := (Aplus x y).
  Add Setoid A eqA sid_theoryA as A_Setoid_arcbz.
  Add Ring Aring_arith_rbz : A_semi_ring.
  Notation vec := (vector Arbz).

  Definition zero_vec_arcbz := Vconst A0rbz.
  Definition id_vec_arcbz n i (ip : i < n) := Vreplace (zero_vec_arcbz n) ip A1rbz.
  Definition eq_vec_arcbz := @VecEq.eq_vec Arbz eqArbz.
  Notation "v1 =v v2" := (eq_vec_arcbz v1 v2) (at level 70).

  Add Parametric Relation n : (vec n) (@eq_vec_arcbz n)
    reflexivity proved by (@eq_vec_refl A eqA sid_theoryA n)
    symmetry proved by (@eq_vec_sym A eqA sid_theoryA n)
      transitivity proved by (@eq_vec_trans A eqA sid_theoryA n)
        as eq_vec_rel_arcbz.

  (** Addition *)

  Definition vector_plus_arcbz n (v1 v2 : vec n): vector Arbz n := Vmap2 Aplus v1 v2.

  Infix "[+]" := vector_plus_arcbz (at level 50).

  Add Parametric Morphism n : (@vector_plus_arcbz n)
    with signature (@eq_vec_arcbz n) ==> (@eq_vec_arcbz n) ==> (@eq_vec_arcbz n)
      as vector_plus_mor_arcbz.

  Proof.
    intros. apply Vforall2n_intro. intros. unfold vector_plus_arcbz.
    repeat rewrite Vnth_map2.
    (*FIXME: rewrite H does not work even if Vnth is declared as morphism *)
    apply Aplus_morrbz; apply (Vnth_mor eqA); hyp.
  Qed.

  Lemma vector_plus_nth_arcbz : forall n (vl vr : vec n) i (ip : i < n),
    Vnth (vl [+] vr) ip =A= Vnth vl ip + Vnth vr ip.

  Proof.
    intros. unfold vector_plus_arcbz. rewrite Vnth_map2.
    refl.
  Qed.   

  Lemma vector_plus_comm_arcbz : forall n (v1 v2 : vec n), v1 [+] v2 =v v2 [+] v1.

  Proof.
    intros. apply Vforall2n_intro. intros.
    do 2 rewrite vector_plus_nth_arcbz. ring.
  Qed.

  Lemma vector_plus_assoc_arcbz : forall n (v1 v2 v3 : vec n),
    v1 [+] (v2 [+] v3) =v v1 [+] v2 [+] v3.

  Proof.
    intros. apply Vforall2n_intro. intros.
    do 4 rewrite vector_plus_nth_arcbz. ring.
  Qed.

  Lemma vector_plus_zero_r_arcbz : forall n (v : vec n), v [+] zero_vec_arcbz n =v v.

  Proof.
    intros. apply Vforall2n_intro. intros. 
    rewrite vector_plus_nth_arcbz.
    set (w := Vnth_const A0 ip). fold zero_vec in w.
    rewrite w at 1. ring.
  Qed.

  Lemma vector_plus_zero_l_arcbz : forall n (v : vec n), zero_vec_arcbz n [+] v =v v.

  Proof.
    intros. rewrite vector_plus_comm_arcbz. apply vector_plus_zero_r_arcbz.
  Qed.

  (** Sum of a vector of vectors. *)

  Definition add_vectors_arcbz n k (v : vector (vec n) k) := 
    Vfold_left (@vector_plus_arcbz n) (zero_vec_arcbz n) v.

  Add Parametric Morphism n k : (@add_vectors_arcbz n k)
    with signature (@VecEq.eq_vec _ (@eq_vec_arcbz n) k) ==> (@eq_vec_arcbz n)
      as add_vectors_mor_arcbz.

  Proof.
    induction x; simpl; intros. VOtac. refl. revert H. VSntac y.
    unfold add_vectors_arcbz. simpl. rewrite (eq_vec_cons (@eq_vec_arcbz n)). intuition.
    rewrite H1. apply vector_plus_mor_arcbz. 2: refl.
    eapply Vfold_left_mor with (b := zero_vec_arcbz n) (b' := zero_vec_arcbz n)
      (v := x) (v' := Vtail y). apply vector_plus_mor_arcbz. refl. hyp.
  Qed.

  Lemma add_vectors_cons_arcbz : forall n i (a : vec n) (v : vector (vec n) i),
    add_vectors_arcbz (Vcons a v) =v a [+] add_vectors_arcbz v.

  Proof.
    intros. unfold add_vectors_arcbz. simpl. rewrite vector_plus_comm_arcbz. refl.
  Qed.

  Lemma add_vectors_zero_arcbz : forall n k (v : vector (vec n) k), 
    Vforall (fun v => v =v zero_vec_arcbz n) v -> add_vectors_arcbz v =v zero_vec_arcbz n.

  Proof.
    induction v. refl. rewrite add_vectors_cons_arcbz. simpl. intuition.
    rewrite H0. rewrite vector_plus_zero_l_arcbz. hyp.
  Qed.

  Lemma add_vectors_perm_arcbz : forall n i v v' (vs : vector (vec n) i),
    add_vectors_arcbz (Vcons v (Vcons v' vs)) =v add_vectors_arcbz (Vcons v' (Vcons v vs)).

  Proof.
    intros. repeat rewrite add_vectors_cons_arcbz. repeat rewrite vector_plus_assoc_arcbz.
    rewrite (vector_plus_comm_arcbz v v'). refl.
  Qed.

  Lemma add_vectors_nth_arcbz : forall n k (vs : vector (vec n) k) i (ip : i < n),
    Vnth (add_vectors_arcbz vs) ip
    =A= Vfold_left Aplus A0 (Vmap (fun v => Vnth v ip) vs).

  Proof.
    induction vs; simpl; intros.
    unfold add_vectors_arcbz, zero_vec_arcbz; simpl. rewrite Vnth_const. 
    refl. rewrite Vnth_mor. 2: rewrite add_vectors_cons_arcbz; refl.
    rewrite vector_plus_nth_arcbz. rewrite IHvs. rewrite A_plus_commrbz. refl.
  Qed.

  Lemma add_vectors_split_arcbz : forall n k (v vl vr : vector (vec n) k),
    (forall i (ip : i < k), Vnth v ip =v Vnth vl ip [+] Vnth vr ip) ->
    add_vectors_arcbz v =v add_vectors_arcbz vl [+] add_vectors_arcbz vr.

  Proof.
    induction k; intros.
    VOtac. unfold add_vectors_arcbz. simpl. rewrite vector_plus_zero_r_arcbz. refl.
    VSntac v. VSntac vl. VSntac vr. do 3 rewrite add_vectors_cons_arcbz.
    rewrite (IHk (Vtail v) (Vtail vl) (Vtail vr)). do 3 rewrite Vhead_nth.
    rewrite (H 0 (Lt.lt_O_Sn k)).
    match goal with
      |- (?A [+] ?B) [+] (?C [+] ?D) =v (?A [+] ?C) [+] (?B [+] ?D) =>
        set (X := A); set (Y := B); set (W := C); set (V := D) end.
    do 2 rewrite <- vector_plus_assoc_arcbz. rewrite (vector_plus_assoc_arcbz W Y V).
    rewrite (vector_plus_comm_arcbz W Y). do 4 rewrite vector_plus_assoc_arcbz. refl.
    intros. do 3 rewrite Vnth_tail. apply H.
  Qed.

  (** Point-wise product. *)

  Definition dot_product_arcbz n (l r : vec n) :=
    Vfold_left Aplus A0 (Vmap2 Amult l r).

  Add Parametric Morphism n : (@dot_product_arcbz n)
    with signature (@eq_vec_arcbz n) ==> (@eq_vec_arcbz n) ==> eqA
      as dot_product_mor_arcbz.

  Proof.
    induction n; intros. VOtac. 
    refl. revert H H0.
    VSntac x. VSntac y. VSntac x0. VSntac y0. intros.
    rewrite (eq_vec_cons eqA) in H3. rewrite (eq_vec_cons eqA) in H4. intuition.
    unfold dot_product_arcbz. simpl. unfold dot_product_arcbz in IHn.
    rewrite (IHn _ _ H6 _ _ H7). rewrite H5. rewrite H3. refl.
  Qed.

  Lemma dot_product_zero_arcbz : forall n (v v' : vec n),
    Vforall (fun el => el =A= A0) v -> dot_product_arcbz v v' =A= A0.

  Proof.
    induction n; intros.
    VOtac.
    refl.
    VSntac v. VSntac v'. unfold dot_product_arcbz. simpl.
    fold (dot_product_arcbz (Vtail v) (Vtail v')). rewrite IHn.
    assert (Vhead v =A= A0). rewrite Vhead_nth. apply Vforall_nth. hyp.
    rewrite H2. ring.
    apply Vforall_incl with (S n) v. intros.
    apply Vin_tail. hyp. hyp.
  Qed.

  Lemma A_plus_0_lbz : forall n:ArcticBZDom, (A0 + n) =A= n.
  Proof.
    intros. ring.
  Qed.

  Lemma A_plus_0_rbz : forall n, (n + A0) =A= n.
  Proof.
    intros. ring.
  Qed.

  Lemma dot_product_id_arcbz : forall i n (ip : i < n) v,
    dot_product_arcbz (id_vec_arcbz ip) v =A= Vnth v ip.

  Proof.
    induction i. intros. 
    destruct n. absurd_arith.
    (* induction base *)
    VSntac v. unfold id_vec, dot_product_arcbz.
    destruct (Vhead v); try discr; simpl in *.
    fold (dot_product_arcbz (Vconst A0 n) (Vtail v)).
    rewrite dot_product_zero_arcbz. ring.
    apply Vforall_nth_intro. intros.
    rewrite Vnth_const. refl.
    fold (dot_product_arcbz (Vconst A0 n) (Vtail v)).
    rewrite dot_product_zero_arcbz. ring.
    apply Vforall_nth_intro. intros.
    rewrite Vnth_const. refl.
    (* induction step *)
    intros. destruct n. NatUtil.absurd_arith.
    VSntac v. unfold dot_product_arcbz. simpl.
    rewrite <- (IHi n (Lt.lt_S_n ip) (Vtail v)).
    ring_simplify. unfold dot_product_arcbz. apply A_plus_0_rbz.
  Qed.

  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).

  Lemma dot_product_comm_arcbz : forall n (u v : vec n),
    dot_product_arcbz u v =A= dot_product_arcbz v u.

  Proof.
    induction n.
    refl. intros. VSntac u. VSntac v. unfold dot_product_arcbz. simpl.
    unfold dot_product_arcbz in IHn. rewrite IHn at 1. ring.
  Qed.

  Lemma dot_product_distr_r_arcbz : forall n (v vl vr : vec n),
    dot_product_arcbz v (vl [+] vr) =A= dot_product_arcbz v vl
    + dot_product_arcbz v vr.

  Proof.
    induction n; intros.
    VOtac. unfold dot_product_arcbz. simpl. refl.
    VSntac v. VSntac vl. VSntac vr. unfold dot_product_arcbz. simpl.
    fold (Vtail vl [+] Vtail vr).
    fold (dot_product_arcbz (Vtail v) (Vtail vl [+] Vtail vr)).
    rewrite IHn. unfold dot_product_arcbz. ring.
  Qed.

  Lemma dot_product_distr_l_arcbz : forall n (v vl vr : vec n),
    dot_product_arcbz (vl [+] vr) v =A= dot_product_arcbz vl v + dot_product_arcbz vr v.

  Proof.
    intros. 
    rewrite dot_product_comm_arcbz. rewrite dot_product_distr_r_arcbz. 
    rewrite (dot_product_comm_arcbz v vl). rewrite (dot_product_comm_arcbz v vr). refl.
  Qed.

  Lemma dot_product_cons_arcbz : forall n al ar (vl vr : vec n),
    dot_product_arcbz (Vcons al vl) (Vcons ar vr) =A= al * ar + dot_product_arcbz vl vr.

  Proof.
    intros. unfold dot_product_arcbz. simpl. ring.
  Qed.

  Lemma dot_product_distr_mult_arcbz : forall n a (v v' : vec n),
    a * dot_product_arcbz v v'
    =A= dot_product_arcbz (Vbuild (fun i ip => a * Vnth v ip)) v'.

  Proof.
    induction n; intros.
    VOtac. unfold dot_product_arcbz. simpl. ring.
    rewrite (VSn_eq (Vbuild (fun i (ip : i < S n) => a * Vnth v ip))).
    VSntac v. VSntac v'. do 2 rewrite dot_product_cons_arcbz. ring_simplify.
    rewrite IHn. 
    rewrite Vbuild_tail. rewrite Vbuild_head. simpl. ring_simplify.
    match goal with
      |- _ + dot_product_arcbz ?X _ =A= _ + dot_product_arcbz ?Y _ => replace X with Y end.
    refl. apply Veq_nth. intros. 
    do 2 rewrite Vbuild_nth. rewrite NatUtil.lt_Sn_nS. refl.
  Qed.

  (** Hints and tactics. *)

  Hint Rewrite vector_plus_zero_l vector_plus_zero_r add_vectors_cons : arith.

  Ltac Vplus_eq := simpl; (try ring_simplify);
    match goal with
      | |- ?vl [+] ?vr = ?vl' [+] ?vr' => 
        replace vl with vl'; [replace vr with vr'; try refl | try refl]
    end.

End VectorArith_arcbz.

(***********************************************************************)
(** ** Functor OrdVectorArith over domain arctic integer numbers. *)

Section OrdVectorArith_arcbz.

  Notation A := Arbz.
  Notation eqA := eqArbz.
  Notation sid_theoryA := sid_theoryArbz.
  Notation vec := (vector A).
  Notation ge := gerbz.
  Notation ge_refl := ge_reflrbz.
  Notation ge_trans := ge_transrbz.
  Notation "x >>= y" := (ge x y) (at level 70).

  Add Setoid A eqA sid_theoryA as A_Setoidrbz.

  Add Relation Arbz ge 
  reflexivity proved by ge_refl
  transitivity proved by ge_trans
    as ge_rel_arcrbz.

  Notation "x =A= y" := (eqA x y) (at level 70).
  Parameter eq_ge_compatrbz : forall x y, x =A= y -> x >>= y.

  Definition vec_ge_arcbz {n} := Vreln (n:=n) gerbz.
  Infix ">=v" := vec_ge_arcbz (at level 70).

  Definition vec_ge_refl_arcbz := Vreln_refl ge_refl.
  Definition vec_ge_trans_arcbz := Vreln_trans ge_trans.
  Definition vec_ge_dec_arcbz := Vreln_dec ge_decrbz.

  Add Parametric Morphism n : (@vec_ge_arcbz n)
    with signature (@eq_vec_arcbz n) ==> (@eq_vec_arcbz n) ==> iff
      as vec_ge_mor_arcbz.

  Proof.
    unfold vec_ge_arcbz. intros. apply (Vforall2n_mor sid_theoryArbz). intuition.
    trans a1. apply eq_ge_compatrbz. sym. hyp.
    trans a2. hyp. apply eq_ge_compatrbz. hyp.
    trans a1'. apply eq_ge_compatrbz. hyp.
    trans a2'. hyp. apply eq_ge_compatrbz. sym. hyp.
    hyp. hyp.
  Qed.

  Implicit Arguments vec_ge_mor_arcbz [n x y x0 y0].

  Infix "[+]" := (vector_plus_arcbz) (at level 50).

  Lemma vec_plus_ge_compat_arcbz : forall n (vl vl' vr vr' : vec n), 
    vl >=v vl' -> vr >=v vr' -> vl [+] vr >=v vl' [+] vr'.

  Proof.
    unfold vector_plus_arcbz, vec_ge_arcbz. intros. apply Vforall2n_intro.
    intros. simpl. do 2 rewrite Vnth_map2.
    apply plus_ge_compatrbz.
    apply Vforall2n_nth. hyp.
    apply Vforall2n_nth. hyp.
  Qed.

  Lemma vec_plus_ge_compat_r_arcbz : forall n (vl vl' vr : vec n), 
    vl >=v vl' -> vl [+] vr >=v vl' [+] vr.

  Proof.
    intros. apply vec_plus_ge_compat_arcbz. hyp. exact (vec_ge_refl_arcbz vr).
  Qed.

  Lemma vec_plus_ge_compat_l_arcbz : forall n (vl vr vr' : vec n), 
    vr >=v vr' -> vl [+] vr >=v vl [+] vr'.

  Proof.
    intros. apply vec_plus_ge_compat_arcbz. exact (vec_ge_refl_arcbz vl). hyp.
  Qed.

End OrdVectorArith_arcbz.

(***********************************************************************)
(** ** Vector arith with type Tropic over naturals with plus infinity
and plus-min operations *)

Section VectorArith_tropicdom.

  Notation eqA := eqAt.
  Notation sid_theoryA := sid_theoryAt.
  Notation A_semi_ring := A_semi_ringt.
  Notation "X =A= Y" := (eqA X Y) (at level 70).
  Notation A := At.
  Notation A0 := A0t.
  Notation A1 := A1t.
  Notation Aplus := Aplust.
  Notation Amult := Amultt.
  Notation "x + y" := (Aplus x y).

  Add Setoid A eqA sid_theoryA as A_Setoid_trop.
  Add Ring Aring_arith_t : A_semi_ring.
  Notation vec := (vector At).

  Definition zero_vec_trop := Vconst A0t.
  Definition id_vec_trop n i (ip : i < n) := Vreplace (zero_vec_trop n) ip A1t.
  Definition eq_vec_trop := @VecEq.eq_vec At eqAt.

  Notation "v1 =v v2" := (eq_vec_trop v1 v2) (at level 70).

  Add Parametric Relation n : (vec n) (@eq_vec_trop n)
    reflexivity proved by (@eq_vec_refl A eqA sid_theoryA n)
    symmetry proved by (@eq_vec_sym A eqA sid_theoryA n)
      transitivity proved by (@eq_vec_trans A eqA sid_theoryA n)
        as eq_vec_rel_trop.

  (** Addition *)

  Definition vector_plus_trop n (v1 v2 : vec n): vector At n := Vmap2 Aplus v1 v2.

  Infix "[+]" := vector_plus_trop (at level 50).

  Add Parametric Morphism n : (@vector_plus_trop n)
    with signature (@eq_vec_trop n) ==> (@eq_vec_trop n) ==> (@eq_vec_trop n)
      as vector_plus_mor_trop.

  Proof.
    intros. apply Vforall2n_intro. intros. unfold vector_plus_trop.
    repeat rewrite Vnth_map2.
    (*FIXME: rewrite H does not work even if Vnth is declared as morphism *)
    apply Aplus_mort; apply (Vnth_mor eqA); hyp.
  Qed.

  Lemma vector_plus_nth_trop : forall n (vl vr : vec n) i (ip : i < n),
    Vnth (vl [+] vr) ip =A= Vnth vl ip + Vnth vr ip.

  Proof.
    intros. unfold vector_plus_trop. rewrite Vnth_map2.
    refl.
  Qed.   

  Lemma vector_plus_comm_trop : forall n (v1 v2 : vec n), v1 [+] v2 =v v2 [+] v1.

  Proof.
    intros. apply Vforall2n_intro. intros.
    do 2 rewrite vector_plus_nth_trop. ring.
  Qed.

  Lemma vector_plus_assoc_trop : forall n (v1 v2 v3 : vec n),
    v1 [+] (v2 [+] v3) =v v1 [+] v2 [+] v3.

  Proof.
    intros. apply Vforall2n_intro. intros.
    do 4 rewrite vector_plus_nth_trop. ring.
  Qed.

  Lemma vector_plus_zero_r_trop : forall n (v : vec n), v [+] zero_vec_trop n =v v.

  Proof.
    intros. apply Vforall2n_intro. intros. 
    rewrite vector_plus_nth_trop.
    set (w := Vnth_const A0 ip). fold zero_vec in w.
    rewrite w at 1. ring.
  Qed.

  Lemma vector_plus_zero_l_trop : forall n (v : vec n), zero_vec_trop n [+] v =v v.

  Proof.
    intros. rewrite vector_plus_comm_trop. apply vector_plus_zero_r_trop.
  Qed.

  (** Sum of a vector of vectors. *)

  Definition add_vectors_trop n k (v : vector (vec n) k) := 
    Vfold_left (@vector_plus_trop n) (zero_vec_trop n) v.

  Add Parametric Morphism n k : (@add_vectors_trop n k)
    with signature (@VecEq.eq_vec _ (@eq_vec_trop n) k) ==> (@eq_vec_trop n)
      as add_vectors_mor_trop.

  Proof.
    induction x; simpl; intros. VOtac. refl. revert H. VSntac y.
    unfold add_vectors_trop. simpl. rewrite (eq_vec_cons (@eq_vec_trop n)). intuition.
    rewrite H1. apply vector_plus_mor_trop. 2: refl.
    eapply Vfold_left_mor with (b := zero_vec_trop n) (b' := zero_vec_trop n)
      (v := x) (v' := Vtail y). apply vector_plus_mor_trop. refl. hyp.
  Qed.

  Lemma add_vectors_cons_trop : forall n i (a : vec n) (v : vector (vec n) i),
    add_vectors_trop (Vcons a v) =v a [+] add_vectors_trop v.

  Proof.
    intros. unfold add_vectors_trop. simpl. rewrite vector_plus_comm_trop. refl.
  Qed.

  Lemma add_vectors_zero_trop : forall n k (v : vector (vec n) k), 
    Vforall (fun v => v =v zero_vec_trop n) v -> add_vectors_trop v =v zero_vec_trop n.

  Proof.
    induction v. refl. rewrite add_vectors_cons_trop. simpl. intuition.
    rewrite H0. rewrite vector_plus_zero_l_trop. hyp.
  Qed.

  Lemma add_vectors_perm_trop : forall n i v v' (vs : vector (vec n) i),
    add_vectors_trop (Vcons v (Vcons v' vs)) =v add_vectors_trop (Vcons v' (Vcons v vs)).

  Proof.
    intros. repeat rewrite add_vectors_cons_trop. repeat rewrite vector_plus_assoc_trop.
    rewrite (vector_plus_comm_trop v v'). refl.
  Qed.

  Lemma add_vectors_nth_trop : forall n k (vs : vector (vec n) k) i (ip : i < n),
    Vnth (add_vectors_trop vs) ip
    =A= Vfold_left Aplus A0 (Vmap (fun v => Vnth v ip) vs).

  Proof.
    induction vs; simpl; intros.
    unfold add_vectors_trop, zero_vec_trop; simpl. rewrite Vnth_const. 
    refl. rewrite Vnth_mor. 2: rewrite add_vectors_cons_trop; refl.
    rewrite vector_plus_nth_trop. rewrite IHvs. rewrite A_plus_commt. refl.
  Qed.

  Lemma add_vectors_split_trop : forall n k (v vl vr : vector (vec n) k),
    (forall i (ip : i < k), Vnth v ip =v Vnth vl ip [+] Vnth vr ip) ->
    add_vectors_trop v =v add_vectors_trop vl [+] add_vectors_trop vr.

  Proof.
    induction k; intros.
    VOtac. unfold add_vectors_trop. simpl. rewrite vector_plus_zero_r_trop. refl.
    VSntac v. VSntac vl. VSntac vr. do 3 rewrite add_vectors_cons_trop.
    rewrite (IHk (Vtail v) (Vtail vl) (Vtail vr)). do 3 rewrite Vhead_nth.
    rewrite (H 0 (Lt.lt_O_Sn k)).
    match goal with
      |- (?A [+] ?B) [+] (?C [+] ?D) =v (?A [+] ?C) [+] (?B [+] ?D) =>
        set (X := A); set (Y := B); set (W := C); set (V := D) end.
    do 2 rewrite <- vector_plus_assoc_trop. rewrite (vector_plus_assoc_trop W Y V).
    rewrite (vector_plus_comm_trop W Y). do 4 rewrite vector_plus_assoc_trop. refl.
    intros. do 3 rewrite Vnth_tail. apply H.
  Qed.

  (** Point-wise product. *)

  Definition dot_product_trop n (l r : vec n) :=
    Vfold_left Aplus A0 (Vmap2 Amult l r).

  Add Parametric Morphism n : (@dot_product_trop n)
    with signature (@eq_vec_trop n) ==> (@eq_vec_trop n) ==> eqA
      as dot_product_mor_trop.

  Proof.
    induction n; intros. VOtac. 
    refl. revert H H0.
    VSntac x. VSntac y. VSntac x0. VSntac y0. intros.
    rewrite (eq_vec_cons eqA) in H3. rewrite (eq_vec_cons eqA) in H4. intuition.
    unfold dot_product_trop. simpl. unfold dot_product_trop in IHn.
    rewrite (IHn _ _ H6 _ _ H7). rewrite H5. rewrite H3. refl.
  Qed.

  Lemma dot_product_zero_trop : forall n (v v' : vec n),
    Vforall (fun el => el =A= A0) v -> dot_product_trop v v' =A= A0.

  Proof.
    induction n; intros.
    VOtac.
    refl.
    VSntac v. VSntac v'. unfold dot_product_trop. simpl.
    fold (dot_product_trop (Vtail v) (Vtail v')). rewrite IHn.
    assert (Vhead v =A= A0). rewrite Vhead_nth. apply Vforall_nth. hyp.
    rewrite H2. ring.
    apply Vforall_incl with (S n) v. intros.
    apply Vin_tail. hyp. hyp.
  Qed.

  Lemma A_plus_0_lt : forall n:TropicalDom, (A0 + n) =A= n.

  Proof.
    intros. ring.
  Qed.

  Lemma A_plus_0_t : forall n, (n + A0) =A= n.

  Proof.
    intros. ring.
  Qed.

  Lemma dot_product_id_trop : forall i n (ip : i < n) v,
    dot_product_trop (id_vec_trop ip) v =A= Vnth v ip.

  Proof.
    induction i. intros. 
    destruct n. absurd_arith.
    (* induction base *)
    VSntac v. unfold id_vec, dot_product_trop.
    destruct (Vhead v); try discr; simpl in *.
    fold (dot_product_trop (Vconst A0 n) (Vtail v)).
    rewrite dot_product_zero_trop. ring.
    apply Vforall_nth_intro. intros.
    rewrite Vnth_const. refl.
    fold (dot_product_trop (Vconst A0 n) (Vtail v)).
    rewrite dot_product_zero_trop. ring.
    apply Vforall_nth_intro. intros.
    rewrite Vnth_const. refl.
    (* induction step *)
    intros. destruct n. NatUtil.absurd_arith.
    VSntac v. unfold dot_product_trop. simpl.
    rewrite <- (IHi n (Lt.lt_S_n ip) (Vtail v)).
    ring_simplify. unfold dot_product_trop. apply A_plus_0_t.
  Qed.

  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).

  Lemma dot_product_comm_trop : forall n (u v : vec n),
    dot_product_trop u v =A= dot_product_trop v u.

  Proof.
    induction n.
    refl. intros. VSntac u. VSntac v. unfold dot_product_trop. simpl.
    unfold dot_product_trop in IHn. rewrite IHn at 1. ring.
  Qed.

  Lemma dot_product_distr_r_trop : forall n (v vl vr : vec n),
    dot_product_trop v (vl [+] vr) =A= dot_product_trop v vl
    + dot_product_trop v vr.

  Proof.
    induction n; intros.
    VOtac. unfold dot_product_trop. simpl. refl.
    VSntac v. VSntac vl. VSntac vr. unfold dot_product_trop. simpl.
    fold (Vtail vl [+] Vtail vr).
    fold (dot_product_trop (Vtail v) (Vtail vl [+] Vtail vr)).
    rewrite IHn. unfold dot_product_trop. ring.
  Qed.

  Lemma dot_product_distr_l_trop : forall n (v vl vr : vec n),
    dot_product_trop (vl [+] vr) v =A= dot_product_trop vl v + dot_product_trop vr v.

  Proof.
    intros. 
    rewrite dot_product_comm_trop. rewrite dot_product_distr_r_trop. 
    rewrite (dot_product_comm_trop v vl). rewrite (dot_product_comm_trop v vr). refl.
  Qed.

  Lemma dot_product_cons_trop : forall n al ar (vl vr : vec n),
    dot_product_trop (Vcons al vl) (Vcons ar vr) =A= al * ar + dot_product_trop vl vr.

  Proof.
    intros. unfold dot_product_trop. simpl. ring.
  Qed.

  Lemma dot_product_distr_mult_trop : forall n a (v v' : vec n),
    a * dot_product_trop v v'
    =A= dot_product_trop (Vbuild (fun i ip => a * Vnth v ip)) v'.

  Proof.
    induction n; intros.
    VOtac. unfold dot_product_trop. simpl. ring.
    rewrite (VSn_eq (Vbuild (fun i (ip : i < S n) => a * Vnth v ip))).
    VSntac v. VSntac v'. do 2 rewrite dot_product_cons_trop. ring_simplify.
    rewrite IHn. 
    rewrite Vbuild_tail. rewrite Vbuild_head. simpl. ring_simplify.
    match goal with
      |- _ + dot_product_trop ?X _ =A= _ + dot_product_trop ?Y _ => replace X with Y end.
    refl. apply Veq_nth. intros. 
    do 2 rewrite Vbuild_nth. rewrite NatUtil.lt_Sn_nS. refl.
  Qed.

  (** Hints and tactics. *)

  Hint Rewrite vector_plus_zero_l vector_plus_zero_r add_vectors_cons : arith.

  Ltac Vplus_eq := simpl; (try ring_simplify);
    match goal with
      | |- ?vl [+] ?vr = ?vl' [+] ?vr' => 
        replace vl with vl'; [replace vr with vr'; try refl | try refl]
    end.

End VectorArith_tropicdom.

(***********************************************************************)
(** ** Functor OrdVectorArith over domain tropical. *)

Section OrdVectorArith_trop.

  Notation A := At.
  Notation eqA := eqAt.
  Notation sid_theoryA := sid_theoryAt.
  Notation vec := (vector A).
  Notation ge := get.
  Notation ge_refl := ge_reflt.
  Notation ge_trans := ge_transt.
  Notation "x >>= y" := (ge x y) (at level 70).

  Add Setoid A eqA sid_theoryA as A_Setoidt.

  Add Relation At ge 
  reflexivity proved by ge_refl
  transitivity proved by ge_trans
    as ge_rel_arct.

  Notation "x =A= y" := (eqA x y) (at level 70).
  Parameter eq_ge_compatt : forall x y, x =A= y -> x >>= y.
  Definition vec_ge_trop {n} := Vreln (n:=n) get.
  Infix ">=v" := vec_ge_trop (at level 70).
  Definition vec_ge_refl_trop := Vreln_refl ge_refl.
  Definition vec_ge_trans_trop := Vreln_trans ge_trans.
  Definition vec_ge_dec_trop := Vreln_dec ge_dect.

  Add Parametric Morphism n : (@vec_ge_trop n)
    with signature (@eq_vec_trop n) ==> (@eq_vec_trop n) ==> iff
      as vec_ge_mor_trop.

  Proof.
    unfold vec_ge_trop. intros. apply (Vforall2n_mor sid_theoryAt). intuition.
    trans a1. apply eq_ge_compatt. sym. hyp.
    trans a2. hyp. apply eq_ge_compatt. hyp.
    trans a1'. apply eq_ge_compatt. hyp.
    trans a2'. hyp. apply eq_ge_compatt. sym. hyp.
    hyp. hyp.
  Qed.

  Implicit Arguments vec_ge_mor_trop [n x y x0 y0].

  Infix "[+]" := (vector_plus_trop) (at level 50).

  Lemma vec_plus_ge_compat_trop : forall n (vl vl' vr vr' : vec n), 
    vl >=v vl' -> vr >=v vr' -> vl [+] vr >=v vl' [+] vr'.

  Proof.
    unfold vector_plus_trop, vec_ge_trop. intros. apply Vforall2n_intro.
    intros. simpl. do 2 rewrite Vnth_map2.
    apply plus_ge_compatt.
    apply Vforall2n_nth. hyp.
    apply Vforall2n_nth. hyp.
  Qed.

  Lemma vec_plus_ge_compat_r_trop : forall n (vl vl' vr : vec n), 
    vl >=v vl' -> vl [+] vr >=v vl' [+] vr.

  Proof.
    intros. apply vec_plus_ge_compat_trop. hyp. exact (vec_ge_refl_trop vr).
  Qed.

  Lemma vec_plus_ge_compat_l_trop : forall n (vl vr vr' : vec n), 
    vr >=v vr' -> vl [+] vr >=v vl [+] vr'.

  Proof.
    intros. apply vec_plus_ge_compat_trop. exact (vec_ge_refl_trop vl). hyp.
  Qed.

End OrdVectorArith_trop.

