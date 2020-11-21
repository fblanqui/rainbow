(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frédéric Blanqui, 2009-03-19 (setoids), 2014-02-19 (classes)
- Adam Koprowski, 2007-04-02

Vector arithmetic.
*)

Set Implicit Arguments.

Require Import VecUtil RelUtil SemiRing OrdSemiRing2 NatUtil LogicUtil
  Setoid Morphisms.

(***********************************************************************)
(** ** Definition of constants and operations. *)

Section def.

  Context {SR : SemiRing}. Import SR_Notations.

  Notation vec := (vector s_typ).

  (** Null vector. *)

  Definition zero_vec := Vconst 0.

  (** Unit vector whose i-th component is 1. *)

  Definition id_vec n i (ip : i < n) := Vreplace (zero_vec n) ip 1.

  (** Binary addition. *)

  Definition vector_plus n (v1 v2 : vec n) := Vmap2 sr_add v1 v2.

  (** Nary addition. *)

  Definition add_vectors n k (v : vector (vec n) k) := 
    Vfold_left (@vector_plus n) (zero_vec n) v.

  (** Point-wise multiplication. *)

  Definition dot_product n (l r : vec n) :=
    Vfold_left sr_add 0 (Vmap2 sr_mul l r).

End def.

Arguments zero_vec {SR n}.
Arguments id_vec {SR n i} _.

(** Notations. *)

Infix "[+]" := vector_plus (at level 50).

(***********************************************************************)
(** ** Properties. *)

Section props.

  Context {SR : SemiRing}.
  Import SR_Notations.
  Add Ring SR : sr_th.

  Notation vec := (vector s_typ).
  Notation veq := (Vforall2 s_eq).
  Infix "=v"   := veq (at level 70).

(***********************************************************************)
(** Binary addition. *)

  Global Instance vector_plus_mor n :
    Proper (veq ==> veq ==> veq) (vector_plus (n:=n)).

  Proof.
    intros u u' uu' v v' vv'. apply Vforall2_intro_nth. intros.
    unfold vector_plus. rewrite !Vnth_map2.
    (*FIXME: rewrite H does not work even if Vnth is declared as morphism *)
    apply sr_add_eq; apply Vforall2_elim_nth; hyp.
  Qed.

  Lemma vector_plus_nth n (vl vr : vec n) i (ip : i < n) :
    Vnth (vl [+] vr) ip == Vnth vl ip + Vnth vr ip.

  Proof.
    unfold vector_plus. rewrite Vnth_map2. refl.
  Qed.

  Lemma vector_plus_comm n (v1 v2 : vec n) : v1 [+] v2 =v v2 [+] v1.

  Proof.
    apply Vforall2_intro_nth. intros. rewrite !vector_plus_nth. ring.
  Qed.

  Lemma vector_plus_assoc n (v1 v2 v3 : vec n) :
    v1 [+] (v2 [+] v3) =v v1 [+] v2 [+] v3.

  Proof.
    apply Vforall2_intro_nth. intros. rewrite !vector_plus_nth. ring.
  Qed.

  Lemma vector_plus_zero_r n (v : vec n) : v [+] zero_vec =v v.

  Proof.
    apply Vforall2_intro_nth. intros. rewrite vector_plus_nth.
    set (w := Vnth_const 0 ip). fold (zero_vec (n:=n)) in w.
    rewrite w. ring.
  Qed.

  Lemma vector_plus_zero_l n (v : vec n) : zero_vec [+] v =v v.

  Proof.
    intros. rewrite vector_plus_comm. apply vector_plus_zero_r.
  Qed.

(***********************************************************************)
(** Nary addition. *)

  Global Instance add_vectors_mor n k :
    Proper (Vforall2 veq ==> veq) (add_vectors (n:=n) (k:=k)).

  Proof.
    induction x; simpl; intros. VOtac. refl. revert H. VSntac y.
    unfold add_vectors. simpl. rewrite Vforall2_cons_eq. intuition.
    rewrite H1. apply vector_plus_mor. 2: refl.
    eapply Vfold_left_proper. apply vector_plus_mor. refl. hyp.
  Qed.

  Lemma add_vectors_cons n i (a : vec n) (v : vector (vec n) i) :
    add_vectors (Vcons a v) =v a [+] add_vectors v.

  Proof.
    unfold add_vectors. simpl. rewrite vector_plus_comm. refl.
  Qed.

  Lemma add_vectors_zero n k (v : vector (vec n) k) : 
    Vforall (fun v => v =v zero_vec) v -> add_vectors v =v zero_vec.

  Proof.
    induction v. refl. rewrite add_vectors_cons. simpl. intuition.
    rewrite H0. rewrite vector_plus_zero_l. hyp.
  Qed.

  Lemma add_vectors_perm n i v v' (vs : vector (vec n) i) :
    add_vectors (Vcons v  (Vcons v' vs)) =v
    add_vectors (Vcons v' (Vcons v  vs)).

  Proof.
    rewrite !add_vectors_cons, !vector_plus_assoc,
    (vector_plus_comm v v'). refl.
  Qed.

  Lemma add_vectors_nth : forall n k (vs : vector (vec n) k) i (ip : i < n),
    Vnth (add_vectors vs) ip == 
    Vfold_left sr_add 0 (Vmap (fun v => Vnth v ip) vs).

  Proof.
    induction vs; simpl; intros.
    unfold add_vectors, zero_vec; simpl.
    rewrite Vnth_const. refl.
    rewrite (Vforall2_elim_nth (R:=s_eq)).
    2: rewrite add_vectors_cons; refl.
    rewrite vector_plus_nth. rewrite IHvs.
    rewrite Aplus_comm. refl.
  Qed.

  Lemma add_vectors_split : forall n k (v vl vr : vector (vec n) k),
    (forall i (ip : i < k),
    Vnth        v ip =v Vnth        vl ip [+] Vnth        vr ip) ->
    add_vectors v    =v add_vectors vl    [+] add_vectors vr.

  Proof.
    induction k; intros.
    VOtac. unfold add_vectors. simpl. rewrite vector_plus_zero_r. refl.
    VSntac v. VSntac vl. VSntac vr. do 3 rewrite add_vectors_cons.
    rewrite (IHk (Vtail v) (Vtail vl) (Vtail vr)). do 3 rewrite Vhead_nth.
    rewrite (H _ (lt_O_Sn k)).
    match goal with
      |- (?A [+] ?B) [+] (?C [+] ?D) =v (?A [+] ?C) [+] (?B [+] ?D) =>
        set (X := A); set (Y := B); set (W := C); set (V := D) end.
    rewrite <- !vector_plus_assoc, (vector_plus_assoc W Y V),
      (vector_plus_comm W Y), !vector_plus_assoc. refl.
    intros. rewrite !Vnth_tail. apply H.
  Qed.

(***********************************************************************)
(** Point-wise multiplication. *)

  Global Instance dot_product_mor n :
    Proper (veq ==> veq ==> s_eq) (dot_product (n:=n)).

  Proof.
    intros u u' uu' v v' vv'; revert u u' uu' v v' vv'.
    induction n; intros. VOtac. refl.
    revert uu' vv'. VSntac u. VSntac v. VSntac u'. VSntac v'.
    intros H3 H4.
    rewrite Vforall2_cons_eq in H3.
    rewrite Vforall2_cons_eq in H4.
    intuition.
    unfold dot_product. simpl.
    unfold dot_product in IHn.
    rewrite (IHn _ _ H6 _ _ H7), H5, H3. refl.
  Qed.

  Lemma dot_product_zero : forall n (v v' : vec n),
    Vforall (fun x => x == 0) v -> dot_product v v' == 0.

  Proof.
    induction n; intros.
    VOtac. refl.
    VSntac v. VSntac v'. unfold dot_product. simpl.
    fold (dot_product (Vtail v) (Vtail v')). rewrite IHn.
    assert (Vhead v == 0). rewrite Vhead_nth.
    apply Vforall_nth. hyp.
    rewrite H2. ring.
    apply Vforall_incl with (S n) v. intros.
    apply Vin_tail. hyp. hyp.
  Qed.

  Lemma dot_product_id : forall i n (ip : i < n) v,
    dot_product (id_vec ip) v == Vnth v ip.

  Proof.
    induction i. intros. 
    destruct n. absurd_arith.
    (* induction base *)
    VSntac v. unfold id_vec, dot_product. simpl.
    fold (dot_product (Vconst 0 n) (Vtail v)).
    rewrite dot_product_zero. ring.
    apply Vforall_nth_intro. intros.
    rewrite Vnth_const. refl.
    (* induction step *)
    intros. destruct n. absurd_arith.
    VSntac v. unfold dot_product. simpl.
    rewrite <- (IHi n (lt_S_n ip) (Vtail v)).
    ring_simplify. unfold dot_product. refl.
  Qed.

  Lemma dot_product_comm : forall n (u v : vec n),
    dot_product u v == dot_product v u.

  Proof.
    induction n. refl. intros. VSntac u. VSntac v.
    unfold dot_product. simpl.
    unfold dot_product in IHn. rewrite IHn. ring.
  Qed.

  Lemma dot_product_distr_r : forall n (v vl vr : vec n),
    dot_product v (vl [+]              vr) ==
    dot_product v  vl  + dot_product v vr.

  Proof.
    induction n; intros.
    VOtac. unfold dot_product. simpl. ring.
    VSntac v. VSntac vl. VSntac vr.
    unfold dot_product. simpl.
    fold (Vtail vl [+] Vtail vr).
    fold (dot_product (Vtail v) (Vtail vl [+] Vtail vr)).
    rewrite IHn. unfold dot_product. ring.
  Qed.

  Lemma dot_product_distr_l : forall n (v vl vr : vec n),
    dot_product (vl  [+]            vr) v ==
    dot_product  vl v + dot_product vr  v.

  Proof.
    intros. rewrite dot_product_comm.
    rewrite dot_product_distr_r. 
    rewrite (dot_product_comm v vl).
    rewrite (dot_product_comm v vr). refl.
  Qed.

  Lemma dot_product_cons : forall n al ar (vl vr : vec n),
    dot_product (Vcons al vl) (Vcons ar vr) ==
    al * ar + dot_product vl vr.

  Proof.
    intros. unfold dot_product. simpl. ring.
  Qed.

  Lemma dot_product_distr_mult : forall n a (v v' : vec n),
    a * dot_product v v' ==
    dot_product (Vbuild (fun i ip => a * Vnth v ip)) v'.

  Proof.
    induction n; intros.
    VOtac. unfold dot_product. simpl. ring.
    rewrite (VSn_eq (Vbuild (fun i (ip : i < S n) => a * Vnth v ip))).
    VSntac v. VSntac v'.
    do 2 rewrite dot_product_cons. 
    ring_simplify. rewrite IHn. 
    rewrite Vbuild_tail.
    rewrite Vbuild_head. simpl. ring_simplify.
    match goal with
      |- _ + dot_product ?X _ == _ + dot_product ?Y _ =>
      replace X with Y end.
    refl. apply Veq_nth. intros. 
    do 2 rewrite Vbuild_nth. rewrite lt_Sn_nS. refl.
  Qed.

End props.

Hint Rewrite @vector_plus_zero_l @vector_plus_zero_r @add_vectors_cons
: arith.

(***********************************************************************)
(** Point-wise ordering. *)

Section osr.

  Context {OSR : OrderedSemiRing}.
  Import OSR_Notations.

  Notation vec := (vector s_typ).
  Notation veq := (Vforall2 s_eq).
  Infix "=v"   := veq (at level 70).
  Notation vge := (Vforall2 osr_ge).
  Infix ">=v"  := vge (at level 70).

  Global Instance vec_ge_mor n :
    Proper (veq ==> veq ==> iff) (Vforall2 osr_ge (n:=n)).

  Proof.
    apply Vforall2_aux_Proper. class.
  Qed.

  Lemma vec_plus_ge_compat : forall n (vl vl' vr vr' : vec n), 
    vl        >=v vl'         ->
           vr >=v         vr' ->
    vl [+] vr >=v vl' [+] vr'.

  Proof.
    unfold vector_plus. intros.
    apply Vforall2_intro_nth.
    intros. simpl. do 2 rewrite Vnth_map2.
    apply osr_add_ge.
    apply Vforall2_elim_nth. hyp.
    apply Vforall2_elim_nth. hyp.
  Qed.

  Lemma vec_plus_ge_compat_r : forall n (vl vl' vr : vec n), 
    vl        >=v vl'        ->
    vl [+] vr >=v vl' [+] vr.

  Proof.
    intros. apply vec_plus_ge_compat. hyp. refl.
  Qed.

  Lemma vec_plus_ge_compat_l : forall n (vl vr vr' : vec n), 
           vr >=v        vr' ->
    vl [+] vr >=v vl [+] vr'.

  Proof.
    intros. apply vec_plus_ge_compat. refl. hyp.
  Qed.

End osr.

Arguments vec_ge_mor {OSR n} [x y] _ [x0 y0] _.
