(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Johannes Waldmann, 2010-04
*)

Set Implicit Arguments.

Require Import Morphisms AMonAlg2 Matrix2 OrdSemiRing2 VecUtil SN RelUtil
  LogicUtil Setoid AMatrixBasedInt2 SemiRing VecArith2.

(** Module type for proving termination with matrix interpretations *)

Section TTropicalBasedInt.

  Variable Sig: Signature.

  Context {OSR: OrderedSemiRing}.

  Import OSR_Notations.

  Variable dim: nat.

  Context {MI: TMatrixInt (OSR:=OSR) Sig dim}.
  
  Notation mint    := (@matrixInt _ dim).
  Notation dim_pos := (dim_pos dim).
  Notation vec     := (vector s_typ dim).

  Definition vec_at0 (v : vec) := Vnth v dim_pos.

     (* TODO: for refactoring we should change this condition to a
        predicate on [vec_at0], which would be general enough to 
        cover all three: arctic/arctic-below-zero/tropical *)

  Definition vec_invariant (v : vec) := 0 >> vec_at0 v.

  Variable A0_gt_A1 : 0 >> 1.
  
  Lemma inv_id_matrix : vec_invariant (id_vec dim_pos).
  
  Proof.
    unfold vec_invariant, vec_at0, id_vec.
    rewrite Vnth_replace. exact A0_gt_A1.
  Qed.

  Global Instance Conf : MatrixMethodConf Sig dim.
  
  Proof.
    apply Build_MatrixMethodConf with
    (mic_vec_invariant := vec_invariant). apply MI. apply inv_id_matrix.
  Defined.
   
  Notation PlusInf := 0.
  
  Variable A0_min   : forall x, x >>= PlusInf.
  Variable ge_gt_eq : forall x y, x >>= y -> x >> y \/ x == y.
  
  Definition gtx x y := x >> y \/ (x == PlusInf /\ y == PlusInf).
  
  (* Add: Boolean function of [gtx]. *)
  
  Require Import BoolUtil.
  
  Definition bgtx x y : bool := 
    bgt _ x y || beq _ x PlusInf && beq _ y PlusInf.
  
  (* Correctness proof of boolean function for [gtx]. *)
  
  Lemma bgtx_ok : forall x y, bgtx x y = true <-> gtx x y.
  Proof.
    intros x y. split.
    (* -> *)
    intro H. unfold bgtx in H.
    rewrite orb_eq in H. destruct H.
    unfold gtx.
    (* Left part. *)
    left. apply bgt_ok. hyp.
    (* Right part. *)
    rewrite andb_eq in H. destruct H.
    unfold gtx. right.
    rewrite beq_ok in H. rewrite beq_ok in H0.
    auto.
    (* <- *)
    intro H. unfold bgtx. rewrite orb_eq. unfold gtx in H.
    destruct H. left.
    rewrite bgt_ok. hyp. 
    right. rewrite andb_eq. split.
    rewrite beq_ok. destruct H; auto.
    rewrite beq_ok. destruct H; auto.
  Qed.

  Notation "x >_0 y" := (gtx x y) (at level 70).

  Global Instance gtx_mor : Proper (s_eq ==> s_eq ==> iff) gtx.
  
  Proof.
    intros x x' xx' y y' yy'. unfold gtx. intuition.
    left. rewrite <- xx', <- yy'. hyp. right.
    split. trans x. sym. hyp. hyp. trans y. sym. hyp. hyp.
    left. rewrite xx', yy'. hyp. right. split.
    trans x'; hyp. trans y'; hyp.
  Qed.

  Global Instance gtx_trans : Transitive gtx.
  
  Proof.
    unfold gtx. intros x y z. intuition.
    left. apply osr_gt_trans with y; hyp.
    rewrite H2. rewrite H0 in H1. auto.
    rewrite H. rewrite H2 in H1. auto.
  Qed.
  
  Definition succ_vec {n}                   := Vforall2 gtx (n:=n).
  Definition succ (x y : (@dom _ Sig _ _) ) := succ_vec (dom2vec x) (dom2vec y).
  Notation "x >v y"                         := (succ x y) (at level 70).
  
  Global Instance succ_trans : Transitive succ.
  
  Proof.
    change (Transitive (Rof succ_vec (@dom2vec _ _ _ _))). apply Rof_trans.
    unfold succ_vec. class.
  Qed.
  
  (*FIXME: Proper*)
  Lemma ge_gtx_compat : forall x y z, x >>= y -> y >_0 z -> x >_0 z.
  
  Proof.
    unfold gtx. intuition. left. apply osr_ge_gt with y; hyp.
    rewrite H2. rewrite H0 in H. destruct (@ge_gt_eq x PlusInf H); intuition.
  Qed.
  
  Variable succ_wf : WF succ.

  Variable gtx_plus_compat : forall m m' n n',
    m >_0 m' -> n >_0 n' -> m + n >_0 m' + n'.
  
  Variable gtx_mult_compat : forall m m' n n',
    m >_0 m' -> n >>= n' -> m * n >_0 m' * n'.
  
  Lemma succ_succeq_compat : absorbs_left succ (@succeq _ _ _ _).
  
  Proof.
    intros x z xz. destruct xz as [y [xy yz] ].
    unfold succ, succ_vec. apply Vforall2_intro_nth. intros.
    apply ge_gtx_compat with (Vnth (dom2vec y) ip).
    apply Vforall2_elim_nth. hyp.
    apply Vforall2_elim_nth. hyp.
  Qed.
  
  Lemma gtx_dec : rel_dec gtx.
  
  Proof.
    intros x y. destruct (osr_gt_dec x y).
    left. left. hyp.
    destruct (ds_eq_dec x PlusInf).
    destruct (ds_eq_dec y PlusInf).
    left. right. auto.
    right. unfold gtx. intuition.
    right. unfold gtx. intuition.
  Defined.
  
  Lemma succ_dec : rel_dec succ.
  
  Proof.
    intros x y. unfold succ.
    apply (Vforall2_dec gtx_dec (dom2vec x) (dom2vec y)).
  Defined.

  Variable mi_eval_ok : forall f v,
    vec_invariant (mi_eval_aux (mi_trsInt f) (Vmap (@dom2vec _ _ _ _) v)).
  
  Notation I       := (I mi_eval_ok).
  Notation IR_succ := (IR I succ).
  
  Definition mat_gt := mat_forall2 gtx (m:=dim) (n:=dim).
  Definition vec_gt := Vforall2 gtx (n:=dim).
  
  Definition mint_gt n (l r : mint n) := 
    Vforall2 mat_gt (args l) (args r) /\ vec_gt (const l) (const r).
  
  Definition term_gt := term_gt mint_gt.
  
  Lemma mat_gt_dec : rel_dec mat_gt.
  
  Proof.
    unfold mat_gt. apply mat_forall2_dec. exact gtx_dec.
  Defined.

  (* Add : Boolean function of [mat_gt] *)
  
  Definition bmat_gt (M N: matrix dim dim) :=
    match mat_gt_dec M N with
      | left _  => true
      | right _ => false
    end.
    
  (* Add: Correctness proof of [mat_ge]. *)
  
  Lemma bmat_gt_ok : forall (M N : matrix dim dim),
    bmat_gt M N = true <-> mat_gt M N.

  Proof.
    intros M N. unfold bmat_gt. case_eq (mat_gt_dec M N); intuition.
  Qed.
  
  (* Add: boolean function of [mint_gt] *)
  
  Definition bmint_gt n (l r : mint n) : bool :=
    bVforall2 bmat_gt (args l) (args r) &&
    bVforall2 (fun m n => bgtx m n) (const l) (const r).
  
  (* Correctness proof of boolean function for [mint_gt]. *)
  
  Lemma bmint_gt_ok : forall n (l r : mint n),
    bmint_gt l r = true <-> mint_gt l r.

  Proof.
    intros n l r. split.
    (* -> *)
    intro H. unfold bmint_gt in H.
    rewrite andb_eq in H. destruct H.
    unfold mint_gt. split.
    (* Left part. *)
    rewrite bVforall2_ok in H. apply H.
    (* Proving boolean function of [bmat_gt]. *)
    intros M N. split.
    (* -> *)
    intro H1. apply bmat_gt_ok. hyp.
    (* <- *)
    intro H1. rewrite bmat_gt_ok. hyp.
    (* Right part. *)
    rewrite bVforall2_ok in H0. apply H0.
    (* Proving boolean function of [bgtx]. *)
    intros x y. split.
    (* -> *)
    intro H1. apply bgtx_ok. hyp.
    (* <- *)
    intro H1. rewrite bgtx_ok. hyp.
    (* [2]. <- *)
    intro H. unfold bmint_gt.
    rewrite andb_eq. split.
    (* Left part. *)
    rewrite bVforall2_ok. unfold mint_gt in H.
    destruct H. apply H.
    (* Proving boolean function of [bmat_gt]. *)
    intros M N. split.
    (* -> *)
    intro H1. apply bmat_gt_ok. hyp.
    (* <- *)
    intro H1. rewrite bmat_gt_ok. hyp.
    (* Right part. *)
    rewrite bVforall2_ok. unfold mint_gt in H.
    destruct H. apply H0.
    (* Proving boolean function of [bgtx]. *)
    intros x y. split.
    (* -> *)
    intro H1. apply bgtx_ok. hyp.
    (* <- *)
    intro H1. rewrite bgtx_ok. hyp.
  Qed.
  
  Lemma vec_gt_dec : rel_dec vec_gt.
  
  Proof.
    unfold vec_gt, rel_dec. apply Vforall2_dec. exact gtx_dec.
  Defined.
  
  Lemma mint_gt_dec : forall n, rel_dec (@mint_gt n).
  
  Proof.
    intros n x y. unfold mint_gt.
    destruct (Vforall2_dec mat_gt_dec (args x) (args y)); 
      intuition.
    destruct (vec_gt_dec (const x) (const y)); intuition.      
  Defined.
  
  Lemma Vfold_left_gtx_compat : forall n (v v' : vector s_typ n),
    (forall i (ip: i < n), Vnth v ip >_0 Vnth v' ip) ->
    Vfold_left sr_add sr_0 v >_0 Vfold_left sr_add sr_0 v'.
  
  Proof.
    induction v; simpl; intros.
    VOtac. simpl. right. intuition.
    VSntac v'. simpl. apply gtx_plus_compat.
    apply IHv. intros. 
    apply Vforall2_elim_nth. change v with (Vtail (Vcons h v)). 
    apply Vforall2_tail. apply Vforall2_intro_nth. hyp.
    change h with (Vhead (Vcons h v)). do 2 rewrite Vhead_nth.
    apply (H _ (Lt.lt_O_Sn n)).
  Qed.
  
  Section Matrix.
    
    Variables (m n p : nat) (M M' : matrix m n) (N N' : matrix n p).
    
    Notation vge := (Vforall2 osr_ge).
    Notation vgt := (Vforall2 gtx).
    Notation mge := mat_ge.
    Notation mgt := (mat_forall2 gtx).
    
    Lemma arctic_dot_product_mon : forall i (v v' w w' : vector s_typ i), 
       vgt v v' -> vge w w' -> dot_product v w >_0 dot_product v' w'.
    
    Proof.
      unfold dot_product. induction v; intros; simpl.
      right. intuition.
      apply gtx_plus_compat.
      apply IHv.
      change v with (Vtail (Vcons h v)). apply Vforall2_tail. hyp.
      apply Vforall2_tail. hyp.
      apply gtx_mult_compat. change h with (Vhead (Vcons h v)). 
      do 2 rewrite Vhead_nth. apply Vforall2_elim_nth. hyp.
        do 2 rewrite Vhead_nth. apply Vforall2_elim_nth. hyp.
    Qed.
    
    Lemma mat_arctic_mult_mon : mgt M M' -> mge N N' -> mgt (M <*> N) (M' <*> N').
    
    Proof.
      intros. unfold mat_forall2. intros.
      do 2 rewrite mat_mult_spec. apply arctic_dot_product_mon.
      apply Vforall2_intro_nth. intros. 
      exact (H i i0 ip ip0).
      apply Vforall2_intro_nth. intros.
      do 2 rewrite <- get_elem_swap. exact (H0 i0 j ip0 jp).
    Qed.
    
  End Matrix.

  Notation mat    := (matrix dim dim).
  Notation vec_ge := (Vforall2 osr_ge).
  Infix ">=v"     := vec_ge (at level 70).
  
  Lemma mat_vec_prod_gt_compat : forall (M M' : mat) m m', 
    mat_gt M M' -> m >=v m' -> vec_gt (mat_vec_prod M m) (mat_vec_prod M' m').
  
  Proof.
    intros. unfold mat_vec_prod, vec_gt. apply Vforall2_intro_nth. 
    intros. do 2 rewrite Vnth_col_mat. 
    apply mat_arctic_mult_mon. hyp.
    intros k l pk pl. do 2 rewrite vec_to_col_mat_spec.
    apply Vforall2_elim_nth. hyp.
  Qed.
  
  Lemma mint_eval_mon_succ : forall (val : valuation I) k (mi mi' : mint k),
    mint_gt mi mi' -> succ_vec (mint_eval val mi) (mint_eval val mi').
  
  Proof.
    intros. unfold succ_vec. apply Vforall2_intro_nth. intros. destruct H.
    eapply gtx_mor. apply Vforall2_elim_nth; rewrite mint_eval_split; refl.
    apply Vforall2_elim_nth. rewrite mint_eval_split. refl.
    do 2 rewrite vector_plus_nth.
    apply gtx_plus_compat. 
    apply Vforall2_elim_nth. hyp.
    do 2 rewrite add_vectors_nth.
    apply Vfold_left_gtx_compat. intros.
    do 2 rewrite Vnth_map. do 2 rewrite Vnth_map2.
    set (eval := Vnth (Vbuild (fun i (_ : i < k) => val i)) ip0).
    apply Vforall2_elim_nth. apply mat_vec_prod_gt_compat.
    apply Vforall2_elim_nth. hyp. refl.
  Qed.

  Lemma term_gt_incl_succ : term_gt << IR_succ.

  Proof.
    intros l r lr v. destruct (mint_eval_equiv l r v). simpl in *.
    unfold succ. unfold succ_vec. symmetry in H. symmetry in H0.
    rewrite (Vforall2_aux_Proper gtx_mor _ _ H _ _ H0).
    apply mint_eval_mon_succ. hyp.
  Qed.

  Definition succ'     := term_gt.
  Definition succ'_sub := term_gt_incl_succ.
  Definition succ'_dec := term_gt_dec mint_gt mint_gt_dec.

  Global Instance MonotoneAlgebra_Trop : MonotoneAlgebraType Sig.

  Proof.
    apply Build_MonotoneAlgebraType with
    (ma_int     := I)
    (ma_succ    := succ)
    (ma_succeq  := @succeq _ _ _ _)
    (ma_succeq' := @succeq' _ _ _ _)
    (ma_succ'   := term_gt).
    apply refl_succeq.
    apply succ_trans.
    apply trans_succeq.
    apply monotone_succeq.
    apply succ_wf.
    apply succ_succeq_compat.
    apply term_gt_incl_succ.
    apply succeq'_sub.
    apply succ'_dec.
    apply succeq'_dec.
  Defined.

End TTropicalBasedInt.

