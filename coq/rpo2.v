(**************************************************************************)
(*           *                                                            *)
(*     _     *   The Coccinelle Library / Evelyne Contejean               *)
(*    <o>    *          CNRS-LRI-Universite Paris Sud                     *)
(*  -/@|@\-  *                   A3PAT Project                            *)
(*  -@ | @-  *                                                            *)
(*  -\@|@/-  *      This file is distributed under the terms of the       *)
(*    -v-    *      CeCILL-C licence                                      *)
(*           *                                                            *)
(**************************************************************************)

(* RPO definition extended by Sorin Stratulat by considering a
quasi-ordering for the precedence instead of an ordering. *)

Require Import rpo term2 ASignature Relations list_permut Bool List
closure more_list equiv_list dickson Wellfounded Arith Wf_nat
term_spec term decidable_set ordered_set Recdef Program.

Set Implicit Arguments.

Section RPO.

  Variable Sig : Signature.

  Variable P : Precedence (symbol Sig).

  Notation term := (term Sig).

  (** ** Definition of rpo.*)

    Inductive equiv : term -> term -> Prop :=
    | Eq     : forall t, equiv t t
    | Eq_lex : forall f g l1 l2,
               status P f = Lex -> status P g = Lex ->
               prec_eq P f g -> equiv_list_lex l1 l2 -> 
               equiv (Term f  l1) (Term g l2) 
    | Eq_mul : forall f g l1 l2,  status P f = Mul ->
               status P g = Mul ->
               prec_eq P f g -> permut0 equiv l1 l2 ->
               equiv (Term f l1) (Term g l2)

    with equiv_list_lex : list term -> list term -> Prop :=
    | Eq_list_nil : equiv_list_lex nil nil
    | Eq_list_cons : 
      forall t1 t2 l1 l2, equiv t1 t2 -> equiv_list_lex l1 l2 ->
        equiv_list_lex (t1 :: l1) (t2 :: l2).

    Inductive rpo (bb : nat) : term -> term -> Prop :=
    | Subterm : forall f l t s, mem equiv s l -> rpo_eq bb t s -> rpo bb t (Term f l)
    | Top_gt : 
      forall f g l l', prec P g f -> (forall s', mem equiv s' l' -> rpo bb s' (Term f l)) -> 
        rpo bb (Term g l') (Term f l)
    | Top_eq_lex : 
      forall f g l l', status P f = Lex -> status P g = Lex -> prec_eq P f g ->
                       (length l = length l' \/ (length l' <= bb /\ length l <= bb)) ->
                       rpo_lex bb l' l -> 
        (forall s', mem equiv s' l' -> rpo bb s' (Term g l)) ->
        rpo bb (Term f l') (Term g l)
    | Top_eq_mul : 
      forall f g l l', status P f = Mul  -> status P g = Mul -> prec_eq P f g ->
                       rpo_mul bb l' l -> rpo bb (Term f l') (Term g l)

    with rpo_eq (bb : nat) : term -> term -> Prop :=
    | Equiv : forall t t', equiv t t' -> rpo_eq bb t t'
    | Lt : forall s t, rpo bb s t -> rpo_eq bb s t

    with rpo_lex (bb : nat) : list term -> list term -> Prop :=
    | List_gt : forall s t l l', rpo bb s t -> rpo_lex bb (s :: l) (t :: l')
    | List_eq : forall s s' l l', equiv s s' -> rpo_lex bb l l' ->
                                  rpo_lex bb (s :: l) (s' :: l')
    | List_nil : forall s l, rpo_lex bb nil (s :: l)

    with rpo_mul ( bb : nat) : list term -> list term -> Prop :=
    | List_mul : forall a lg ls lc l l', 
      permut0 equiv l' (ls ++ lc) -> permut0 equiv l (a :: lg ++ lc) ->
      (forall b, mem equiv b ls -> exists a', mem equiv a' (a :: lg) /\ rpo bb b a') ->
      rpo_mul bb l' l.

    Notation variable := nat (only parsing).
    Notation symbol := (symbol Sig) (only parsing).
    Notation eq_var_bool := var_eq_bool.
    Notation eq_bool_ok := (eq_bool_symb_ok Sig).
    Notation eq_bool := (eq_bool_symb Sig).

 (* Define function [equiv_bool_F] used in the definition of [equiv_bool_terminate]. *)

  Definition equiv_bool_F := 
    (fun (equiv_bool : term -> term -> bool) (t1 t2 : term) =>
      match t1, t2 with
        | Var v1, Var v2 => eq_var_bool v1 v2
        | Var _, Term _ _ => false
        | Term _ _, Var _ => false
        | Term f1 l1, Term f2 l2 =>
          if prec_eq_bool P f1 f2
            then
              match status P f1 with
                | Lex => 
                  let equiv_lex_bool :=
                    (fix equiv_lex_bool (kk1 kk2 : list term) {struct kk1} :  bool :=  
                      (match kk1 with
                         | [] => match kk2 with [] => true | _ :: _=> false end
                         | t1 :: k1 => 
                           match kk2 with 
                             [] => false 
                             | t2 :: k2=> (equiv_bool t1 t2) && (equiv_lex_bool k1 k2)
                           end
                       end)) in
                    (equiv_lex_bool l1 l2)
                | Mul => 
                  let equiv_mult_bool :=
                    (fix equiv_mult_bool (kk1 kk2 : list term) {struct kk1} :  bool :=  
                      (match kk1 with
                         | [] => match kk2 with [] => true | _ :: _=> false end
                         | t1 :: k1 => 
                           match remove equiv_bool t1 kk2 with 
                             None => false 
                             | Some k2 => equiv_mult_bool k1 k2 end
                       end)) in
                    (equiv_mult_bool l1 l2)
              end
            else false
      end) : (term -> term -> bool) -> term -> term -> bool.

  (* Define function [equiv_bool_terminate] used in the function [equiv_bool]. *)

  (*Require Import Datatypes.*)

  Notation size := (@size Sig).

  Definition equiv_bool_terminate :
    forall t1 t2 : term,
      {v : bool |  forall k : nat, (size t1) <= k ->
        forall def : term -> term -> bool,
          iter (term -> term -> bool) k equiv_bool_F def t1 t2 = v}.
  intro t1.
  assert (Acc_t1 := well_founded_ltof term size t1).
  induction Acc_t1 as [t1 Acc_t1 IHAcc].
  revert Acc_t1 IHAcc; case t1; clear t1; [intro v1 | intros f1 l1]; 
    (intros Acc_t1 IHAcc t2; case t2; clear t2; [intro v2 | intros f2 l2]).

  exists (eq_var_bool v1 v2); intros [ | p] p_lt_k def.
  apply False_ind; exact (gt_irrefl 0 p_lt_k).
  exact (refl_equal _).

  exists false; intros [ | p] p_lt_k def.
  apply False_ind; exact (gt_irrefl 0 p_lt_k).
  exact (refl_equal _).

  exists false; intros [ | p] p_lt_k def.
  apply False_ind; exact (le_Sn_O _ p_lt_k).
  exact (refl_equal _).

  rewrite size_unfold.
  assert ({v : bool |forall k : nat,list_size size l1 <= k ->
    forall def : term -> term -> bool,
      iter (term -> term -> bool) (S k)
      equiv_bool_F def (Term f1 l1) (Term f2 l2) = v}).
  unfold iter; simpl.
  case (prec_eq_bool P f1 f2).
  assert (IH : forall t1 : term, In t1 l1 ->
    forall t2 : term,
      {v : bool |forall k : nat,size t1 <= k ->
        forall def : term -> term -> bool,
          iter (term -> term -> bool) k equiv_bool_F def t1 t2 = v}).
  intros t1 t1_in_l1;
    exact (IHAcc t1 (size_direct_subterm t1 (Term f1 l1) t1_in_l1)).
  case (status P f1).
  clear IHAcc Acc_t1; revert l1 IH l2; fix equiv_lex_bool 1.
  intros l1; case l1.
  intros _ l2; case l2.
  exists true; intros k p_lt_k def; exact (refl_equal _).
  exists false; intros k p_lt_k def; exact (refl_equal _).
  intros a1 k1 IHl1 l2; case l2.
  exists false; intros k p_lt_k def; exact (refl_equal _).
  intros a2 k2; case (equiv_lex_bool k1 (tail_set _ IHl1) k2); intros bl IH'.
  case (IHl1 a1 (or_introl _ (refl_equal _)) a2); intros ba IH''.
  exists (ba && bl); intros k p_le_k def.
  assert (pa_lt_k : size a1 <= k).
  apply le_trans with (list_size size (a1 :: k1)); [apply le_plus_l | exact p_le_k].
  rewrite (IH'' k pa_lt_k).
  assert (pl_le_k : list_size size k1 <= k).
  apply le_trans with (list_size size (a1 :: k1)); [apply le_plus_r | exact p_le_k].
  rewrite (IH' k pl_le_k def).
  reflexivity.

  clear IHAcc Acc_t1 f2.
  revert l1 IH l2; fix IHl1 1.
  intro l1; case l1; clear l1.
  intros _ l2; case l2.
  exists true; intros k p_lt_k def; exact (refl_equal _).
  exists false; intros k p_lt_k def; exact (refl_equal _).
  intros a1 l1 IH l2.
  assert (Hrem : {ok : option (list term) |
    forall k : nat, list_size size (a1 :: l1) <= k ->
      forall def : term -> term -> bool,
        remove (iter _ k equiv_bool_F def) a1 l2 = ok}).
  revert l2; fix IHl2 1.
  intro l2; case l2; clear l2.
  exists (@None (list term)); intro k; case k; clear k.
  intro L; apply False_rect.      
  apply (le_Sn_O _ (le_trans (size_ge_one a1) (le_trans (le_plus_l _ _) L))).
  intros k _ def; reflexivity.
  intros a2 l2;
    case (IH a1 (or_introl _ (refl_equal _)) a2); intro v; case v; intro Ha1.
  exists (Some l2); intros k L def; simpl; rewrite Ha1.
  reflexivity.
  apply le_trans with (list_size size (a1 :: l1)); [apply le_plus_l | apply L].
  case (IHl2 l2); clear IHl2; intro ok; case ok; clear ok.
  intros k2 IHl2; exists (Some (a2 :: k2)); intros k L def; simpl.
  rewrite Ha1.
  rewrite IHl2.
  reflexivity.
  apply L.
  apply le_trans with (list_size size (a1 :: l1)); [apply le_plus_l | apply L].
  intro IHl2; exists (@None (list term)); intros k L def; simpl.
  rewrite Ha1.
  rewrite IHl2.
  reflexivity.
  apply L.
  apply le_trans with (list_size size (a1 :: l1)); [apply le_plus_l | apply L].
  case Hrem; clear Hrem; intro ok; case ok; clear ok.
  intros k2 Hrem.
  case (IHl1 _ (tail_set _ IH) k2); intros v Hl1; exists v; intros k L def.
  rewrite (Hrem k L).
  assert (l1_le_k : list_size size l1 <= k).
  refine (le_trans _ L); apply le_plus_r.
  rewrite (Hl1 k l1_le_k def).
  reflexivity.
  intro Hrem; exists false; intros k L def.
  rewrite (Hrem k L).
  reflexivity.

  exists false; intros _ _ _; exact (refl_equal _).

  case H; clear H; intros v H; exists v; intro k; case k; clear k.
  intro L; apply False_rect.
  apply (le_Sn_O _ (le_trans (le_plus_l _ _) L)).
  intros k L def; rewrite (H k).
  reflexivity.
  apply (le_S_n  L).
  Defined.

  (* Define function [equiv_bool] used in lemma [equiv_bool_ok]. *)

  Definition equiv_bool := fun t1 t2 => let (v,_) := equiv_bool_terminate t1 t2 in v.

  (* The proof of [equiv_bool_equation] used in the proof of [equiv_bool_ok]. *)

  Lemma equiv_bool_equation :
    forall t1 t2, equiv_bool t1 t2 = 
      match t1, t2 with
        | Var v1, Var v2 => eq_var_bool v1 v2
        | Var _, Term _ _ => false
        | Term _ _, Var _ => false
        | Term f1 l1, Term f2 l2 =>
          if prec_eq_bool P f1 f2
            then
              match status P f1 with
                | Lex => 
                  let equiv_lex_bool :=
                    (fix equiv_lex_bool (kk1 kk2 : list term) {struct kk1} :  bool :=  
                      (match kk1 with
                         | [] => match kk2 with [] => true | _ :: _=> false end
                         | t1 :: k1 => 
                           match kk2 with 
                             [] => false 
                             | t2 :: k2=> (equiv_bool t1 t2) && (equiv_lex_bool k1 k2)
                           end
                       end)) in
                    (equiv_lex_bool l1 l2)
                | Mul => 
                  let equiv_mult_bool :=
                    (fix equiv_mult_bool (kk1 kk2 : list term) {struct kk1} :  bool :=  
                      (match kk1 with
                         | [] => match kk2 with [] => true | _ :: _=> false end
                         | t1 :: k1 => 
                           match remove equiv_bool t1 kk2 with 
                             None => false 
                             | Some k2 => equiv_mult_bool k1 k2 end
                       end)) in
                    (equiv_mult_bool l1 l2)
              end
            else false
      end.

  Proof.
    assert (H : forall t1 t2 k, size t1 <= k ->
      iter (term -> term -> bool) k equiv_bool_F equiv_bool t1 t2 = equiv_bool t1 t2).
    intros t1 t2 k L; unfold equiv_bool at 2; generalize (equiv_bool_terminate t1 t2).
    intro H; case H; clear H; intros v H; apply H; apply L.
    intro t1; pattern t1; apply term_rec3; clear t1.
    intros v1 [v2 | f2 l2]; reflexivity.
    intros f1 l1 IH [v2 | f2 l2].
    reflexivity.
    rewrite <- (H (Term f1 l1) (Term f2 l2) _ (le_n _)); rewrite size_unfold; simpl.
    case (prec_eq_bool P f1 f2); [idtac | reflexivity].
    case (status P f1); clear f1.
    assert (H' : forall l1 f1 f2, (forall t1, In t1 l1 ->
      forall t2, f1 t1 t2 = f2 t1 t2) -> forall l2,
      (fix equiv_lex_bool (kk1 kk2 : list term) : bool :=
        match kk1 with
          | [] => match kk2 with
                    | [] => true
                    | _ :: _ => false
                  end
          | t1 :: k1 =>
            match kk2 with
              | [] => false
              | t2 :: k2 => f1 t1 t2 && equiv_lex_bool k1 k2
            end
        end) l1 l2 =
      (fix equiv_lex_bool (kk1 kk2 : list term) : bool :=
        match kk1 with
          | [] => match kk2 with
                    | [] => true
                    | _ :: _ => false
                  end
          | t1 :: k1 =>
            match kk2 with
              | [] => false
              | t2 :: k2 => f2 t1 t2 && equiv_lex_bool k1 k2
            end
        end) l1 l2).
    clear l1 l2 IH; intro l1; induction l1 as [ | a1 l1]; intros g1 g2 IH [ | a2 l2].
    reflexivity.
    reflexivity.
    reflexivity.
    apply f_equal2.
    apply IH; left; reflexivity.
    apply (IHl1 g1 g2 (tail_prop _ IH) l2).
    refine (H' l1 _ _ _ l2); clear H'.
    intros t1 t1_in_l1 t2; apply H.
    generalize (size_direct_subterm t1 (Term f2 l1) t1_in_l1).
    rewrite (size_unfold (Term f2 l1)).
    simpl; intro L; apply (le_S_n L).
    assert (H' : forall l1 f1 f2, (forall t1, In t1 l1 ->
      forall t2, f1 t1 t2 = f2 t1 t2) -> forall l2,
      (fix equiv_mult_bool (kk1 kk2 : list term) : bool :=
        match kk1 with
          | [] => match kk2 with
                    | [] => true
                    | _ :: _ => false
                  end
          | t1 :: k1 =>
            match
              remove f1 t1 kk2
              with
              | Some k2 => equiv_mult_bool k1 k2
              | None => false
            end
        end) l1 l2 =
      (fix equiv_mult_bool (kk1 kk2 : list term) : bool :=
        match kk1 with
          | [] => match kk2 with
                    | [] => true
                    | _ :: _ => false
                  end
          | t1 :: k1 =>
            match remove f2 t1 kk2 with
              | Some k2 => equiv_mult_bool k1 k2
              | None => false
            end
        end) l1 l2).
    clear l1 l2 IH; intro l1; induction l1 as [ | a1 l1]; intros g1 g2 IH l2.
    reflexivity.
    assert (H' : forall f1 f2, (forall t2, f1 a1 t2 = f2 a1 t2) ->
      forall l2, remove f1 a1 l2 = remove f2 a1 l2).
    clear l1 l2 g1 g2 IH IHl1; intros g1 g2 IH; induction l2 as [ | a2 l2].
    reflexivity.
    simpl; rewrite (IH a2); rewrite IHl2; reflexivity.
    rewrite (H' g1 g2 (IH a1 (or_introl _ (refl_equal _)))).
    case (remove g2 a1 l2).
    intro k2; apply (IHl1 g1 g2 (tail_prop _ IH)).
    reflexivity.
    refine (H' l1 _ _ _ l2).
    intros t1 t1_in_l1 t2; apply H.
    generalize (size_direct_subterm t1 (Term f2 l1) t1_in_l1).
    rewrite (size_unfold (Term f2 l1)).
    simpl; intro L; apply (le_S_n L).
  Defined.

  (* The proof of [equiv_equiv] used in the proof of
     [trans_equiv_aterm] in Coccinelle2.v *)

  Lemma equiv_equiv  : equivalence term equiv.
    
  Proof.
    split.
    (* Reflexivity *)
    intro t; apply Eq.
    (* Transitivity *)
    intros t1; pattern t1; apply term_rec3.
    (* 1/3 variable case *)
    intros v t2 t3 t1_eq_t2 t2_eq_t3; inversion t1_eq_t2; subst; trivial.
    (* 1/2 compound case *)
    intros f l1 E_l1 t2 t3 t1_eq_t2 t2_eq_t3; 
      inversion t1_eq_t2 as
        [ | f' g' l1' l2 Sf Sg eq_f_g l1_eq_l2 H22 H'
          | f' g' l1' l2 Sf Sg eq_f_g ]; subst; trivial;
        inversion t2_eq_t3 as
          [ | f' g'' l2' l3 Sf' Sg' eq_f_g' l2_eq_l3 H22 H''
            | f' g'' l2' l3 Sf' Sg' eq_f_g' P' ]; subst; trivial.
    (* 1/5 Lex case *)
    apply Eq_lex; trivial.
    apply prec_eq_transitive with g'; trivial.
    generalize l2 l3 l1_eq_l2 l2_eq_l3;
      clear t1_eq_t2 t2_eq_t3 l2 l3 l1_eq_l2 l2_eq_l3;
        induction l1 as [ |s1 l1]; intros l2 l3 l1_eq_l2 l2_eq_l3.
    inversion l1_eq_l2; subst; trivial.
    inversion l1_eq_l2 as [ | s1' s2 l1' l2' s1_eq_s2 l1'_eq_l2']; subst.
    inversion l2_eq_l3 as [ | s2' s3 l2'' l3' s2_eq_s3 l2''_eq_l3']; subst.
    apply Eq_list_cons.
    apply E_l1 with s2; trivial; left; trivial.
    apply IHl1 with l2'; trivial.
    intros t t_in_l1; apply E_l1; right; trivial.
    (* 1/4 absurd case *)
    rewrite Sg in Sf'; discriminate.
    (* 1/3 absurd case *)
    rewrite Sg in Sf'; discriminate.
    (* 1/2 Mul case *)
    apply Eq_mul; trivial.
    apply prec_eq_transitive with g'; trivial.
    apply permut_trans with l2; trivial.
    intros a b c a_in_l1 _ _; apply E_l1; trivial.
    (* Symmetry *)
    intros t1; pattern t1; apply term_rec3; clear t1.
    intros v t2 t1_eq_t2; inversion t1_eq_t2; subst; trivial.
    intros f l1 IHl t2 t1_eq_t2; 
      inversion t1_eq_t2 as 
        [ | f' g' l1' l2 Sf Sg preceq_f_g l1_eq_l2 
          | f' g' l1' l2 Sf Sg preceq_f_g]; clear t1_eq_t2; subst.
    apply Eq.
    apply Eq_lex; trivial.
    apply prec_eq_sym. trivial.
    generalize l2 l1_eq_l2; clear l2 l1_eq_l2; 
      induction l1 as [ | t1 l1]; intros l2 l1_eq_l2;
        inversion l1_eq_l2 as [ | s1 s2 l1' l2' s1_eq_s2 l1'_eq_l2']; subst; trivial.
    apply Eq_list_cons.
    apply IHl; trivial; left; trivial.
    apply IHl1; trivial.
    intros t t_in_l1; apply IHl; right; trivial.
    apply Eq_mul; trivial.
    apply prec_eq_sym. trivial.
    apply permut_sym; trivial.
    intros a b a_in_l1 _; apply IHl; trivial.
  Qed.

  (* Define [equiv] as transitivity/reflexivity and symmetry. Used in
     the proof of [equiv_bool_ok]. *)
  
  Add Relation term equiv
  reflexivity proved by (Relation_Definitions.equiv_refl _ _ equiv_equiv)
  symmetry proved by (Relation_Definitions.equiv_sym _ _ equiv_equiv)
    transitivity proved by (Relation_Definitions.equiv_trans _ _ equiv_equiv) as EQUIV_RPO.

  (* Proof lemma [equiv_bool_ok] used in the proof of [term_rec3_mem]. *)

  Notation eq_var_bool_ok := var_eq_bool_ok.

  (* REMARK: [equiv] has the same name in [Relations_Definitions] and
     [Classes.v] in Coq's library. [Eq] also has a same name in
     [Datatypes.v] *)

  Lemma equiv_bool_ok : forall t1 t2,
    match equiv_bool t1 t2 with true => equiv t1 t2 | false => ~equiv t1 t2 end.

  Proof.
    intros t1; pattern t1; apply term_rec3; clear t1.
    intros v1 t2; case t2; clear t2.
    intro v2; rewrite equiv_bool_equation;
      generalize (eq_var_bool_ok v1 v2); case (eq_var_bool v1 v2).
    intro v1_eq_v2; rewrite v1_eq_v2; apply Eq.
    intros v1_diff_v2 v1_eq_v2; apply v1_diff_v2; inversion v1_eq_v2; reflexivity.
    intros f2 l2; rewrite equiv_bool_equation; intro t1_eq_t2; inversion t1_eq_t2.
    intros f1 l1 IH t2; case t2; clear t2.
    intros v2; rewrite equiv_bool_equation; intro t1_eq_t2; inversion t1_eq_t2.
    intros f2 l2; rewrite equiv_bool_equation.
    case_eq (prec_eq_bool P f1 f2).
    intro f1_eq_f2; case_eq (status P f1).
    intro Lex_f1; simpl.
    assert (H : if (fix equiv_lex_bool (kk1 kk2 : list term) : bool :=
      match kk1 with
        | [] => match kk2 with
                  | [] => true
                  | _ :: _ => false
                end
        | t1 :: k1 =>
          match kk2 with
            | [] => false
            | t2 :: k2 => equiv_bool t1 t2 && equiv_lex_bool k1 k2
          end
      end) l1 l2
      then equiv_list_lex l1 l2 else ~equiv_list_lex l1 l2).
    revert l2; induction l1 as [ | a1 l1]; intro l2; case l2; clear l2.
    apply Eq_list_nil.
    intros a2 l2; simpl; intro l1_eq_l2; inversion l1_eq_l2.
    simpl; intro l1_eq_l2; inversion l1_eq_l2.
    intros a2 l2; simpl; generalize (IH a1 (or_introl _ (refl_equal _)) a2).
    case (equiv_bool a1 a2).
    intro a1_eq_a2; generalize (IHl1 (tail_prop _ IH) l2).
    simpl.
    case ((fix equiv_lex_bool (kk1 kk2 : list term) : bool :=
      match kk1 with
        | [] => match kk2 with
                  | [] => true
                  | _ :: _ => false
                end
        | t1 :: k1 =>
          match kk2 with
            | [] => false
            | t3 :: k2 => equiv_bool t1 t3 && equiv_lex_bool k1 k2
          end
      end) l1 l2).
    intro l1_eq_l2; apply Eq_list_cons; assumption.
    intros l1_diff_l2 l1_eq_l2; apply l1_diff_l2; inversion l1_eq_l2; assumption.
    intros a1_diff_a2 l1_eq_l2; apply a1_diff_a2; inversion l1_eq_l2; assumption.
    revert H; simpl.
    case ((fix equiv_lex_bool (kk1 kk2 : list term) : bool :=
      match kk1 with
        | [] => match kk2 with
                  | [] => true
                  | _ :: _ => false
                end
        | t1 :: k1 =>
          match kk2 with
            | [] => false
            | t3 :: k2 => equiv_bool t1 t3 && equiv_lex_bool k1 k2
          end
      end) l1 l2).
    intro l1_eq_l2.  apply Eq_lex; trivial. assert (H2:= prec_eq_bool_ok).
    assert (H2':= H2 _ P f1 f2). rewrite f1_eq_f2 in H2'.
    assert (H5:= prec_eq_status P f1 f2).
    assert (H6: status P f1 = status P f2).
    apply H5; trivial. rewrite <- H6. trivial.
    assert (H2:= prec_eq_bool_ok). assert (H2':= (H2 _ P f1 f2)).
    rewrite f1_eq_f2 in H2'. trivial.
    intros l1_diff_l2 t1_eq_t2; inversion t1_eq_t2; subst l2.
    apply l1_diff_l2; generalize l1; intro l; induction l as [ | a l].
    apply Eq_list_nil.
    apply Eq_list_cons; [apply Eq | assumption].
    apply l1_diff_l2; assumption.
    subst f2; rewrite Lex_f1 in H3. discriminate.
    intro Mul_f1; simpl.
    assert (H : if (fix equiv_mult_bool (kk1 kk2 : list term) : bool :=
      match kk1 with
        | [] => match kk2 with
                  | [] => true
                  | _ :: _ => false
                end
        | t1 :: k1 =>
          match remove equiv_bool t1 kk2 with
            | Some k2 => equiv_mult_bool k1 k2
            | None => false
          end
      end) l1 l2
      then permut0 equiv l1 l2 else ~permut0 equiv l1 l2).
    revert l2; induction l1 as [ | a1 l1].
    intro l2; case l2; clear l2.
    simpl; apply Pnil.
    intros a2 l2; simpl; intro t1_eq_t2; inversion t1_eq_t2.
    assert (R : forall l2,
      match remove equiv_bool a1 l2 with
        | Some _ =>
          {a2 : term & 
            {l2' : list term & 
              {l2'' : list term |
                equiv a1 a2 /\
                l2 = l2' ++ a2 :: l2'' /\
                remove equiv_bool a1 l2 = Some (l2' ++ l2'')}}}
        | None => forall a2, equiv a1 a2 -> ~ In a2  l2
      end).
    intro l2; induction l2 as [ | a2 l2].
    intros a2 a1_eq_a2 F; assumption.
    rewrite remove_equation.
    generalize (IH a1 (or_introl _ (refl_equal _)) a2);
      case (equiv_bool a1 a2).
    intro a1_eq_a2; exists a2; exists (@nil term);
      exists l2; repeat split; assumption.
    intro a1_diff_a2; revert IHl2; case (remove equiv_bool a1 l2).
    intros k2 [a1' [l2' [l2'' [H1 [H2 H3]]]]];
      exists a1'; exists (a2 :: l2'); exists l2''; repeat split.
    assumption.
    simpl; apply f_equal; assumption.
    simpl; do 2 apply f_equal; injection H3; intros; assumption.
    simpl; intros a1_not_in_l2; intros a a_eq_a1 [a_eq_a2 | a_in_l2].
    subst a; apply a1_diff_a2; assumption.
    apply (a1_not_in_l2 a a_eq_a1 a_in_l2).
    intro l2; generalize (R l2); case (remove equiv_bool a1 l2).
    intros k2 [a2 [k2' [k2'' [H1 [H2 H3]]]]].
    generalize (IHl1 (tail_prop _ IH) k2); simpl.
    injection H3; clear H3; intro H3; 
      case ((fix equiv_mult_bool (kk1 kk2 : list term) : bool :=
        match kk1 with
          | [] => match kk2 with
                    | [] => true
                    | _ :: _ => false
                  end
          | t1 :: k1 =>
            match remove equiv_bool t1 kk2 with
              | Some k3 => equiv_mult_bool k1 k3
              | None => false
            end
        end) l1 k2).
    intro P1; subst l2 k2; apply Pcons; assumption.
    intros not_P P1; subst l2 k2; apply not_P.
    apply (@permut_cons_inside term term equiv) with a1 a2.
    intros u3 u1 u4 u2 _ _ _ _ H31 H41 H42; transitivity u1.
    assumption.
    transitivity u4.
    symmetry; assumption.
    assumption.
    assumption.
    assumption.
    intros H P1; inversion P1 as [ | a1' a2 l1' l2' l2'' a1_eq_a2 P'].
    apply (H a2 a1_eq_a2); subst l2; apply in_or_app; right; left; reflexivity.
    revert H; case ((fix equiv_mult_bool (kk1 kk2 : list term) : bool :=
      match kk1 with
        | [] => match kk2 with
                  | [] => true
                  | _ :: _ => false
                end
        | t1 :: k1 =>
          match remove equiv_bool t1 kk2 with
            | Some k2 => equiv_mult_bool k1 k2
            | None => false
          end
      end) l1 l2).
    intro P1. apply Eq_mul. assumption.
    assert (H2:= prec_eq_bool_ok). assert (H2':= H2 _ P f1 f2).
    rewrite f1_eq_f2 in H2'. assert (H6:= prec_eq_status P f1 f2); trivial.
    assert (H7: status P f1 = status P f2). apply H6. trivial.
    rewrite <- H7. trivial. 
    assert (H2:= prec_eq_bool_ok). assert (H2':= H2 _ P f1 f2).
    rewrite f1_eq_f2 in H2'. trivial.
    trivial. 
    intros not_P t1_eq_t2.
    inversion t1_eq_t2. subst l2.
    apply not_P; apply permut_refl; intros; reflexivity.
    rewrite Mul_f1 in H3; discriminate.
    apply not_P; assumption.
    intros f1_diff_f2 t1_eq_t2. inversion t1_eq_t2. rewrite H1 in f1_diff_f2.
    assert (H3:= prec_eq_bool_ok). assert (H3':= H3 _ P f2 f2).
    rewrite f1_diff_f2 in H3'. contradict H3'.
    apply prec_eq_refl. trivial.
    assert (H8:= prec_eq_bool_ok). assert (H8':= H8 _ P f1 f2).
    rewrite f1_diff_f2 in H8'. contradict H8'. trivial. 
    assert (H8:= prec_eq_bool_ok). assert (H8':= H8 _ P f1 f2).
    rewrite f1_diff_f2 in H8'. contradict H8'.  trivial. 
  Defined.
      
  (* Proof of lemma [equiv_same_size] used in the proof of [term_rec3_mem]. *)

  Lemma equiv_same_size : forall t t', equiv t t' -> size t = size t'.

  Proof.
    intros t; pattern t; apply term_rec2.
    intro n; induction n as [ | n]; intros t1 St1 t2 t1_eq_t2.
    absurd (1 <= 0); auto with arith; apply le_trans with (size t1); trivial;
      apply size_ge_one.
    inversion t1_eq_t2 as [ | f g l1' l2' Sf Sg prec_eq_f_g l1_eq_l2
      | f g l1' l2' Sf Sg prec_eq_f_g P1];  
    subst.
    trivial.
      (* Lex case *)
    do 2 rewrite size_unfold; apply (f_equal (fun n => 1 + n)).
    generalize l2' l1_eq_l2; clear l2' l1_eq_l2 t1_eq_t2.
    induction l1' as [ | t1 l1]; intros l2 l1_eq_l2; 
      inversion l1_eq_l2 as [ | s1 s2 l1' l2' s1_eq_s2 l1'_eq_l2']; subst; trivial.
    simpl.
    assert (St1' : size t1 <= n).
    apply le_S_n; apply le_trans with (size (Term f (t1 :: l1))); trivial.
    apply size_direct_subterm; left; trivial.
    rewrite (IHn t1 St1' s2); trivial. 
    assert (Sl1 : (size) (Term f l1) <= S n).
    apply le_trans with (size (Term f (t1 :: l1))); trivial.
    do 2 rewrite size_unfold.
    simpl; apply le_n_S.
    apply (plus_le_compat_r 0 (size t1) (list_size size l1)).
    apply lt_le_weak; apply (size_ge_one t1).
    rewrite (IHl1 Sl1 l2'); trivial.
      (* Mul case *)
    subst; do 2 rewrite size_unfold; apply (f_equal (fun n => 1 + n)).
    apply (@permut_size _ _ equiv); trivial.
    intros a a' a_in_l1 _ a_eq_a'; apply IHn; trivial.
    apply le_S_n.
    apply le_trans with (size (Term f l1')); trivial.
    apply size_direct_subterm; trivial.
  Qed.

  (* Proof lemma [term_rec3_mem] used in the proof of [wf_rpo]. *)
  
  Lemma term_rec3_mem : 
    forall P : term -> Type,
      (forall v : variable, P (Var Sig v)) ->
      (forall (f : symbol) (l : list term),
        (forall t : term, mem equiv t l -> P t) -> P (Term f l)) ->
      forall t : term, P t.
  Proof.
    intros P1 Hvar Hterm. 
    apply term_rec2; induction n; intros t Size_t.
    absurd (1 <= 0); auto with arith; 
      apply le_trans with (size t); trivial; apply size_ge_one.
    destruct t as [ x | f l ]; trivial;
      apply Hterm; intros; apply IHn;
        apply lt_n_Sm_le.
    apply lt_le_trans with (size (Term f l)); trivial.
    destruct (mem_split_set _ _ equiv_bool_ok _ _ H) as [t' [l1 [l2 [t_eq_t' [H' _]]]]].
    simpl in t_eq_t'; simpl in H'; subst l.
    rewrite (equiv_same_size t_eq_t').
    apply size_direct_subterm; simpl; apply in_or_app; right; left; trivial.
  Qed.

  (* [rpo_rest] type used in the proof of [wf_rpo_rest]. *)

  Inductive rpo_rest (bb : nat) : (symbol * list term) -> (symbol * list term) -> Prop :=
  | Top_gt_rest : 
    forall f g l l', prec P g f -> 
      (forall s, mem equiv s l -> Acc (rpo bb) s) ->
      (forall s, mem equiv s l' -> Acc (rpo bb) s) ->
      rpo_rest bb (g, l') (f, l)
  | Top_eq_lex_rest : 
    forall f g l l', status P f = Lex -> status P g = Lex ->
      prec_eq P f g ->
      (length l = length l' \/ length l' <= bb /\ length l <= bb) ->
      rpo_lex bb l' l -> 
      (forall s, mem equiv s l -> Acc (rpo bb) s) ->
      (forall s, mem equiv s l' -> Acc (rpo bb) s) ->
      rpo_rest bb (f, l') (g, l)
  | Top_eq_mul_rest : 
    forall f g l l', status P f = Mul ->
      status P g = Mul -> prec_eq P f g -> rpo_mul bb l' l -> 
      (forall s, mem equiv s l -> Acc (rpo bb) s) ->
      (forall s, mem equiv s l' -> Acc (rpo bb) s) ->
      rpo_rest bb (f, l') (g, l).

  (* [rpo_lex_rest] type used in the proof of [wf_rpo_lex_rest]. *)

  Inductive rpo_lex_rest (bb bb' : nat) : list term -> list term -> Prop :=
  | Rpo_lex_rest : 
    forall l l', (length l = length l' \/ (length l' <= bb /\ length l <= bb)) ->
      (forall s, mem equiv s l -> Acc (rpo bb') s) ->
      (forall s, mem equiv s l' -> Acc (rpo bb') s) ->
      rpo_lex bb' l' l -> rpo_lex_rest bb bb' l' l.

  (* Definition of [size2] used in the definition of [o_size2]. *)

  Definition size2 s := match s with (s1,s2) => (@size s1, @size s2) end.

  (* Definition of [o_size2] used in the proof [wf_size2]. *)

  Definition o_size2 s t := lex var_eq_bool lt lt (size2 s) (size2 t).
 
  (* The proof of [wf_size2] used in the proof of [equiv_rpo_equiv_1]. *)

  Lemma wf_size2 : well_founded o_size2.

  Proof.
    refine (wf_inverse_image _ _ (lex  var_eq_bool lt lt) size2 _);
      apply wf_lex.
    exact var_eq_bool_ok.
    apply lt_wf.
    apply lt_wf.
  Defined.

  (* The proof of [mem_mem] used in the proof of [equiv_rpo_equiv_1]. *)

  Lemma mem_mem :
    forall t l1 l2, equiv_list_lex l1 l2 ->  (mem equiv t l1 <-> mem equiv t l2).
  Proof.
    intros t l1 l2 l1_eq_l2; split.
    generalize t l2 l1_eq_l2; clear t l2 l1_eq_l2; induction l1 as [ | t1 l1]; 
      intros t l2 l1_eq_l2 t_mem_l1.
    contradiction.
    inversion l1_eq_l2 as [ | s1 s2 l1' l2' s1_eq_s2 l1_eq_l2']; subst.
    destruct t_mem_l1 as [ t_eq_t1 | t_mem_l1].
    left; transitivity t1; trivial.
    right; apply IHl1; trivial.
    generalize t l2 l1_eq_l2; clear t l2 l1_eq_l2; induction l1 as [ | t1 l1]; 
      intros t l2 l1_eq_l2 t_mem_l2;
        inversion l1_eq_l2 as [ | s1 s2 l1' l2' s1_eq_s2 l1_eq_l2']; subst.
    trivial.
    destruct t_mem_l2 as [ t_eq_t2 | t_mem_l2].
    left; transitivity s2; trivial.
    symmetry; trivial.
    right; apply IHl1 with l2'; trivial.
  Qed.

  (* The proof of [size2_lex1] used in [size2_lex1_mem]. *)

  Lemma size2_lex1 : 
    forall s f l t1 t2, In s l -> o_size2 (s,t1) (Term f l,t2).

  Proof.
    intros s f l t1 t2 s_in_l; unfold o_size2, size2, lex.
    generalize (eq_var_bool_ok (size s) (size (Term f l)));
      case (eq_var_bool (size s) (size (Term f l))); [intro s_eq_t | intro s_lt_t].
    absurd (size (Term f l) < size (Term f l)); auto with arith;
      generalize (size_direct_subterm s (Term f l) s_in_l); rewrite s_eq_t; trivial.
    apply (size_direct_subterm s (Term f l) s_in_l).
  Defined.

  (* The proof of [size2_lex1_mem] used in the proof of [equiv_rpo_equiv_1]. *)

  Lemma size2_lex1_mem : 
    forall s f l t1 t2, mem equiv s l -> o_size2 (s,t1) (Term f l,t2).
  Proof.
    intros s f l t1 t2 s_mem_l;
      destruct (mem_split_set _ _ equiv_bool_ok _ _ s_mem_l) as [s' [l1 [l2 [s_eq_s' [H _]]]]].
    simpl in s_eq_s'; simpl in H.
    unfold o_size2, size2; rewrite (equiv_same_size s_eq_s').
    apply (size2_lex1 s' f l t1 t2).
    subst l; apply in_or_app; right; left; trivial.
  Qed.

  (* The proof of [equiv_list_lex_same_length] used in the proof of
     [equiv_rpo_equiv_1]. *)

  Lemma equiv_list_lex_same_length :
    forall l1 l2, equiv_list_lex l1 l2 -> length l1 = length l2.
  Proof.
    intros l1; induction l1 as [ | t1 l1]; intros l2 l1_eq_l2; 
      inversion l1_eq_l2 as [ | s1 s2 l1' l2' _ l1'_eq_l2']; subst; trivial.
    simpl; rewrite (IHl1 l2'); trivial.
  Qed.

  (* The proof of [o_size2_trans] used in the proof of
     [equiv_rpo_equiv_1]. *)

  Lemma o_size2_trans : transitive o_size2.

  Proof.
    intros [x1 x2] [y1 y2] [z1 z2].
    apply (lex_trans var_eq_bool var_eq_bool_ok).
    intros n m n_lt_m m_lt_n;
      generalize (lt_asym n m n_lt_m m_lt_n);
        contradiction.
    intros n1 n2 n3; apply lt_trans.
    intros n1 n2 n3; apply lt_trans.
  Qed.

  (* The proof of [size2_lex1_bis] used in the proof of
     [equiv_rpo_equiv_1]. *)

  Lemma size2_lex1_bis : 
    forall a f l t1 t2, o_size2 (Term f l, t1) (Term f (a::l), t2).
  Proof.
    intros a f l t1 t2; unfold o_size2, size2, lex;
      generalize (var_eq_bool_ok (size (Term f l)) (size (Term f (a :: l)))); 
        case (var_eq_bool (size (Term f l)) (size (Term f (a :: l)))); [intro s_eq_t | intro s_lt_t].
    do 2 rewrite size_unfold in s_eq_t; injection s_eq_t; clear s_eq_t; intro s_eq_t;
      absurd (list_size (@size ) l < list_size (@size ) l); auto with arith;
        generalize (plus_le_compat_r _ _ (list_size (@size ) l) (size_ge_one a));
          rewrite <- s_eq_t; trivial.
    do 2 rewrite size_unfold;
      simpl; apply lt_n_S; apply lt_le_trans with (1 + list_size (@size ) l);
        auto with arith; 
          apply plus_le_compat_r; apply size_ge_one.
  Defined.

  (* The proof of [equiv_rpo_equiv_1] used in the proof of
     [wf_rpo_lex_rest] *)

  Lemma equiv_rpo_equiv_1 :
    forall bb t t', equiv t t' -> (forall s, rpo bb s t <-> rpo bb s t').

  Proof.
    intro bb.
    assert (H : forall p,
      match p with (s,t) =>
        forall t', equiv t t' -> rpo bb s t -> rpo bb s t'
      end).
    intro p; pattern p; refine (well_founded_ind wf_size2 _ _ _); clear p.
    intros [s t] IH t' t_eq_t' s_lt_t.
    inversion t_eq_t' as [ t'' | f g'' l1 l2 Statf Statg eq_f_g H |
      f g'' l1 l2 Statf Statg eq_f_g P1]; subst.
    (* 1/4 equivalence is syntactic identity *)
    trivial.
    (* 1/3 equivalence with Lex top symbol *)
    inversion s_lt_t as  [g l t'' t' t'_mem_l t''_le_t'
      | g g' l l' g_prec_f l'_lt_t
      | g g''' l l' Stat_g Statg''' eq_g_g''' L l'_lt_ll1 l'_lt_t
      | g g''' l l' Stat_g Statg''' eq_g_g''' l'_lt_ll1 ]; subst.
    (* 1/6 equivalence with Lex top symbol, Subterm *)
    destruct t''_le_t' as [t'' t' t''_eq_t' | t'' t' t''_lt_t'];
      apply Subterm with t'; trivial.
    rewrite <- (mem_mem t' H); trivial.
    apply Equiv; trivial.
    rewrite <- (mem_mem t' H); trivial.
    apply Lt; trivial.
    (* 1/5 equivalence with Lex top symbol, Top_gt *)
    apply Top_gt; trivial.
    apply prec_eq_prec1 with f. trivial. trivial.
    intros s' s'_mem_l'.
    apply (IH (s',(Term f l1))); trivial.
    apply size2_lex1_mem; trivial.
    apply l'_lt_t; trivial.
    (* 1/4 equivalence with Lex top symbol,  Top_eq_lex *)
    apply Top_eq_lex; trivial. apply prec_eq_transitive with f; trivial.
    rewrite <- (equiv_list_lex_same_length H); assumption.
    clear t_eq_t' l'_lt_t s_lt_t L. revert l2 l' l'_lt_ll1 IH H. 
    induction l1 as [ | t1 l1]; intros l2 l' l'_lt_l1 IH l1_eq_l2;
      inversion l'_lt_l1 as [ s t1' l'' l1' s_lt_t1' L_eq 
        | t1' t1'' l'' l1' t1'_eq_t1'' l''_lt_l1' | s l'']; subst;
      inversion l1_eq_l2 as [ | t1'' t2 l1' l2' t1''_eq_t2 l1_eq_l2']; subst.
    simpl; apply List_gt.
    apply (IH (s,t1)); trivial.
    apply size2_lex1; left; trivial.
    apply List_eq.
    transitivity t1; trivial.
    apply IHl1; trivial.
    intros y H; apply IH.
    refine (o_size2_trans _ _ _ H _).
    apply size2_lex1_bis.
    apply List_nil.
    intros s' s'_mem_l'.
    apply (IH (s', Term f l1)); trivial.
    apply size2_lex1_mem; trivial.
    apply l'_lt_t; trivial.
    (* 1/3 equivalence with Lex top symbol,  Top_eq_mul *)
    rewrite Statf in Statg'''; discriminate.
    (* 1/2 equivalence with Mul top symbol *)
    inversion s_lt_t as  [g l t'' t' t'_mem_l t''_le_t'
      | g g' l l' g_prec_f l'_lt_t
      | g g''' l l' Stat_g Statg''' eq_g_g''' L l'_lt_ll1 l'_lt_t
      | g g''' l l' Stat_g Statg''' eq_g_g''' l'_lt_ll1 ]; subst.
    (* 1/5 equivalence with Mul top symbol , Subterm *)
    destruct t''_le_t' as [t'' t' t''_eq_t' | t'' t' t''_lt_t'];
      apply Subterm with t'; trivial.
    rewrite <- (mem_permut0_mem equiv_equiv  t' P1); trivial.
    apply Equiv; trivial.
    rewrite <- (mem_permut0_mem equiv_equiv t' P1); trivial.
    apply Lt; trivial.
    (* 1/4 equivalence with Mul top symbol,  Top_gt *)
    apply Top_gt; trivial. apply prec_eq_prec1 with f. trivial. trivial.
    intros s' s'_mem_l2.
    apply (IH (s', Term f l1)); trivial.
    apply size2_lex1_mem; trivial.
    apply l'_lt_t; trivial.
    (* 1/3 equivalence with Mul top symbol,  Top_eq_lex *)
    rewrite Statf in Statg'''; discriminate.
    (* 1/2 equivalence with Mul top symbol,  Top_eq_mul *)
    apply Top_eq_mul; trivial.
    apply prec_eq_transitive with f. trivial. trivial.
    inversion l'_lt_ll1 as [a lg ls lc l'' l''' Q1 Q2 ls_lt_alg]; subst.
    apply (@List_mul bb a lg ls lc); trivial.
    apply (permut0_trans equiv_equiv) with l1.
    apply (permut0_sym equiv_equiv). trivial. 
    exact Q2.

    intros t t' t_eq_t' s; split.
    apply (H (s,t)); trivial.
    apply (H (s,t')); trivial.
    apply (Relation_Definitions.equiv_sym _ _ equiv_equiv); trivial.
  Qed.

  (* The proof of [wf_rpo_lex_rest] used in the proof of [wf_rpo_rest]. *)

  Lemma wf_rpo_lex_rest : forall bb bb', well_founded (rpo_lex_rest bb bb').

  Proof.
    intro bb; unfold well_founded; induction bb.
    (* 1/2 bb = 0 *)
    intros bb' l; revert bb'; pattern l; apply list_rec2; clear l.
    induction n as [ | n]; intros [ | a l] L bb'.
    apply Acc_intro; intros k H;
      inversion H as [k' k'' L' Acc_k Acc_k' H' H1 H2];
        clear H; subst; inversion H'.
    inversion L.
    apply Acc_intro; intros k H; 
      inversion H as [k' k'' L' Acc_k Acc_k' H' H1 H2];
        clear H; subst; inversion H'.
    apply Acc_intro; intros k H;
      inversion H as [k' k'' L' Acc_k Acc_k' H' H1 H2]; subst.
    assert (Acc_a : Acc (rpo bb') a).
    apply Acc_k; left; apply Eq.
    assert (Acc_l' : forall s : term, mem equiv s l -> Acc (rpo bb') s).
    intros; apply Acc_k; right; assumption.
    apply Acc_inv with (a :: l); [idtac | assumption].
    clear k H L' Acc_k' H'.
    clear -IHn Acc_a L Acc_l'.
    simpl in L; generalize (le_S_n L); clear L; intro L.
    revert l L Acc_l'; induction Acc_a as [a Acc_a IHa]; intros l L Acc_l.
    assert (Acc_l' := IHn _ L bb').
    induction Acc_l' as [l Acc_l' IHl].
    apply Acc_intro; intros l' H;
      inversion H as [ k k' L' Acc_al Acc_l'' H' H1 H2]; clear H; subst.
    destruct L' as [L' | [L1 L2]]; [idtac | inversion L2].
    inversion H' as [u s' k' k'' u_lt_s | s' s'' k' k'' s'_eq_s k'_lt_l H1 H2 | u k'];
      clear H'; subst.
    (* 1/4 *)
    apply IHa; trivial.
    injection L'; clear L'; intro L'; rewrite <- L'; assumption.
    intros; apply Acc_l''; right; assumption.
    (* 1/3 *)
    apply Acc_intro.
    intros k'' H'; apply Acc_inv with (a :: k').
    apply IHl.
    constructor; trivial.
    left; injection L'; intro; assumption.
    intros; apply Acc_l''; right; assumption.
    injection L'; clear L'; intro L'; rewrite <- L'; assumption.
    intros; apply Acc_l''; right; assumption.
    inversion  H' as [k1 k1' L'' Acc_l1 Acc_l1' H1' H1 H2]; subst.
    constructor; trivial.
    simpl; intros s [s_eq_a | s_in_k']; [idtac | apply Acc_l1; right; assumption].
    apply Acc_intro; intros; apply Acc_inv with a.
    apply Acc_intro; apply Acc_a; trivial.
    rewrite <- (equiv_rpo_equiv_1 _ s_eq_a); trivial.
    inversion H1' as [u s'' k1' k1'' u_lt_s |
      s1' s'' k1' k1'' s'_eq_s1 k'_lt_l1 H1 H2 | u k1']; clear H1'; subst.
    constructor 1; trivial.
    rewrite <- (equiv_rpo_equiv_1 _ s'_eq_s); trivial.
    constructor 2; trivial.
    apply (equiv_trans _ _ equiv_equiv) with s'; trivial.
    constructor 3.
    (* 1/2 *)
    apply Acc_intro; intros l' H; inversion H as
      [ k k' L'' Acc_l1 Acc_l1' H' H1 H2]; clear H; subst.
    inversion H'.
    (* 1/1 induction step *)
    intros bb' l.
    apply Acc_intro; intros k H; inversion H as
      [k' k'' L' Acc_k Acc_k' H' H1 H2]; subst.
    destruct l as [ | a l].
    inversion H'.
    apply Acc_inv with (a :: l); [idtac | assumption].
    clear -IHbb Acc_k.
    assert (Acc_a : Acc (rpo bb') a).
    apply Acc_k; left; apply Eq.
    assert (Acc_l : forall s : term, mem equiv s l -> Acc (rpo bb') s).
    intros; apply Acc_k; right; assumption.
    revert Acc_l; clear Acc_k.
    revert l; induction Acc_a as [a Acc_a IHa]; intros l.
    pattern l; apply (well_founded_ind (IHbb bb'));
      clear l; intros l IHl Acc_l.
    apply Acc_intro; intros l' H; inversion H as
      [ k k' L Acc_al Acc_l' H' H1 H2]; clear H; subst.
    inversion H' as [u s' k' k'' u_lt_s |
      s' s'' k' k'' s'_eq_s k'_lt_l H1 H2 | u k']; clear H'; subst.
    (* 1/3 *)
    apply IHa; trivial.
    intros; apply Acc_l'; right; assumption.
    (* 1/2 *)
    apply Acc_intro.
    intros k'' H'; apply Acc_inv with (a :: k').
    apply IHl; constructor.
    destruct L as [L | [L1 L2]].
    left; injection L; intro; assumption.
    right; split; apply le_S_n; assumption.
    intros; apply Acc_al; right; assumption.
    intros; apply Acc_l'; right; assumption.
    assumption.
    apply Acc_inv; apply Acc_l'; right; assumption.
    inversion  H' as [ k1 k1' L' Acc_l1 Acc_l1' H1' H1 H2]; subst.
    constructor; trivial.
    simpl; intros s [s_eq_a | s_in_k']; [idtac | apply Acc_l1; right; assumption].
    apply Acc_intro; intros; apply Acc_inv with a.
    apply Acc_intro; apply Acc_a; trivial.
    rewrite <- (equiv_rpo_equiv_1 _ s_eq_a); trivial.
    inversion H1' as [u s'' k1' k1'' u_lt_s |
      s1' s'' k1' k1'' s'_eq_s1 k'_lt_l1 H1 H2 | u k1']; clear H1'; subst.
    constructor 1; trivial.
    rewrite <- (equiv_rpo_equiv_1 _ s'_eq_s); trivial.
    constructor 2; trivial.
    apply (equiv_trans _ _ equiv_equiv) with s'; trivial.
    constructor 3.
    (* 1/1 *)
    apply Acc_intro; intros l' H; inversion H as
      [ k k' L' Acc_l1 Acc_l1' H' H1 H2]; clear H; subst.
    inversion H'.
  Qed.
  
  (* The proof of [rpo_rest_prec_eq] used in the proof [wf_rpo_rest]. *)

  Lemma rpo_rest_prec_eq : forall bb f g l,
    prec_eq P f g -> Acc (rpo_rest bb) (f, l) -> Acc (rpo_rest bb) (g, l).

  Proof.
    intros.
    destruct H0.
    apply Acc_intro.
    intros.
    apply H0. clear H0.
    destruct y.
    inversion H1.
    apply Top_gt_rest.
    apply prec_eq_prec1 with g. trivial.
    apply prec_eq_sym. trivial. trivial. trivial.
    apply Top_eq_lex_rest; trivial. assert (H13:= prec_eq_status P f g).
    assert (H14: status P f = status P g).
    apply H13. trivial. rewrite  H14. trivial. 
    apply prec_eq_transitive with g; trivial. 
    apply prec_eq_sym; trivial.
    apply Top_eq_mul_rest; trivial.
    assert (H13:= prec_eq_status P f g).
    assert (H14: status P f = status P g).
    apply H13. trivial. rewrite  H14. trivial. 
    apply prec_eq_transitive with g; trivial. 
    apply prec_eq_sym; trivial.
  Qed.

  (* Type [rpo_mul_rest] used in the proof [wf_rpo_mul_rest]. *)

  Inductive rpo_mul_rest (bb : nat) : list term -> list term -> Prop :=
  | Rpo_mul_rest : 
    forall l l', (forall s, mem equiv s l -> Acc (rpo bb) s) -> 
      (forall s, mem equiv s l' -> Acc (rpo bb) s) ->
      rpo_mul bb l' l -> rpo_mul_rest bb l' l.

  (* Type [rpo_mul_step] used in the definition of type
     [rpo_mul_step_rest]. *)

  (** Definition of a finer grain for multiset extension. *)
  
  Inductive rpo_mul_step (bb : nat) : list term -> list term -> Prop :=
  | List_mul_step : 
    forall a ls lc l l',  
      permut0 equiv l' (ls ++ lc) -> permut0 equiv l (a :: lc) ->
      (forall b, mem equiv b ls -> rpo bb b a) ->
      rpo_mul_step bb l' l.

  (* Type [rpo_mul_step_rest] used in the proof of [wf_rpo_mul_rest]. *)

  Inductive rpo_mul_step_rest (bb : nat) : list term -> list term -> Prop :=
  | Rpo_mul_step_rest : 
    forall l l', (forall s, mem equiv s l -> Acc (rpo bb) s) -> 
      (forall s, mem equiv s l' -> Acc (rpo bb) s) ->
      rpo_mul_step bb l' l -> rpo_mul_step_rest bb l' l.

  (* Add those Relation to be able to proof in the [wf_rpo_mul_rest]. *)

  Add Relation term equiv 
  reflexivity proved by (Relation_Definitions.equiv_refl _ _ equiv_equiv)
  symmetry proved by (Relation_Definitions.equiv_sym _ _ equiv_equiv)
    transitivity proved by (Relation_Definitions.equiv_trans _ _ equiv_equiv) as EQA.

  Add Relation (list term) (permut0 equiv) 
  reflexivity proved by (permut0_refl equiv_equiv) 
  symmetry proved by (permut0_sym equiv_equiv) 
    transitivity proved by (permut0_trans equiv_equiv)
      as LP.

  Add Morphism (mem equiv)
    with signature equiv ==> permut0 equiv ==> iff
      as mem_morph2.
    exact (mem_morph2 equiv_equiv).
  Qed.
  
  Add Morphism (List.app (A:=term)) 
    with signature permut0 equiv ==> permut0 equiv ==> permut0 equiv
      as app_morph.
    exact (app_morph equiv_equiv).
  Qed.

  Add Morphism (List.cons (A:=term)) 
    with signature equiv ==> permut0 equiv ==> permut0 equiv
      as add_A_morph.
    exact (add_A_morph equiv_equiv).
  Qed.

  (* The proof of [equiv_rpo_equiv_2] used in the proof of
     [rpo_mul_rest_trans_clos]. *)

  Lemma equiv_rpo_equiv_2 :
    forall bb t t', equiv t t' -> (forall s, rpo bb t s <-> rpo bb t' s).

  Proof.
    intro bb.
    assert (H : forall p,
      match p with (s,t) =>
        forall t', equiv t t' -> rpo bb t s -> rpo bb t' s
      end).
    intro p; pattern p; refine (well_founded_ind wf_size2 _ _ _); clear p.
    intros [s t] IH t' t_eq_t' t_lt_s.
    inversion t_eq_t' as [ t'' | g g' l1 l2 Stat Statg' g_eq_g' l1_eq_l2 |
      g g' l1 l2 Stat Statg' g_eq_g' P1]; subst.
      (* 1/4 equivalence is syntactic identity *)
    trivial.
      (* 1/3 equivalence with Lex top symbol *)
    inversion t_lt_s as  [f l t'' t' t'_mem_l t''_le_t'
      | f f' l l' g_prec_f l'_lt_s
      | f' f l l' Stat_g Stat' f_stat_g L ll1_lt_l ll_lt_s
      | f' f l l' Stat_g Stat' f_stat_g ll1_lt_l ]; subst.
      (* 1/6 equivalence with Lex top symbol , Subterm *)
    destruct t''_le_t' as [t'' t' t''_eq_t' | t'' t' t''_lt_t'];
      apply Subterm with t'; trivial.
    apply Equiv.
    transitivity t''; trivial.
    symmetry; trivial.
    apply Lt.
    apply (IH (t',t'')); trivial.
    apply size2_lex1_mem; trivial.
      (* 1/5 equivalence with Lex top symbol,  Top_gt *)
    apply Top_gt; trivial.
    apply prec_eq_prec2 with g; trivial.
    intros s' s'_mem_l2. apply l'_lt_s.
    rewrite (@mem_mem s' l1 l2); trivial.
      (* 1/4 equivalence with Lex top symbol,  Top_eq_lex *)
    apply Top_eq_lex; trivial.
    apply prec_eq_transitive with g. apply prec_eq_sym. trivial. trivial.
    rewrite <- (equiv_list_lex_same_length l1_eq_l2); assumption.
    clear t_eq_t' ll_lt_s t_lt_s L; revert l2 l l1_eq_l2 ll1_lt_l IH.
    induction l1 as [ | t1 l1]; intros l2 l l1_eq_l2 l1_lt_l IH;
      inversion l1_lt_l as [ t1' s l1' l' t1'_lt_s L_eq 
        | t1' s l1' l'' t1'_eq_s l1'_lt_l'' 
        | s l']; subst;
      inversion l1_eq_l2 as [ | t1'' t2 l1' l2' t1''_eq_t2 l1_eq_l2']; subst.
    apply List_nil.
    simpl; apply List_gt.
    apply (IH (s,t1)); trivial.
    apply size2_lex1; left; trivial.
    simpl; apply List_eq.
    transitivity t1; trivial.
    symmetry; trivial.
    apply IHl1; trivial.
    intros y H; apply IH.
    refine (o_size2_trans _ _ _ H _).
    apply size2_lex1_bis.
    intros s' s'_in_l2; apply ll_lt_s.
    rewrite (@mem_mem s' l1 l2); trivial.
    (* 1/3 equivalence with Lex top symbol,  Top_eq_mul *)
    rewrite Stat in Stat_g; discriminate.
    (* 1/2 equivalence with Mul top symbol *)
    inversion t_lt_s as  [f l t'' t' t'_mem_l t''_le_t'
      | f f' l l' g_prec_f l'_lt_s
      | f' f l l' Stat_g Stat' f_stat_g L ll1_lt_l ll_lt_s
      | f' f l l' Stat_g Stat' f_stat_g ll1_lt_l ]; subst.
    (* 1/5 equivalence with Mul top symbol, Subterm *)
    destruct t''_le_t' as [t'' t' t''_eq_t' | t'' t' t''_lt_t'];
      apply Subterm with t'; trivial.
    apply Equiv.
    transitivity t''; trivial.
    symmetry; trivial.
    apply Lt.
    apply (IH (t',t'')); trivial.
    apply size2_lex1_mem; trivial.
    (* 1/4 equivalence with Mul top symbol, Top_gt *)
    apply Top_gt; trivial.
    apply prec_eq_prec2 with g; trivial.
    intros s' s'_mem_l2; apply l'_lt_s.
    rewrite (mem_permut0_mem equiv_equiv s' P1); trivial.
    (* 1/3 equivalence with Mul top symbol, Top_eq_lex *)
    rewrite Stat in Stat_g; discriminate.
    (* 1/3 equivalence with Mul top symbol, Top_eq_mul *)
    apply Top_eq_mul; trivial.
    apply prec_eq_transitive with g. apply prec_eq_sym; trivial. trivial.
    inversion ll1_lt_l as [a lg ls lc l' l'' Q1 Q2 ls_lt_alg]; subst.
    apply (@List_mul bb a lg ls lc); trivial. 
    apply permut0_trans with l1.
    exact equiv_equiv.
    apply (permut0_sym equiv_equiv). assumption. assumption.
    intros t t' t_eq_t' s; split.
    apply (H (s,t)); trivial.
    apply (H (s,t')); trivial.
    apply (Relation_Definitions.equiv_sym _ _ equiv_equiv); trivial.
  Qed.

  (* The proof of [rpo_mul_rest_trans_clos] used in the proof of
     [wf_rpo_mul_rest]. *)
  
  (** The plain multiset extension is in the transitive closure of
     the finer grain extension. *)
  
  Lemma rpo_mul_rest_trans_clos :
    forall bb, inclusion (rpo_mul_rest bb) (clos_trans (rpo_mul_step_rest bb)).

  Proof.
    intro bb; unfold inclusion; intros l' l H; 
      inversion H as [k k' Acc_l Acc_l' H' H1 H2 ]; subst.
    inversion H' as [a lg ls lc k k' P' P1 ls_lt_alg]; subst.
    generalize l' l a ls lc P' P1 ls_lt_alg Acc_l Acc_l'; 
      clear l' l a ls lc P' P1 ls_lt_alg H Acc_l Acc_l' H';
        induction lg as [ | g lg]; intros l' l a ls lc P' P1 ls_lt_alg Acc_l Acc_l'.
    apply Relation_Operators.t_step; apply Rpo_mul_step_rest; trivial;
      apply (@List_mul_step bb a ls lc); trivial.
    intros b b_in_ls; destruct (ls_lt_alg b b_in_ls) as
      [a' [[a'_eq_a | a'_in_nil] b_lt_a']].
    rewrite <- (equiv_rpo_equiv_1 _ a'_eq_a); trivial.
    contradiction.
    assert (H: exists ls1, exists ls2, 
      permut0 equiv ls (ls1 ++ ls2) /\
      (forall b, mem equiv b ls1 -> rpo bb b g) /\
      (forall b, mem equiv b ls2 -> exists a', mem equiv a' (a :: lg) /\ rpo bb b a')).
    clear P'; induction ls as [ | s ls].
    exists (nil : list term); exists (nil : list term); intuition. reflexivity.
    destruct IHls as [ls1 [ls2 [P' [ls1_lt_g ls2_lt_alg]]]].
    intros b b_in_ls; apply ls_lt_alg; right; trivial.
    destruct (ls_lt_alg s) as [a' [[a'_eq_a | [a'_eq_g | a'_in_lg]] b_lt_a']].
    left; reflexivity.
    exists ls1; exists (s :: ls2); repeat split; trivial.
    rewrite <- permut0_cons_inside; trivial. apply equiv_equiv.
    reflexivity.
    intros b [b_eq_s | b_in_ls2].
    exists a; split.
    left; reflexivity.
    rewrite (equiv_rpo_equiv_2 _ b_eq_s).
    rewrite <- (equiv_rpo_equiv_1 _ a'_eq_a); trivial.
    apply ls2_lt_alg; trivial.
    exists (s :: ls1); exists ls2; repeat split; trivial.
    simpl; rewrite <- permut0_cons; trivial. apply equiv_equiv.
    reflexivity.
    intros b [b_eq_s | b_in_ls1].
    rewrite (equiv_rpo_equiv_2 _ b_eq_s).
    rewrite <- (equiv_rpo_equiv_1 _ a'_eq_g); trivial.
    apply ls1_lt_g; trivial.
    exists ls1; exists (s :: ls2); repeat split; trivial.
    rewrite <- permut0_cons_inside; trivial. apply equiv_equiv.
    reflexivity.
    intros b [b_eq_s | b_in_ls2].
    exists a'; split.
    right; trivial.
    rewrite (equiv_rpo_equiv_2 _ b_eq_s); trivial.
    apply ls2_lt_alg; trivial.
    destruct H as [ls1 [ls2 [Pls [ls1_lt_g ls2_lt_alg]]]].
    apply Relation_Operators.t_trans with (g :: ls2 ++ lc).
    apply Relation_Operators.t_step; apply Rpo_mul_step_rest; trivial.
    simpl; intros s [g_eq_s | s_mem_ls2lc].
    apply Acc_l.
    rewrite P1; right; left; trivial.
    apply Acc_l'.
    rewrite P'; rewrite <- mem_or_app.
    rewrite <- mem_or_app in s_mem_ls2lc.
    destruct s_mem_ls2lc as [s_mem_ls2 | s_mem_lc].
    left; rewrite Pls; rewrite <- mem_or_app; right; trivial.
    right; trivial.
    apply (@List_mul_step bb g ls1 (ls2 ++ lc)); reflexivity || auto.
    rewrite P'; rewrite Pls; rewrite ass_app; reflexivity || auto.
    apply (IHlg (g :: ls2 ++ lc) l a ls2 (g :: lc)); trivial.
    rewrite <- permut0_cons_inside; try reflexivity. apply equiv_equiv.
    rewrite P1.
    rewrite <- permut0_cons;[|apply equiv_equiv|
      apply (Relation_Definitions.equiv_refl _ _ equiv_equiv)]. 
    simpl; rewrite <- permut0_cons_inside;
      [reflexivity|apply equiv_equiv|
        apply (Relation_Definitions.equiv_refl _ _ equiv_equiv)].
    simpl; intros s [g_eq_s | s_mem_ls2lc].
    apply Acc_l.
    rewrite P1; right; left; trivial.
    apply Acc_l'.
    rewrite P'; rewrite <- mem_or_app.
    rewrite <- mem_or_app in s_mem_ls2lc.
    destruct s_mem_ls2lc as [s_mem_ls2 | s_mem_lc].
    left; rewrite Pls; rewrite <- mem_or_app; right; trivial.
    right; trivial.
  Qed.

  (* The proof of [two_cases_rpo] used in the proof
     [wf_rpo_mul_rest]. *)

  (** Splitting in two disjoint cases. *)
  
  Lemma two_cases_rpo :
    forall bb a m n, 
      rpo_mul_step bb n (a :: m) ->
      (exists a', exists n', equiv a a' /\ permut0 equiv n (a' :: n') /\ 
        rpo_mul_step bb n' m) \/
      (exists ls, (forall b, mem equiv b ls -> rpo bb b a) /\ permut0 equiv n (ls ++ m)).

  Proof.
    intros bb b m n M; inversion M as [a ls lc l l' P' P1 ls_lt_a]; subst.
    assert (b_mem_a_lc : mem equiv b (a :: lc)).
    rewrite <- (mem_permut0_mem equiv_equiv b P1); left; reflexivity.
    simpl in b_mem_a_lc; destruct b_mem_a_lc as [b_eq_a | b_mem_lc].
    right; exists ls; repeat split; trivial.
    intros c c_mem_ls; rewrite (equiv_rpo_equiv_1 _ b_eq_a).
    apply ls_lt_a; trivial.
    rewrite P'; rewrite <- permut_app1.
    rewrite <- permut0_cons in P1;  try (symmetry; trivial). apply equiv_equiv.
    symmetry;trivial.
    apply equiv_equiv.
    destruct (mem_split_set _ _ equiv_bool_ok _ _ b_mem_lc) as [b' [lc1 [lc2 [b_eq_b' [H _]]]]];
      simpl in b_eq_b'; simpl in H.
    left; exists b'; exists (ls ++ (lc1 ++ lc2)); repeat split; trivial.
    rewrite P'; subst lc.
    rewrite ass_app; apply permut0_sym. apply equiv_equiv.
    rewrite <- permut0_cons_inside;
      [|apply equiv_equiv|apply (Relation_Definitions.equiv_refl _ _ equiv_equiv)]. 
    rewrite ass_app; reflexivity.
    apply (@List_mul_step bb a ls (lc1 ++ lc2)); try reflexivity.
    rewrite app_comm_cons.
    rewrite (@permut0_cons_inside _ _ equiv_equiv _ _ m (a :: lc1) lc2 b_eq_b').
    rewrite P1.
    simpl; subst lc; reflexivity.
    auto.
  Qed.

  (* The proof of [list_permut_map_acc] used in the proof of
     [wf_rpo_mul_rest]. *)

  Lemma list_permut_map_acc :
    forall bb l l', permut0 equiv l l' ->
      Acc (rpo_mul_step_rest bb) l ->  Acc (rpo_mul_step_rest bb) l'.

  Proof.
    intros bb l l' P1 A1; apply Acc_intro; intros l'' M2.
    inversion A1 as [H]; apply H; 
      inversion M2 as [k' k'' Acc_l' Acc_l'' H']; subst.
    inversion H' as [a ls lc k' k'' P'' P' ls_lt_a]; subst.
    apply Rpo_mul_step_rest; trivial.
    intros s s_in_l; apply Acc_l'; rewrite <- (mem_permut0_mem equiv_equiv s P1); trivial.
    apply (@List_mul_step bb a ls lc); trivial;
      apply permut0_trans with l'; trivial. apply equiv_equiv.
  Qed.

  (** Multiset extension of rpo on accessible terms lists is well-founded. *)

  (* The proof of [wf_rpo_mul_rest] used in the proof of [wf_rpo_rest]. *)

  Lemma wf_rpo_mul_rest : forall bb, well_founded (rpo_mul_rest bb).

  Proof.     
    intro bb; apply wf_incl with (clos_trans (rpo_mul_step_rest bb)).
    unfold inclusion; apply rpo_mul_rest_trans_clos.
    apply wf_clos_trans.
    unfold well_founded; intro l; induction l as [ | s l]. 
      (* 1/2 l = nil *)
    apply Acc_intro; intros m H; inversion H as [l l' Acc_l Acc_l' H']; subst;
      inversion H' as [a ls lc l l'  P1 P']; subst.
    assert (L := permut_length P'); discriminate.
      (* 1/1 induction step *)
    assert (Acc (rpo bb) s -> Acc (rpo_mul_step_rest bb) (s :: l)).
    intro Acc_s; generalize l IHl; clear l IHl; 
      pattern s; apply Acc_ind with term (rpo bb); trivial; clear s Acc_s.
    intros s Acc_s IHs l Acc_l; pattern l; 
      apply Acc_ind with (list term) (rpo_mul_step_rest bb); trivial; clear l Acc_l.
    intros l Acc_l IHl; apply Acc_intro.
    intros l' H; inversion H as [s_k k' Acc_s_l Acc_l' H']; subst.
    destruct (@two_cases_rpo bb s l l' H') as [[s' [n' [s_eq_s' [P1 H'']]]] | [ls [ls_lt_s P1]]].
      (* 1/3 First case *)
    apply (@list_permut_map_acc bb (s :: n')).
    rewrite P1; rewrite <- permut0_cons; reflexivity || apply equiv_equiv || auto. symmetry;assumption.
    apply Acc_intro; intros l'' l''_lt_s'_n; apply Acc_inv with (s :: n').
    apply IHl; apply Rpo_mul_step_rest; trivial.
    intros; apply Acc_s_l; right; trivial.
    intros s'' s''_in_n'; apply Acc_l'; rewrite (mem_permut0_mem equiv_equiv s'' P1); right; trivial.
    trivial.
      (* 1/2 Second case *)
    apply (@list_permut_map_acc bb (ls ++ l)).
    apply permut0_sym; trivial. apply equiv_equiv.
    clear P1; induction ls as [ | b ls].
    simpl; apply Acc_intro; trivial.
    simpl; apply IHs.
    apply ls_lt_s; left; reflexivity.
    apply IHls; intros; apply ls_lt_s; right; trivial.
    apply Acc_intro.
    intros l' H'.
    apply Acc_inv with (s :: l); trivial.
    inversion H' as [k k' Acc_s_l Acc_l']; subst;
      apply H; apply Acc_s_l; left; reflexivity.
  Qed.

  (* The proof of [wf_rpo_rest] used in the proof of [acc_build]. *)

  Lemma wf_rpo_rest : well_founded (prec P) -> forall bb, well_founded (rpo_rest bb).
  Proof.
    intros wf_prec bb; unfold well_founded; intros [f l]; generalize l; clear l; 
      pattern f; apply (well_founded_induction_type wf_prec); clear f.
    intros f IHf l; assert (Sf : forall f', f' = f -> status P f' = status P f).
    intros; subst; trivial.
    destruct (status P f); generalize (Sf _ (refl_equal _)); clear Sf; intro Sf.
    pattern l; apply (well_founded_induction_type (wf_rpo_lex_rest bb bb)); clear l.
    intros l IHl; apply Acc_intro; intros [g l'] H. 
    inversion H as [ f' g' k k' g_prec_f Acc_l Acc_l' 
      | f' g' k k' Sf' Sg' eq_f'_g' L H' Acc_l Acc_l'
      | f' g' k k' Sf' Sg' eq_f'_g' H' Acc_l Acc_l' ]; subst.
    apply IHf; trivial.
    apply rpo_rest_prec_eq with f. apply prec_eq_sym; trivial.
    apply rpo_rest_prec_eq with f. apply prec_eq_refl.
    apply IHl; apply Rpo_lex_rest; trivial.
    rewrite Sf in Sg'; discriminate.
    pattern l; apply (well_founded_induction_type (wf_rpo_mul_rest bb)); clear l.
    intros l IHl; apply Acc_intro; intros [g l'] H; 
      inversion H as [ f' g' k k' g_prec_f Acc_l Acc_l' 
        | f' k k' Sf' L H' Acc_l Acc_l'
        | f' k k' Sf' H' Acc_l Acc_l' ]; subst.
    apply IHf; trivial.
    absurd (Lex = Mul); [discriminate | apply trans_eq with (status P f); auto].
    apply rpo_rest_prec_eq with f. apply prec_eq_sym; trivial.
    apply IHl; apply Rpo_mul_rest; trivial.
  Qed.

  (* Definition of [size3] used in the definition of [o_size3]. *)

  Definition size3 s := match s with (s1,s2) => (@size s1, @size2 s2) end.

  (* The definition of [o_size3] used in the proof of [wf_size3]. *)

  Definition o_size3 s t := lex var_eq_bool lt (lex var_eq_bool lt lt) (size3 s) (size3 t).

  (* The proof of [wf_size3] used in the proof of [rpo_trans]. *)
  Lemma wf_size3 : well_founded o_size3.
  Proof.
    refine (wf_inverse_image _ _ 
      (lex  var_eq_bool lt (lex var_eq_bool lt lt)) size3 _).
    apply wf_lex; 
      [ exact var_eq_bool_ok
        | apply lt_wf 
        | apply wf_lex; [ exact var_eq_bool_ok | apply lt_wf | apply lt_wf ]].
  Defined.

  (* The proof of [size3_lex1] used in the proof of [size3_lex1_mem]. *)

  Lemma size3_lex1 : 
    forall s f l t1 u1 t2 u2, In s l -> o_size3 (s,(t1,u1)) (Term f l,(t2,u2)).
  Proof.
    intros s f l t1 u1 t2 u2 s_in_l; unfold o_size3, size3, size2, lex.
    generalize (var_eq_bool_ok (size s) (size (Term f l)));
      case (var_eq_bool (size s) (size (Term f l))); [intro s_eq_t | intro s_lt_t].
    absurd (size (Term f l) < size (Term f l)); auto with arith;
      generalize (size_direct_subterm s (Term f l) s_in_l); rewrite s_eq_t; trivial.
    apply (size_direct_subterm s (Term f l) s_in_l).
  Defined.

  (* The proof of [size3_lex1_mem] used in the proof of [rpo_trans]. *)

  Lemma size3_lex1_mem :
    forall s f l t1 u1 t2 u2, mem equiv s l -> o_size3 (s,(t1,u1)) (Term f l,(t2,u2)).

  Proof.
    intros s f l t1 u1 t2 u2 s_mem_l;
      destruct (mem_split_set _ _ equiv_bool_ok _ _ s_mem_l)
        as [s' [l1 [l2 [s_eq_s' [H _]]]]].
    simpl in s_eq_s'; simpl in H.
    unfold o_size3, size3; rewrite (equiv_same_size s_eq_s').
    apply (size3_lex1 s' f l t1 u1 t2 u2).
    subst l; apply in_or_app; right; left; trivial.
  Qed.

  (* The proof of [size3_lex2] used in the proof of [size3_lex2_mem]. *)

  Lemma size3_lex2 :
    forall t f l s u1 u2, In t l -> o_size3 (s,(t,u1)) (s,(Term f l, u2)).

  Proof.
    intros t f l s u1 u2 t_in_l;
      unfold o_size3, size3, size2, lex.
    generalize (var_eq_bool_ok (size s) (size s));
      case (var_eq_bool (size s) (size s)); [intros _ | intro s_diff_s].
    generalize (var_eq_bool_ok (size t) (size (Term f l)));
      case (var_eq_bool (size t) (size (Term f l))); [intro t_eq_fl | intro t_lt_fl].
    absurd (size (Term f l) < size (Term f l)); auto with arith;
      generalize (size_direct_subterm t (Term f l) t_in_l); rewrite t_eq_fl; trivial.
    apply (size_direct_subterm t (Term f l) t_in_l).
    apply False_rect; apply s_diff_s; reflexivity.
  Defined.

  (* The proof of [size3_lex2_mem] used in the proof of [rpo_trans]. *)

  Lemma size3_lex2_mem :
    forall t f l s u1 u2, mem equiv t l -> o_size3 (s,(t,u1)) (s,(Term f l, u2)).
  Proof.
    intros t f l s u1 u2 t_mem_l;
      destruct (mem_split_set _ _ equiv_bool_ok _ _ t_mem_l) as [t' [l1 [l2 [t_eq_t' [H _]]]]].
    simpl in t_eq_t'; simpl in H.
    unfold o_size3, size3, size2; rewrite (equiv_same_size t_eq_t').
    apply (size3_lex2 t' f l s u1 u2).
    subst l; apply in_or_app; right; left; trivial.
  Qed.

  (* The proof of [size3_lex3] used in the proof of [rpo_trans]. *)

  Lemma size3_lex3 :
    forall u f l s t, In u l -> o_size3 (s,(t,u)) (s,(t,Term f l)).

  Proof.
    intros u f l s t u_in_l;
      unfold o_size3, size3, size2, lex;
        generalize (var_eq_bool_ok (size s) (size s));
          case (var_eq_bool (size s) (size s)); [intros _ | intro s_diff_s].
    generalize (var_eq_bool_ok (size t) (size t));
      case (var_eq_bool (size t) (size t)); [intros _ | intro t_diff_t].
    apply (size_direct_subterm u (Term f l) u_in_l).
    apply False_rect; apply t_diff_t; reflexivity.
    apply False_rect; apply s_diff_s; reflexivity.
  Defined.

  (* The proof of [rpo_subterm_equiv] used in the proof of
     [rpo_subterm]. *)

  (** ** rpo is a preorder, and its reflexive closure is an ordering. *)
  
  Lemma rpo_subterm_equiv :
    forall bb s t, equiv t s -> forall tj, direct_subterm tj t -> rpo bb tj s.

  Proof.
    intros bb s [ | f l] fl_eq_s tj; simpl. 
    contradiction.
    intro tj_in_l; rewrite <- (equiv_rpo_equiv_1 _  fl_eq_s).
    apply Subterm with tj.
    apply in_impl_mem; trivial.
    intros; apply Eq.
    intros; apply Equiv; apply Eq.
  Qed.

  (* The proof of [rpo_subterm] used in the proof of [rpo_subterm_mem] *)

  Lemma rpo_subterm :
    forall bb s t, rpo bb t s -> forall tj, direct_subterm tj t -> rpo bb tj s.

  Proof.
    intros bb s t; 
      cut (forall p : term * term,
        match p with
          | (s,t) => rpo bb t s -> forall tj, direct_subterm tj t -> rpo bb tj s
        end).
    intro H; apply (H (s,t)).
    clear s t; intro p; pattern p; refine (well_founded_ind wf_size2 _ _ _); clear p.
    intros [s [ v | f l]] IH t_lt_s tj tj_in_l; simpl in tj_in_l; [ contradiction | idtac].
    inversion t_lt_s as [ f' l' t' s' s'_in_l' t'_le_s'
      | f' g' k k' g'_prec_f' H
      | f' g k k' Sf' Sg f_eq_g L k'_lt_k H
      | f' g k k' Sf' Sg f_eq_g k'_lt_k ].
    (* 1/4 Subterm *)
    subst; inversion t'_le_s' as [ t'' s'' t'_eq_s' | t'' s'' t'_lt_s']; clear t'_le_s'; subst.
    apply (@Subterm bb f' l' tj s'); trivial;
      apply Lt; apply rpo_subterm_equiv with (Term f l); trivial.
    apply (@Subterm bb f' l' tj s'); trivial.
    apply Lt; apply (IH (s', Term f l)); trivial.
    apply size2_lex1_mem; trivial.
    (* 1/3 Top_gt *)
    subst; apply H2; apply in_impl_mem; trivial.
    intros; apply Eq.
    (* 1/2 Top_eq_lex *)
    subst; apply H2; apply in_impl_mem; trivial.
    intros; apply Eq.
    (* Top_eq_mul *)
    inversion k'_lt_k as [a lg ls lc l1 l2 P1 P2 H]; subst.
    assert (tj_mem_l := in_impl_mem equiv Eq tj l tj_in_l).
    rewrite (mem_permut0_mem equiv_equiv tj P1) in tj_mem_l.
    rewrite <- mem_or_app in tj_mem_l.
    destruct tj_mem_l as [tj_mem_ls | tj_mem_llc].
    destruct (H _ tj_mem_ls) as [a' [a'_mem_a_lg tj_lt_a']].
    apply (@Subterm bb g k tj a').
    rewrite (mem_permut0_mem equiv_equiv a' P2); rewrite app_comm_cons.
    rewrite <- mem_or_app; left; trivial.
    apply Lt; trivial.
    apply (@Subterm bb g k tj tj).
    rewrite (mem_permut0_mem equiv_equiv tj P2).
    right; rewrite <- mem_or_app; right; trivial.
    apply Equiv; apply Eq.
  Qed.

  (* The proof of [rpo_subterm_mem] used in the proof of [size3_lex3_mem]. *)

  Lemma rpo_subterm_mem :
    forall bb s f l, rpo bb (Term f l) s -> forall tj, mem equiv tj l -> rpo bb tj s.

  Proof.
    intros bb s f l fl_lt_s tj tj_mem_l.
    destruct (mem_split_set _ _ equiv_bool_ok _ _ tj_mem_l) as [tj' [l1 [l2 [tj_eq_tj' [H _]]]]].
    simpl in tj_eq_tj'; simpl in H.
    rewrite (equiv_rpo_equiv_2  _ tj_eq_tj').
    apply rpo_subterm with (Term f l); trivial.
    subst l; simpl; apply in_or_app; right; left; trivial.
  Qed.

  (* The proof of [size3_lex3_mem] used in the proof of [rpo_trans]. *)

  Lemma size3_lex3_mem :
    forall u f l s t, mem equiv u l -> o_size3 (s,(t,u)) (s,(t,Term f l)).
  Proof.
    intros u f l s t u_mem_l;
      destruct (mem_split_set _ _ equiv_bool_ok _ _ u_mem_l) as [u' [l1 [l2 [u_eq_u' [H _]]]]].
    simpl in u_eq_u'; simpl in H.
    unfold o_size3, size3, size2; rewrite (equiv_same_size u_eq_u').
    apply (size3_lex3 u' f l s t).
    subst l; apply in_or_app; right; left; trivial.
  Qed.

  (* The proof of [size3_lex1_bis] used in the proof [o_size3_trans]. *)

  Lemma size3_lex1_bis : 
    forall a f l t1 u1 t2 u2, o_size3 (Term f l,(t1,u1)) (Term f (a::l),(t2,u2)).

  Proof.
    intros a f l t1 u1 t2 u2; unfold o_size3, size3, lex;
      generalize (var_eq_bool_ok (size (Term f l)) (size (Term f (a :: l)))); 
        case (var_eq_bool (size (Term f l)) (size (Term f (a :: l))));
          [intro s_eq_t | intro s_lt_t].
    do 2 rewrite size_unfold in s_eq_t; injection s_eq_t; clear s_eq_t; intro s_eq_t;
      absurd (list_size (@size ) l < list_size (@size ) l); auto with arith;
        generalize (plus_le_compat_r _ _ (list_size (@size ) l) (size_ge_one a));
          rewrite <- s_eq_t; trivial.
    do 2 rewrite size_unfold;
      simpl; apply lt_n_S; apply lt_le_trans with (1 + list_size (@size ) l);
        auto with arith; 
          apply plus_le_compat_r; apply size_ge_one.
  Defined.

  (* The proof of [o_size3_trans] used in the proof of [rpo_trans]. *)

  Lemma o_size3_trans : transitive o_size3.

  Proof.
    intros [x1 x2] [y1 y2] [z1 z2].
    apply (@lex_trans _ _ var_eq_bool lt (lex var_eq_bool lt lt) var_eq_bool_ok).
    intros n m n_lt_m m_lt_n;
      generalize (lt_asym n m n_lt_m m_lt_n); contradiction.
    intros n1 n2 n3; apply lt_trans.
    apply lex_trans.
    exact var_eq_bool_ok.
    intros n m n_lt_m m_lt_n;
      generalize (lt_asym n m n_lt_m m_lt_n); contradiction.
    intros n1 n2 n3; apply lt_trans.
    intros n1 n2 n3; apply lt_trans.
  Qed.

  (* The proof of [rpo_trans] used in the proof of [acc_build] *)

  Lemma rpo_trans : forall bb u t s, rpo bb u t -> rpo bb t s ->  rpo bb u s.

  Proof.
    intros bb u t s;
      cut (forall triple : term * (term * term),
        match triple with
          | (s,(t,u)) => rpo bb t s -> rpo bb u t -> rpo bb u s
        end).
    intros H u_lt_t t_lt_s; apply (H (s,(t,u))); trivial.
    clear s t u; intro triple; pattern triple; 
      refine (well_founded_ind wf_size3 _ _ triple); clear triple.
    intros [[v | f l] [t u]] IH.
    (* 1/2 Variable case *)
    intros t_lt_v; inversion t_lt_v.
    (* 1/1 Compound case *)
    intros t_lt_fl u_lt_t;
      inversion t_lt_fl as [ f'' l' s' t' t'_in_l' t_le_t'
        | f'' f' k'' l' f'_prec_f H''
        | f'' g'' k'' l' Sf Sg f''_eq_g'' L l'_lt_l H H1 H2 
        | f'' g'' k'' l' Sf Sg f''_eq_g'' l'_lt_l ]; subst.
    (* 1/4 Subterm *)
    apply Subterm with t'; trivial; apply Lt;
      inversion t_le_t' as [t'' t''' t_eq_t' | t'' t''' t_lt_t']; subst.
    rewrite <- (equiv_rpo_equiv_1  _ t_eq_t'); trivial.
    apply (IH (t',(t,u))); trivial.
    apply size3_lex1_mem; trivial.
    (* 1/3 Top_gt *)
    inversion u_lt_t as [ f'' l'' s' t' t'_in_l' u_le_t'
      | g'' f'' k'' l'' f''_prec_f'' H'''
      | g'' g' k'' l'' Sf' Sf'' g''_eq_g' L l''_lt_l' H H1 H2 
      | g'' g' k'' l'' Sf' Sf'' g''_eq_g' l''_lt_l' ]; subst.
    (* 1/6 Top_gt, Subterm *)
    inversion u_le_t' as [t'' t''' u_eq_t' | t'' t''' u_lt_t']; subst.
    rewrite (equiv_rpo_equiv_2 _ u_eq_t'); trivial; apply H''; trivial.
    apply (IH (Term f l,(t',u))); trivial.
    apply size3_lex2_mem; trivial.
    apply H''; trivial.
    (* 1/5 Top_gt, Top_gt *)
    apply Top_gt.
    apply prec_transitive with f'; trivial.
    intros u u_in_l''; apply (IH (Term f l, (Term f' l', u))); trivial.
    apply size3_lex3_mem; trivial.
    apply H'''; trivial.
    (* 1/4 Top_gt, Top_eq_lex *)
    apply Top_gt. apply prec_eq_prec2 with f'. trivial.
    apply prec_eq_sym. trivial.
    intros u u_in_l''; apply (IH (Term f l, (Term f' l', u))); trivial.
    apply size3_lex3_mem; trivial.
    apply H0; trivial.
    (* 1/3 Top_gt, Top_eq_mul *)
    apply Top_gt. apply prec_eq_prec2 with f'. trivial.
    apply prec_eq_sym. trivial.
    intros u u_in_l''. apply (IH (Term f l, (Term f' l', u))); trivial.
    apply size3_lex3_mem; trivial.
    apply rpo_subterm_mem with g'' l''; trivial.
    (* 1/2 Top_eq_lex *)
    inversion u_lt_t as [ f''' l'' s' t' t'_in_l' u_le_t'
      | g'' f''' k'' l'' f''_prec_f' H'''
      | g'' f''' k'' l'' Sf' Sg' f_eq_g' L' l''_lt_l' H H1 H2 
      | g'' f''' k'' l'' Sf' Sg' f_eq_g' l''_lt_l' ]; subst.
    (* 1/5 Top_eq_lex, Subterm *)
    inversion u_le_t' as [t'' t''' u_eq_t' | t'' t''' u_lt_t']; subst.
    rewrite (equiv_rpo_equiv_2 _ u_eq_t').
    apply rpo_subterm_mem with f'' l'; trivial.
    apply (IH (Term f l, (t', u))); trivial.
    apply size3_lex2_mem; trivial.
    apply H0; trivial.
    (* 1/4 Top_eq_lex, Top_gt *)
    apply Top_gt. apply prec_eq_prec1 with f''; trivial.
    intros u u_in_l''. apply (IH (Term f l, (Term f'' l', u))). 
    apply size3_lex3_mem. trivial. trivial. 
    apply H'''. trivial. 
    (* 1/3 Top_eq_lex, Top_eq_lex *)
    apply Top_eq_lex; trivial.
    apply prec_eq_transitive with f''. trivial. trivial.
    destruct L as [L | [L1 L2]].
    rewrite L; assumption.
    destruct L' as [L' | [L1' L2']].
    rewrite <- L'; right; split; assumption.
    right; split; assumption.
    generalize l' l'' l'_lt_l l''_lt_l' IH;
      clear l' l'' l'_lt_l l''_lt_l' IH H0 H3 t_lt_fl u_lt_t L L';
        induction l as [ | s l]; intros l' l'' l'_lt_l l''_lt_l' IH.
    inversion l'_lt_l.
    inversion l'_lt_l as [ t s' k' k t_lt_s 
      | t s' k' k t_eq_s k'_lt_k | t k];
    inversion l''_lt_l' as [ u t' k'' h' u_lt_t 
      | u t' k'' h' u_eq_t k''_lt_k' | u k1].
    subst; injection H3; intros; subst; apply List_gt.
    apply (IH (s,(t,u))); trivial.
    apply size3_lex1; left; trivial.
    subst; injection H3; intros; subst; apply List_gt.
    rewrite (equiv_rpo_equiv_2 _ u_eq_t); trivial.
    apply List_nil.
    subst; injection H3; intros; subst; apply List_gt.
    rewrite <- (equiv_rpo_equiv_1 _ t_eq_s); trivial.
    subst; injection H3; intros; subst; apply List_eq.
    transitivity t; trivial.
    apply IHl with k'; trivial.
    intros; apply IH;
      apply o_size3_trans with (Term f l, (Term f k', Term f k'')); trivial.
    apply size3_lex1_bis.
    apply List_nil.
    subst; discriminate H3.
    subst; discriminate H3.
    subst; discriminate H3.
    intros u u_in_l''. apply (IH (Term f l, (Term f'' l', u))); trivial.
    apply size3_lex3_mem. trivial.
    apply H3; trivial.
    (* 1/2 Top_eq_lex, Top_eq_mul *)
    rewrite Sf in Sg'; discriminate.
    (* 1/1 Top_eq_mul *)
    inversion u_lt_t as [ f''' l'' s' t' t'_in_l' u_le_t'
      | g'' f''' k'' l'' f''_prec_f' H'''
      | g'' f''' k'' l'' Sf' Sf''' Seq_g''_f''' L l''_lt_l' H H1 H2 
      | g'' f''' k'' l'' Sf' Sf''' Seq_g''_f''' l''_lt_l' ]; subst.
    (* 1/4 Top_mul_lex, Subterm *)
    inversion u_le_t' as [t'' t''' u_eq_t' | t'' t''' u_lt_t']; subst.
    rewrite (equiv_rpo_equiv_2 _ u_eq_t').
    apply rpo_subterm_mem with f'' l'; trivial. 
    apply (IH (Term f l, (t', u))); trivial.
    apply size3_lex2_mem; trivial.
    apply rpo_subterm_mem with f'' l'; trivial.
    (* 1/3 Top_eq_mul, Top_gt *)
    apply Top_gt; trivial. apply prec_eq_prec1 with f''. trivial. trivial.
    intros u u_in_l''; apply (IH (Term f l, (Term f'' l', u))); trivial.
    apply size3_lex3_mem; trivial.
    apply H'''; trivial.
    (* 1/2 Top_eq_mul, Top_eq_lex *)
    rewrite Sf in Sf'''; discriminate.
    (* 1/1 Top_eq_mul, Top_eq_mul *)
    apply Top_eq_mul; trivial. apply prec_eq_transitive with f''. trivial. trivial. 
    destruct l'_lt_l as [a lg ls lc l l' P' P1 ls_lt_alg].
    destruct l''_lt_l' as [a' lg' ls' lc' l' l'' Q' Q ls'_lt_alg'].
    rewrite P' in Q; rewrite app_comm_cons in Q.
    destruct (@ac_syntactic _ _ equiv_equiv _ equiv_bool_ok _ _ _ _ Q) as 
      [k1 [k2 [k3 [k4 [P11 [P2 [P3 P4]]]]]]]. 
    apply (@List_mul bb a (lg ++ k2) (ls' ++ k3) k1).
    rewrite Q'.
    rewrite <- ass_app.
    rewrite <- permut_app1.
    rewrite list_permut0_app_app; trivial. apply equiv_equiv. apply equiv_equiv.
    rewrite P1.
    rewrite <- permut0_cons;[|apply equiv_equiv|
      apply (Relation_Definitions.equiv_refl _ _ equiv_equiv)].
    rewrite <- ass_app.
    rewrite <- permut_app1.
    rewrite list_permut0_app_app; trivial.  apply equiv_equiv. apply equiv_equiv.
    intros b b_mem_ls'_k3; rewrite <- mem_or_app in b_mem_ls'_k3.
    destruct b_mem_ls'_k3 as [b_mem_ls' | b_mem_k3].
    destruct (ls'_lt_alg'  _ b_mem_ls') as [a'' [a''_in_a'lg' b_lt_a'']].
    rewrite (mem_permut0_mem equiv_equiv a'' P4) in a''_in_a'lg'.
    rewrite <- mem_or_app in a''_in_a'lg'.
    destruct a''_in_a'lg' as [a''_mem_k2 | a''_mem_k4].
    exists a''; split; trivial.
    rewrite app_comm_cons; rewrite <- mem_or_app; right; trivial.
    destruct (ls_lt_alg a'') as [a3 [a3_in_alg a''_lt_a3]].
    rewrite (mem_permut0_mem equiv_equiv a'' P2).
    rewrite <- mem_or_app; right; trivial.
    exists a3; split.
    rewrite app_comm_cons; rewrite <- mem_or_app; left; trivial.
    apply (IH (a3,(a'',b))); trivial.
    apply size3_lex1_mem.
    rewrite (mem_permut0_mem equiv_equiv a3 P1).
    rewrite app_comm_cons; rewrite <- mem_or_app; left; trivial.
    destruct (ls_lt_alg b) as [a'' [a''_in_alg b_lt_a'']].
    rewrite (mem_permut0_mem equiv_equiv b P2); rewrite <- mem_or_app; left; trivial.
    exists a''; split; trivial.
    rewrite app_comm_cons; rewrite <- mem_or_app; left; trivial.
  Qed.

  (* The proof of [acc_build] used in the proof of [wf_rpo]. *)

  Lemma acc_build :
    well_founded (prec P) -> forall bb f_l,
      match f_l with (f, l) => 
        (forall t, mem equiv t l -> Acc (rpo bb) t) ->  Acc (rpo bb) (Term f l)
      end.

  Proof.
    intros wf_prec bb f_l; pattern f_l;
      apply (well_founded_induction_type (wf_rpo_rest wf_prec bb)); clear f_l.
    intros [f l] IH Acc_l; apply Acc_intro;
      intros s; pattern s; apply term_rec3_mem; clear s.
    intros v _; apply Acc_intro.
    intros t t_lt_v; inversion t_lt_v.
    intros g k IHl gk_lt_fl;
      inversion gk_lt_fl as [ f' l' s' t t_in_l H' 
        | f' g' k' l' g_prec_f 
        | f' g' k' l' Sf Sg f_eq_g L H' H''
        | f' g' k' l' Sf Sg f_eq_g H']; subst.
    (* 1/4 Subterm case *)
    assert (Acc_t := Acc_l _ t_in_l).
    subst; inversion H' as [s' t' s_eq_t | s' t' s_lt_t ]; 
      subst s' t'; [idtac | apply Acc_inv with t; trivial ].
    apply Acc_intro; intro u.
    rewrite (@equiv_rpo_equiv_1 _ (Term g k) t); trivial;
      intro; apply Acc_inv with t; trivial.
    (* 1/3 Top gt *)
    assert (Acc_k : forall s, mem equiv s k -> Acc (rpo bb) s).
    intros s s_mem_k; apply IHl; trivial.
    apply H0; trivial.
    apply (IH (g,k)); trivial.
    apply Top_gt_rest; trivial.
    (* 1/2 Top_eq_lex *)
    assert (Acc_k : forall s, mem equiv s k -> Acc (rpo bb) s).
    intros s s_mem_k; apply IHl; trivial.
    apply H''; trivial.
    apply (IH (g,k)); trivial.
    apply Top_eq_lex_rest; trivial.
    (* 1/1 Top_eq_mul *)
    assert (Acc_k : forall s, mem equiv s k -> Acc (rpo bb) s).
    intros s s_mem_k; apply IHl; trivial.
    apply rpo_trans with (Term g k); trivial; apply Subterm with s; trivial; 
      apply Equiv; apply Eq.
    apply (IH (g,k)); trivial.
    apply Top_eq_mul_rest; trivial.
  Qed.

  (** ** Main theorem: when the precedence is well-founded, so is the rpo. *)

  (* REMARK: this function will be use in Coccinelle2.v to proof the
  well-founded of [succ]. *)

  Lemma wf_rpo : well_founded (prec P) -> forall bb, well_founded (rpo bb).

  Proof.
    intros wf_prec bb;
      unfold well_founded; intro t; pattern t; apply term_rec3_mem; clear t.
    intro v; apply Acc_intro; intros s s_lt_t; inversion s_lt_t.
    intros f l Acc_l; apply (acc_build wf_prec bb (f,l)); trivial.
  Qed.

  (* The proof [size2_lex2] used in the proof of [size2_lex2_mem].*)

  Lemma size2_lex2 :
    forall t f l s, In t l -> o_size2 (s,t) (s, Term f l).

  Proof.
    intros t f l s t_in_l;
      unfold o_size2, size2, lex;
        generalize (var_eq_bool_ok (size s) (size s));
          case (var_eq_bool (size s) (size s)); [intros _ | intro s_diff_s].
    apply size_direct_subterm; trivial.
    apply False_rect; apply s_diff_s; reflexivity.
  Defined.

  (* The proof of [size2_lex2_mem] used in the proof of
     [rpo_subst]. *)

  Lemma size2_lex2_mem :
    forall t f l s, mem equiv t l -> o_size2 (s,t) (s, Term f l).
  Proof.
    intros t f l s t_mem_l;
      destruct (mem_split_set _ _ equiv_bool_ok _ _ t_mem_l) as
        [t' [l1 [l2 [t_eq_t' [H _]]]]].
    simpl in t_eq_t'; simpl in H.
    unfold o_size2, size2; rewrite (equiv_same_size t_eq_t').
    apply (size2_lex2 t' f l s).
    subst l; apply in_or_app; right; left; trivial.
  Qed.

  (* The proof of [equiv_subst] used to proof a lemma [rpo_subst]. *)

  Lemma equiv_subst :
    forall s t, equiv s t -> 
      forall sigma, equiv (apply_subst sigma s) (apply_subst sigma t).

  Proof.
    intros s t; generalize s; clear s.
    pattern t; apply term_rec3_mem; clear t.
    intros v s v_eq_s; inversion v_eq_s; subst; intro sigma; apply Eq.
    intros f l IHl s fl_eq_s sigma; 
      inversion fl_eq_s as [ s' 
        | f' g l1 l2 Sf Sg f'_eq_g l1_eq_l2
        | f' g l1 l2 Sf Sg f'_eq_g P1]; subst.
    (* 1/3 Syntactic equality *)
    apply Eq.
    (* 1/2 Lex top symbol *)
    simpl; apply Eq_lex; trivial.
    generalize l1 l1_eq_l2; clear fl_eq_s l1 l1_eq_l2; 
      induction l as [ | s l]; intros l1 l1_eq_l2;
        inversion l1_eq_l2 as [ | s1 s' l1' l' s1_eq_s' l1'_eq_l']; subst.
    simpl; apply Eq_list_nil.
    simpl; apply Eq_list_cons.
    apply IHl; trivial; left; reflexivity.
    apply IHl0; trivial.
    intros t t_in_l; apply IHl; right; trivial.
    (* 1/1 Mul top symbol *)
    simpl; apply Eq_mul; trivial.
    apply (permut_map (A := term) (B := term) (A' := term) (B' := term) (R := equiv)).
    intros a1 a2 a1_in_l1 _ a1_eq_a2; symmetry; apply IHl.
    rewrite <- (mem_permut0_mem equiv_equiv a1 P1).
    apply in_impl_mem; trivial.
    intros; apply Eq.
    symmetry; trivial.
    trivial.
  Qed.

  (* The proof of [rpo_subst] used in Coccinelle2.v at the lemma
     [sc_succ_rpo]. *)

  Lemma rpo_subst :
    forall bb s t, rpo bb s t -> 
      forall sigma, rpo bb (apply_subst sigma s) (apply_subst sigma t).

  Proof.
    intro bb.
    cut (forall p,
      match p with 
        (s,t) => rpo bb s t -> 
        forall sigma, rpo bb (apply_subst sigma s) (apply_subst sigma t)
      end).
    intros H s t s_lt_t sigma; apply (H (s,t)); trivial.
    intro p; pattern p; refine (well_founded_ind wf_size2 _ _ _); clear p.
    intros [s t] IH s_lt_t sigma.
    inversion s_lt_t as [ f l s' t' t'_mem_l R' 
      | f g l l' R' R'' 
      | f g l l' f_lex g_lex f_eq_g L Rlex R' H2 H3
      | f g l l' f_mul g_mul f_eq_g Rmul R' H2 ]; subst.
    (* 1/4 case Subterm *)
    simpl; apply Subterm with (apply_subst sigma t').
    destruct (mem_split_set _ _ equiv_bool_ok _ _ t'_mem_l) as
      [t'' [l1 [l2 [t'_eq_t'' [H _]]]]];
      simpl in t'_eq_t''; simpl in H; subst l.
    rewrite map_app; rewrite <- mem_or_app.
    right; left; apply equiv_subst; trivial.
    inversion R' as [ s' R'' | s' t'' R'' ]; subst. 
    apply Equiv; apply equiv_subst; trivial.
    apply Lt; apply (IH (s,t')); trivial.
    apply size2_lex2_mem; trivial.
    (* 1/3 case Top_gt *)
    simpl; apply Top_gt; trivial.
    intros s' s'_mem_l'_sigma; 
      destruct (mem_split_set _ _ equiv_bool_ok _ _ s'_mem_l'_sigma) as
        [s'' [l1 [l2 [s'_eq_s'' [H _]]]]];
        simpl in s'_eq_s''; simpl in H.
    rewrite (equiv_rpo_equiv_2 _ s'_eq_s'').
    assert (s''_in_l'_sigma : In s'' (map (apply_subst sigma) l')).
    rewrite H; apply in_or_app; right; left; trivial.
    rewrite in_map_iff in s''_in_l'_sigma.
    destruct s''_in_l'_sigma as [u [s_eq_u_sigma u_in_l']].
    subst s''; 
      replace (Term f (map (apply_subst sigma) l)) with 
        (apply_subst sigma (Term f l)); trivial.
    apply (IH (u, Term f l)).
    apply size2_lex1; trivial.
    apply rpo_trans with (Term g l'); trivial.
    apply Subterm with u.
    apply in_impl_mem; trivial.
    exact Eq.
    apply Equiv; apply Eq.
    (* 1/2 case Top_eq_lex *)
    simpl; apply Top_eq_lex; trivial.
    do 2 rewrite length_map; assumption.
    generalize l Rlex IH; clear l s_lt_t Rlex R' IH L;
      induction l' as [ | s' l' ]; intros l Rlex IH; 
        inversion Rlex as [s'' t' k k' s'_lt_t' L |
          s'' t' k k' s'_eq_t' k_lt_k' | ]; subst; simpl.
    apply List_nil.
    apply List_gt.
    apply (IH (s',t')); trivial.
    apply size2_lex1; left; trivial.
    apply List_eq.
    apply equiv_subst; trivial.
    apply IHl'; trivial.
    intros [s t] S s_lt_t tau; apply (IH (s,t)); trivial.
    apply o_size2_trans with (Term f l', Term f k'); trivial.
    apply size2_lex1_bis.
    intros s' s'_mem_l'_sigma; 
      destruct (mem_split_set _ _ equiv_bool_ok _ _ s'_mem_l'_sigma) as
        [s'' [l1 [l2 [s'_eq_s'' [H _]]]]];
        simpl in s'_eq_s''; simpl in H.
    rewrite (equiv_rpo_equiv_2 _ s'_eq_s'').
    assert (s''_in_l'_sigma : In s'' (map (apply_subst sigma) l')).
    rewrite H; apply in_or_app; right; left; trivial.
    rewrite in_map_iff in s''_in_l'_sigma.
    destruct s''_in_l'_sigma as [u [s_eq_u_sigma u_in_l']].
    subst s''; 
      replace (Term f (map (apply_subst sigma) l)) with 
        (apply_subst sigma (Term f l)); trivial.
    apply (IH (u, Term g l)).
    apply size2_lex1; trivial.
    apply rpo_trans with (Term f l'); trivial.
    apply Subterm with u.
    apply in_impl_mem; trivial.
    exact Eq.
    apply Equiv; apply Eq.
    (* 1/1 case Top_eq_mul *)
    simpl; apply Top_eq_mul; trivial;
      inversion Rmul as [ a lg ls lc l0 k0 Pk Pl ls_lt_alg]; subst.
    apply (@List_mul bb (apply_subst sigma a) (map (apply_subst sigma) lg)
      (map (apply_subst sigma) ls) (map (apply_subst sigma) lc)).
    rewrite <- map_app; apply permut_map with equiv; trivial.
    intros b b' _ _ b_eq_b'; apply equiv_subst; trivial.
    rewrite <- map_app.
    refine (@permut_map term term term term equiv 
      equiv (apply_subst sigma) _ _ (a :: lg ++ lc) _ _); trivial.
    intros b b' b_in_l _ b_eq_b'; apply equiv_subst; trivial.
    intros b b_mem_ls_sigma; 
      destruct (mem_split_set _ _ equiv_bool_ok _ _ b_mem_ls_sigma) as
        [b' [ls1 [ls2 [b_eq_b' [H _]]]]];
        simpl in b_eq_b'; simpl in H.
    assert (b'_in_ls_sigma : In b' (map (apply_subst sigma) ls)).
    rewrite H; apply in_or_app; right; left; trivial.
    rewrite in_map_iff in b'_in_ls_sigma.
    destruct b'_in_ls_sigma as [b'' [b''_sigma_eq_b' b''_in_ls]].
    destruct (ls_lt_alg b'') as [a' [a'_mem_alg b''_lt_a']].
    apply in_impl_mem; trivial.
    exact Eq.
    destruct (mem_split_set _ _ equiv_bool_ok _ _ a'_mem_alg) as
      [a'' [alg' [alg'' [a'_eq_a'' [H' _]]]]];
      simpl in a'_eq_a''; simpl in H'.
    exists (apply_subst sigma a''); split; trivial.
    apply in_impl_mem.
    exact Eq.
    rewrite (in_map_iff (apply_subst sigma) (a :: lg)).
    exists a''; split; trivial.
    rewrite H'; apply in_or_app; right; left; trivial.
    rewrite (equiv_rpo_equiv_2 _ b_eq_b').
    subst b'; apply (IH (b'',a'')).
    apply size2_lex1_mem.
    rewrite Pk; rewrite <- mem_or_app; left;
      apply in_impl_mem; trivial. 
    exact Eq.
    rewrite <- (equiv_rpo_equiv_1 _ a'_eq_a''); trivial.
  Qed.

  (* Define a record type of [rpo_inf] used in [empty_rpo_infos]. *)

  Record rpo_inf : Type := 
    { bb : nat;
      rpo_l : list (term*term);
      rpo_eq_l : list (term*term);
      equiv_l : list (term*term);
      rpo_l_valid : forall t t', In (t,t') rpo_l -> rpo bb t t';
      rpo_eq_valid : forall t t', In (t,t') rpo_eq_l -> rpo_eq bb t t';
      equiv_l_valid : forall t t', In (t,t') equiv_l -> equiv t t'
    }.

  (* Definition of [empty_rpo_infos] used in function [rpo_eval] to
     define [bsucc_rpo] in Coccinelle2.v *)

  Definition empty_rpo_infos : forall (n : nat), rpo_inf.

  Proof. 
    intro n;  constructor 1 with n (@nil (term*term)) (@nil (term*term))
      (@nil (term*term));simpl;tauto.
  Defined.

  (* Definition of [eq_tt_bool] used in the definition of
     [rpo_eval]. *)

  Notation t_eq_bool := (@t_eq_bool Sig).
  Notation t_eq_bool_ok := (@t_eq_bool_ok Sig).

  Definition eq_tt_bool t12 t12'  := 
    match t12, t12' with 
      (t1,t2), (t1',t2') => andb (@t_eq_bool t1 t1') (@t_eq_bool t2 t2')
    end.

  (* Definition of [equiv_eval_list] used to define [equiv_eval]. *)

  Function equiv_eval_list (p : term -> term -> option bool) (l1 l2 : list term) 
    {struct l1} : option bool := 
    match l1, l2 with
      | nil, nil => Some true
      | (a :: l), (b :: l') => 
        match p a b with
          | Some true => equiv_eval_list p l l'
          | Some false => Some false
          | None => None
        end
      | _, _ => Some false
    end.

  (* Define a [result] type. *)

  Inductive result (A : Type) : Type := 
  | Not_found : result A
  | Not_finished : result A
  | Found : A -> result A.

  (* Definition of [remove_equiv_eval] used to define [remove_equiv_eval_list]. *)

  Function remove_equiv_eval (p : term -> term -> option bool) 
    (t : term) (l : list term) {struct l} : result (list term) :=
    match l with
      | nil => @Not_found _
      | a :: l => 
        match p t a with
          | Some true => (Found l)
          | Some false =>
            match remove_equiv_eval p t l  with
              | Found l' => Found (a :: l')
              | Not_found => @Not_found _
              | Not_finished => @Not_finished _
            end
          | None => @Not_finished _
        end 
    end.

  (* Definition of [remove_equiv_eval_list] used to define [equiv_eval]. *)

  Function  remove_equiv_eval_list (p : term -> term -> option bool) (l1 l2 : list term) 
    {struct l1} : option ((list term) * (list term)):=
    match l1, l2 with
      | _, nil => Some (l1,l2)
      | nil, _ => Some (l1,l2)
      | a1 :: l1, l2 =>
        match remove_equiv_eval p a1 l2 with
          | Found l2' =>  remove_equiv_eval_list p l1 l2' 
          | Not_found =>
            match remove_equiv_eval_list p l1 l2 with
              | Some (l1',l2') => Some (a1 :: l1', l2')
              | None => None
            end
          | Not_finished => None
        end
    end.

  (* Definition of [equiv_eval] used to define [rpo_eval]. *)

  Fixpoint equiv_eval rpo_infos (n : nat) (t1 t2 : term) {struct n} : option bool := 
    match n with
      | 0 => None
      | S m =>
        match t1, t2 with
          | Var v1, Var v2 => Some (eq_var_bool v1 v2)
          | Term f1 l1, Term f2 l2 =>
            if mem_bool eq_tt_bool  (t1, t2) rpo_infos.(equiv_l)
              then  Some true 
              else
                if prec_eq_bool P f1 f2 
                  then 
                    match status P f1 with
                      | Lex =>  equiv_eval_list (equiv_eval rpo_infos m) l1 l2
                      | Mul => 
                        match remove_equiv_eval_list (equiv_eval rpo_infos m) l1 l2 with
                          | Some (nil,nil) => Some true
                          | Some _ => Some false
                          | None => None
                        end
                    end
                  else Some false
          | _, _ => Some false
        end
    end.

  (* Definition of [prec_eval] used to define function [rpo_eval]. *)

  Definition prec_eval f1 f2 :=
    if (prec_eq_bool P f1 f2) 
      then Equivalent
      else 
        if prec_bool P f1 f2 then Less_than
          else 
            if prec_bool P f2 f1 then Greater_than
              else Uncomparable.

  (* Definition of [list_gt_list] used to define [mult_eval]. *)

  Definition list_gt_list  (p : term -> term -> option comp) lg ls :=
    list_forall_option 
    (fun s => 
      list_exists_option 
      (fun g => 
        match p g s with
          | Some Greater_than => Some true
          | Some _ => Some false
          | None => None
        end) lg) ls.

  (* Definition of [mult_eval] used to define function [rpo_eval]. *)

  Definition mult_eval (p : term -> term -> option comp) (l1 l2 : list term)  : option comp :=
    match list_gt_list p l1 l2 with
      | None => None
      | Some true => Some Greater_than
      | Some false =>
        match list_gt_list p l2 l1 with
          | Some true => Some Less_than
          | Some false => Some Uncomparable
          | None => None
        end
    end.

  (* Definition of [term_gt_list] used to define [lexico_eval]. *)

  Definition term_gt_list (p : term -> term -> option comp) s l :=
    list_forall_option 
    (fun t => 
      match p s t with
        | Some Greater_than => Some true
        | Some _ => Some false
        | None => None
      end) l.

  (* Definition of [lexico_eval] used to define [rpo_eval]. *)

  Fixpoint lexico_eval (p : term -> term -> option comp) (s1 s2 : term)
    (l1 l2 : list term) {struct l1} : option comp :=
    match l1, l2 with
      | nil, nil => Some Equivalent
      | nil, (_ :: _) => Some Less_than
      | (_ :: _), nil => Some Greater_than
      | (t1 :: l1'), (t2 :: l2') =>
        match p t1 t2 with
          | Some Equivalent => lexico_eval p s1 s2 l1' l2'
          | Some Greater_than => 
            match term_gt_list p s1 l2 with
              | Some true => Some Greater_than
              | Some false => Some Uncomparable
              | None => None
            end
          | Some Less_than =>
            match term_gt_list p s2 l1 with
              | Some true => Some Less_than
              | Some false => Some Uncomparable
              | None => None
            end
          | Some Uncomparable => Some Uncomparable
          | None => None
        end
    end.

  (* Definition of [rpo_eval] main function to define [bsucc_rpo] in
     Coccinelle2.v *)

  Fixpoint rpo_eval rpo_infos (n : nat) (t1 t2 : term) {struct n} : option comp :=
    if mem_bool eq_tt_bool (t1, t2) (rpo_l rpo_infos) 
      then Some Less_than
      else if mem_bool eq_tt_bool (t2, t1) (rpo_l rpo_infos) 
        then Some Greater_than 
        else if mem_bool eq_tt_bool (t1, t2) (equiv_l rpo_infos) 
          then Some Equivalent 
          else if mem_bool eq_tt_bool (t2, t1) (equiv_l rpo_infos) 
            then Some Equivalent 
            else
              (match equiv_eval rpo_infos n t1 t2 with
                 | None => None
                 | Some true => Some Equivalent
                 | Some false =>
                   (match t1, t2 with
                      | Var _, Var _ => Some Uncomparable

                      | Var x, (Term _ l) =>
                        if var_in_term_list x l
                          then Some Less_than
                          else Some Uncomparable

                      | (Term _ l), Var x =>
                        if var_in_term_list x l
                          then Some Greater_than
                          else Some Uncomparable

                      | (Term f1 l1), (Term f2 l2) =>
                        (match n with
                           | 0 => None
                           | S m => 
                             let check_l1_gt_t2 :=
                               list_exists_option 
                               (fun t => match rpo_eval rpo_infos m t t2 with 
                                           | Some Equivalent 
                                           | Some Greater_than => Some true
                                           | Some _ => Some false
                                           | None => None
                                         end) l1 in
                               (match check_l1_gt_t2 with
                                  | None => None
                                  | Some true => Some Greater_than
                                  | Some false =>
                                    let check_l2_gt_t1 :=
                                      list_exists_option 
                                      (fun t => match rpo_eval rpo_infos m t1 t with
                                                  | Some Equivalent 
                                                  | Some Less_than => Some true
                                                  | Some _ => Some false
                                                  | None  => None
                                                end) l2 in
                                      (match check_l2_gt_t1 with
                                         | None => None
                                         | Some true => Some Less_than
                                         | Some false =>
                                           (match prec_eval f1 f2 with
                                              | Uncomparable => Some Uncomparable
                                              | Greater_than =>
                                                let check_l2_lt_t1 :=
                                                  list_forall_option
                                                  (fun t => match rpo_eval rpo_infos m t1 t with
                                                              | Some Greater_than => Some true
                                                              | Some _ => Some false
        	                                              | None => None
                                                            end) l2 in
                                                  (match check_l2_lt_t1 with
                                                     | None => None
                                                     | Some true => Some Greater_than
                                                     | Some false => Some Uncomparable
                                                   end)
                                              | Less_than =>
                                                let check_l1_lt_t2 :=
                                                  list_forall_option
                                                  (fun t => match rpo_eval rpo_infos m t t2 with
                                                              | Some Less_than => Some true
                                                              | Some _ => Some false
                                                              | None => None
                                                            end) l1 in
                                                  (match check_l1_lt_t2 with
                                                     | None => None
                                                     | Some true => Some Less_than
                                                     | Some false => Some Uncomparable
                                                   end)
                                              | Equivalent =>
                                                (match status P f1 with
                                                   | Mul => 
                                                     match remove_equiv_eval_list (equiv_eval rpo_infos m) l1 l2 with
                                                       | None => None
                                                       | Some (nil, nil) => Some Equivalent
                                                       | Some (nil, _ :: _) => Some Less_than
                                                       | Some (_ :: _,nil) => Some Greater_than
                                                       | Some (l1, l2) => mult_eval (rpo_eval rpo_infos m) l1 l2
                                                     end
                                                   | Lex => 
                                                     if (var_eq_bool (length l1) (length l2)) || 
                                                       (leb (length l1) rpo_infos.(bb) && leb (length l2) rpo_infos.(bb))
                                                       then lexico_eval (rpo_eval rpo_infos m) t1 t2 l1 l2
                                                       else Some Uncomparable
                                                 end) 
                                            end)
                                       end)
                                end)
                         end)
                    end)
               end).

  (* The proof of [eq_tt_bool_ok] used in the proof of [find_is_sound]. *)

  Lemma eq_tt_bool_ok : forall t12 t12',
    match eq_tt_bool t12 t12' with true => t12 = t12' | false => t12 <> t12' end.

  Proof.
    unfold eq_tt_bool; intros [t1 t2] [t1' t2']; generalize (@t_eq_bool_ok t1 t1');
      case (@t_eq_bool t1 t1').
    intro t1_eq_t1'; generalize (@t_eq_bool_ok t2 t2'); case (@t_eq_bool t2 t2').
    intro t2_eq_t2'; simpl; subst; reflexivity.
    intro t2_diff_t2'; simpl; intro H; apply t2_diff_t2'; injection H; intros; assumption.
    intro t1_diff_t1'; simpl; intro H; apply t1_diff_t1'; injection H; intros; assumption.
  Defined.

  (* The proof of [find_is_sound] used in the proof of [rpo_eval_is_sound_weak]. *)

  Lemma find_is_sound : 
    forall (I: term -> term -> Prop) l (l_sound: forall t t', In (t,t') l -> I t t') t1 t2,  
      mem_bool eq_tt_bool (t1,t2) l = true -> 
      I t1 t2.
  Proof.
    intros I l l_sound t1 t2 H; apply l_sound.
    apply (mem_impl_in (@eq (term*term))).
    intros; assumption.
    generalize (mem_bool_ok _ _ eq_tt_bool_ok (t1,t2) l); rewrite H; intros; assumption.
  Qed.
  
  (* The proof of [rpo_eval_equation] used in the proof of
     [rpo_eval_is_sound_weak]. *)

  Lemma rpo_eval_equation :
    forall rpo_infos n t1 t2, rpo_eval rpo_infos n t1 t2 =
      if mem_bool eq_tt_bool (t1, t2) (rpo_l rpo_infos) 
        then Some Less_than
        else if mem_bool eq_tt_bool (t2, t1) (rpo_l rpo_infos) 
          then Some Greater_than 
          else if mem_bool eq_tt_bool (t1, t2) (equiv_l rpo_infos) 
            then Some Equivalent 
            else if mem_bool eq_tt_bool (t2, t1) (equiv_l rpo_infos) 
              then Some Equivalent 
              else
                (match equiv_eval rpo_infos n t1 t2 with
                   | None => None
                   | Some true => Some Equivalent
                   | Some false =>
                     (match t1, t2 with
                        | Var _, Var _ => Some Uncomparable
                        | Var x, (Term _ l) =>
                          if var_in_term_list x l
                            then Some Less_than
                            else Some Uncomparable
                        | (Term _ l), Var x =>
                          if var_in_term_list x l
                            then Some Greater_than
                            else Some Uncomparable
                        | (Term f1 l1), (Term f2 l2) =>
                          (match n with
                             | 0 => None
                             | S m => 
                               let check_l1_gt_t2 :=
                                 list_exists_option 
                                 (fun t => match rpo_eval rpo_infos m t t2 with 
                                             | Some Equivalent 
                                             | Some Greater_than => Some true
                                             | Some _ => Some false
                                             | None => None
                                           end) l1 in
                                 (match check_l1_gt_t2 with
                                    | None => None
                                    | Some true => Some Greater_than
                                    | Some false =>
                                      let check_l2_gt_t1 :=
                                        list_exists_option 
                                        (fun t => match rpo_eval rpo_infos m t1 t with
                                                    | Some Equivalent 
                                                    | Some Less_than => Some true
                                                    | Some _ => Some false
                                                    | None  => None
                                                  end) l2 in
                                        (match check_l2_gt_t1 with
                                           | None => None
                                           | Some true => Some Less_than
                                           | Some false =>
                                             (match prec_eval f1 f2 with
                                                | Uncomparable => Some Uncomparable
                                                | Greater_than =>
                                                  let check_l2_lt_t1 :=
                                                    list_forall_option
                                                    (fun t => match rpo_eval rpo_infos m t1 t with
                                                                | Some Greater_than => Some true
                                                                | Some _ => Some false
        	                                                | None => None
                                                              end) l2 in
                                                    (match check_l2_lt_t1 with
                                                       | None => None
                                                       | Some true => Some Greater_than
                                                       | Some false => Some Uncomparable
                                                     end)
                                                | Less_than =>
                                                  let check_l1_lt_t2 :=
                                                    list_forall_option
                                                    (fun t => match rpo_eval rpo_infos m t t2 with
                                                                | Some Less_than => Some true
                                                                | Some _ => Some false
                                                                | None => None
                                                              end) l1 in
                                                    (match check_l1_lt_t2 with
                                                       | None => None
                                                       | Some true => Some Less_than
                                                       | Some false => Some Uncomparable
                                                     end)
                                                | Equivalent =>
                                                  (match status P f1 with
                                                     | Mul => 
                                                       match remove_equiv_eval_list (equiv_eval rpo_infos m) l1 l2 with
                                                         | None => None
                                                         | Some (nil, nil) => Some Equivalent
                                                         | Some (nil, _ :: _) => Some Less_than
                                                         | Some (_ :: _,nil) => Some Greater_than
                                                         | Some (l1, l2) => mult_eval (rpo_eval rpo_infos m) l1 l2
                                                       end
                                                     | Lex => 
                                                       if (var_eq_bool (length l1) (length l2)) || 
                                                         (leb (length l1) rpo_infos.(bb) && leb (length l2) rpo_infos.(bb))
                                                         then lexico_eval (rpo_eval rpo_infos m) t1 t2 l1 l2
                                                         else Some Uncomparable
                                                   end) 
                                              end)
                                         end)
                                  end)
                           end)
                      end)
                 end).
  Proof.
    intros rpo_infos [ | n] [v1 | f1 l1] [v2 | f2 l2];
      unfold rpo_eval; simpl; trivial.
  Qed.

  Lemma remove_equiv_eval_is_sound : 
    forall p t l, 
      match remove_equiv_eval p t l with
        | Found l' => 
          exists t', p t t' = Some true /\ 
            list_permut.permut0 (@eq term) l (t' :: l')
        | Not_found => forall t', In t' l -> p t t' = Some false
        | Not_finished => exists t', In t' l /\ p t t' = None
      end.
    intros p t l; 
      functional induction (remove_equiv_eval p t l) as 
        [ 
          | H1 a l t' H 
          | H1 a l t' H IH l' H' 
          | H1 a l t' H IH H' 
          | H1 a l t' H IH H' 
          | H1 a l t' H].
    simpl; intros; contradiction.
    exists a; split; auto.
    apply list_permut.permut_refl; intro; trivial.
    rewrite H' in IH; destruct IH as [t' [H'' P1]]; exists t'; split; trivial.
    apply (Pcons (R := @eq term) a a (l := l) (t' :: nil) l'); trivial.
    rewrite H' in IH; intros t' [a_eq_t' | t'_in_l]; [subst | apply IH]; trivial.
    rewrite H' in IH; destruct IH as [t' [t'_in_l ptt'_eq_none]]; 
      exists t'; split; trivial; right; trivial.
    exists a; split; trivial; left; trivial.
  Qed.

  Lemma remove_equiv_eval_list_is_sound :
    forall p l1 l2, 
      match remove_equiv_eval_list p l1 l2 with
        | Some (l1',l2') => 
          exists ll, (forall t1 t2, In (t1,t2) ll -> p t1 t2 = Some true) /\
            list_permut.permut0 (@eq term) l1 (l1' ++ (map (fun st => fst st) ll)) /\
            list_permut.permut0 (@eq term) l2 (l2' ++ (map (fun st => snd st) ll)) /\
            (forall t1 t2, In t1 l1' -> In t2 l2' -> p t1 t2 = Some false)
        | None => exists t1, exists t2, In t1 l1 /\ In t2 l2 /\ p t1 t2 = None
      end.
  Proof.
    intros p l1 l2; 
      functional induction (remove_equiv_eval_list p l1 l2) as
        [ l1
          | H1 l2 H2 H3 H4 H'
          | H1 l2 t1 l1 H2 H3 H4 H' l2' H IH 
          | H1 l2 t1 l1 H2 H3 H4 H' H IH l1' l2' R
          | H1 l2 t1 l1 H2 H3 H4 H' H IH R
          | H1 l2 t1 l1 H2 H3 H4 H' H].
      (* 1/ 6 *)
    exists (@nil (term * term)); simpl; intuition; intros.
    rewrite <- app_nil_end; apply list_permut.permut_refl; intro; trivial.
    apply list_permut.permut_refl; intro; trivial.
      (* 1/5 *)
    destruct l2 as [ | t2 l2].
    contradiction.
    exists (@nil (term * term)); simpl; intuition; intros.
    apply list_permut.permut_refl; intro; trivial.
    rewrite <- app_nil_end; apply list_permut.permut_refl; intro; trivial.
      (* 1/4 *)
    assert (K := remove_equiv_eval_is_sound p t1 l2); rewrite H in K.
    destruct K as [t2' [pt1t2_eq_true P1]].
    destruct (remove_equiv_eval_list p l1 l2') as [ [l1'' l2''] | ].
    destruct IH as [ll [E_ll [P11 [P2 F]]]]; exists ((t1,t2') :: ll); repeat split; trivial.
    intros u1 u2 [u1u2_eq_t1t2' | u1u2_in_ll].
    injection u1u2_eq_t1t2'; intros; subst; apply pt1t2_eq_true.
    apply E_ll; trivial.
    simpl; apply Pcons; trivial.
    apply list_permut.permut_trans with (t2' :: l2').
    intros a b c _ a_eq_b b_eq_c; transitivity b; trivial. trivial.
    simpl. apply Pcons. trivial.
    trivial. 
    destruct IH as [t1' [t2 [t1_in_l1 [t2_in_l2 p1p2_eq_none]]]];
      exists t1'; exists t2; repeat split; trivial.
    right; trivial.
    destruct (list_permut.permut_inv_right P1) as [t2'' [k2 [k2' [t2''_eq_t2' [H'' P']]]]].
    subst l2; apply in_insert.
    generalize (k2 ++ k2') l2' t2_in_l2 P'; intro k; induction k as [ | u k];
      intros l t2_in_l Q; inversion Q as [ | a b k' l1' l2]; subst; trivial.

      (* REMARK: in_app_or comment proof *)

    destruct (in_app_or t2_in_l) as [t2_in_l1' | [t2_eq_b | t2_in_l2']].
    right; apply (IHk (l1' ++ l2)); trivial; apply in_or_app; left; trivial.
    left; subst; trivial.
    right; apply (IHk (l1' ++ l2)); trivial; apply in_or_app; right; trivial.
      (* 1/3 *)
    assert (K := remove_equiv_eval_is_sound p t1 l2); rewrite H in K.
    rewrite R in IH; destruct IH as [ll [E_ll [P1 [P2 F]]]]; 
      exists ll; repeat split; auto.
    simpl. apply (Pcons (R := @eq term) t1 t1 (l := l1) nil
    (l1' ++ map (fun st : term * term => fst st) ll)); trivial.
    simpl; intros u1 u2 [u1_eq_t1 | u1_in_l1'] u2_in_l2'.
    subst u1; apply K; rewrite (in_permut_in P2);
      apply in_or_app; left; trivial.
    apply F; trivial.
      (* 1/2 *)
    rewrite R in IH; destruct IH as [u1 [u2 [u1_in_l1 [u2_in_l2 pu1u2_eq_none]]]];
      exists u1; exists u2; repeat split; trivial; right; trivial.
      (* 1/1 *)
    assert (K := remove_equiv_eval_is_sound p t1 l2); rewrite H in K.
    destruct K as [t2 [t2_in_l2 pt1t2_eq_none]];
      exists t1; exists t2; repeat split; trivial; left; trivial.
  Qed.

  Lemma equiv_eval_is_sound_weak :
    forall rpo_infos n t1 t2, equiv_eval rpo_infos n t1 t2 = Some true -> equiv t1 t2.
    intros rpo_infos n; induction n as [ | n].
      (* n = 0 *)
    intros; discriminate.
      (* n = S n *)
    destruct t1 as [v1 | f1 l1]; destruct t2 as [v2 | f2 l2]; simpl.
      (* t1 = Var v1 ; t2 = v2 *)
    generalize (eq_var_bool_ok v1 v2); case (eq_var_bool v1 v2); [intro v1_eq_v2 | intro v1_diff_v2].
      (* v1 = v2 *)
    subst; intuition; apply Eq.
      (* v1 <> v2 *)
    intro; discriminate.
      (*t1 = Var v1 ; t2 = f2 l2*)
    intro; discriminate.
      (*t1 = f1 l1 ; t2 = v2 *)
    intro; discriminate.
      (*t1 = f1 l1 ; t2 = f2 l2 *)
    case_eq (mem_bool eq_tt_bool ((Term f1 l1), (Term f2 l2)) (equiv_l rpo_infos));simpl.
      (* (t1,t2) in (equiv_l rpo_infos) *)
    intros H _ ;eapply find_is_sound with (1:=equiv_l_valid rpo_infos);auto.
    intros _.
    case_eq (prec_eq_bool P f1 f2); [intro f1_eq_f2 | intro f1_diff_f2].
    case_eq (status P f1). intros Status.
    intro H; apply Eq_lex; trivial.
    assert (H1:= prec_eq_status). assert (H1':= H1 _ P f1 f2).
    assert (status P f1 = status P f2). apply H1'; trivial. trivial.
    assert (H3:= prec_eq_bool_ok). assert (H3':= H3 _ P f1 f2).
    rewrite f1_eq_f2 in H3'. trivial. rewrite <- H0. trivial.
    assert (H3:= prec_eq_bool_ok). assert (H3':= H3 _ P f1 f2).
    rewrite f1_eq_f2 in H3'. trivial.
    generalize l1 l2 H; clear l1 l2 H;
      intro l; induction l as [ | t l]; intros [ | t' l'] H.
    apply Eq_list_nil.
    discriminate.
    discriminate.
    simpl in H; apply Eq_list_cons.
    apply IHn; destruct (equiv_eval rpo_infos n t t') as [ [ | ] | ]; 
      trivial; discriminate.
    apply IHl; destruct (equiv_eval rpo_infos n t t') as [ [ | ] | ]; 
      trivial; discriminate. intro Status.

    intro H; assert (H' := remove_equiv_eval_list_is_sound (equiv_eval rpo_infos n) l1 l2);
      destruct (remove_equiv_eval_list (equiv_eval rpo_infos n) l1 l2) as [ [l1' l2'] | ].
    destruct H' as [ll [E_ll [P1 [P2 H']]]];
      apply Eq_mul; trivial.
    assert (H1:= prec_eq_status). assert (H1':= H1 _ P f1 f2).
    assert (status P f1 = status P f2). apply H1'; trivial. trivial.
    assert (H3:= prec_eq_bool_ok). assert (H3':= H3 _ P f1 f2).
    rewrite f1_eq_f2 in H3'. trivial. rewrite <- H0. trivial.
    assert (H3:= prec_eq_bool_ok). assert (H3':= H3 _ P f1 f2).
    rewrite f1_eq_f2 in H3'. trivial.
    destruct l1'; destruct l2'; try discriminate; simpl in P1; trivial.
    generalize l1 l2 P1 P2; clear l1 l2 P1 P2; 
      induction ll as [ | [t1 t2] ll]; intros l1 l2 P1 P2.
    rewrite (permut_nil P1); rewrite (permut_nil P2); apply Pnil.
    destruct (permut_inv_right P1) as [t1' [l1' [l1'' [t1_eq_t1' [H'' Q1]]]]]; subst l1 t1'.
    destruct (permut_inv_right P2) as [t2' [l2' [l2'' [t2_eq_t2' [H'' Q2]]]]]; subst l2 t2'.
    simpl; apply permut_strong.
    apply IHn; apply E_ll; left; trivial.
    apply IHll; trivial.
    intros; apply E_ll; right; trivial.
    discriminate.
    intro; discriminate.
  Qed.

  Lemma trans_clos_subterm_rpo:
    forall bb s t,  (trans_clos (@direct_subterm Sig)) s t -> rpo bb s t.
  Proof.
    intros bb s t H; induction H as [ s [ v | f l ] H | s t u H1 H2].
    inversion H.
    apply (@Subterm bb f l s s); trivial.
    simpl in H; apply in_impl_mem; trivial.
    exact Eq.
    apply Equiv; apply Eq.
    apply (@rpo_subterm bb u t); trivial.
  Qed.

  Lemma term_gt_list_is_sound :
    forall p s l,
      match term_gt_list p s l with
        | Some true => forall t, In t l -> p s t = Some Greater_than
        | _ => True
      end.
  Proof.
    intros p s l; induction l as [ | t l]; simpl.
    intros; contradiction.
    replace (term_gt_list p s (t :: l)) with
      (match p s t with
         | Some Greater_than => term_gt_list p s l
         | Some _ => match term_gt_list p s l with Some _ => Some false | None => None end
         | None => None
       end).
    case_eq (p s t); [intros [ | | | ] H | trivial].
    destruct (term_gt_list p s l) as [ [ | ] | ]; trivial.
    destruct (term_gt_list p s l) as [ [ | ] | ]; trivial.
    destruct (term_gt_list p s l) as [ [ | ] | ]; trivial.
    intros u [u_eq_t | u_in_l]; [subst | apply IHl]; assumption.
    destruct (term_gt_list p s l) as [ [ | ] | ]; trivial.
    unfold term_gt_list; simpl.
    destruct (p s t) as [[ | | | ] | ]; trivial.
  Qed.

  Lemma lexico_eval_is_sound :
    forall (p : term -> term -> option comp) s1 s2 l1 l2,
      match lexico_eval p s1 s2 l1 l2 with
        | Some Equivalent => 
          (exists ll, (forall t1 t2, In (t1,t2) ll -> p t1 t2 = Some Equivalent) /\
            l1 = map (fun st => fst st) ll /\
            l2 = map (fun st => snd st) ll) 
        |  Some Less_than => 
          (l1 = nil /\ l2 <> nil) \/
          (exists ll, exists t2, exists l2',
            (forall t1 t2, In (t1,t2) ll -> p t1 t2 = Some Equivalent) /\
            l1 = map (fun st => fst st) ll /\
            l2 = map (fun st => snd st) ll ++ t2 :: l2') \/
          (exists ll, exists t1, exists t2, exists l1', exists l2',
            (forall t1 t2, In (t1,t2) ll -> p t1 t2 = Some Equivalent) /\
            p t1 t2 = Some Less_than /\
            (forall t1, In t1 l1 -> 
              ((exists t2, In t2 l2 /\ (p t1 t2 = Some Equivalent \/
                p t1 t2 = Some Less_than)) \/ 
              p s2 t1 = Some Greater_than)) /\
            l1 = map (fun st => fst st) ll ++ t1 :: l1' /\
            l2 = map (fun st => snd st) ll ++ t2 :: l2')
        |  Some Greater_than => 
          (l1 <> nil /\ l2 = nil) \/
          (exists ll, exists t1, exists l1',
            (forall t1 t2, In (t1,t2) ll -> p t1 t2 = Some Equivalent) /\
            l1 = map (fun st => fst st) ll ++ t1 :: l1' /\
            l2 = map (fun st => snd st) ll) \/
          (exists ll, exists t1, exists t2, exists l1', exists l2',
            (forall t1 t2, In (t1,t2) ll -> p t1 t2 = Some Equivalent) /\
            p t1 t2 = Some Greater_than /\
            (forall t2, In t2 l2 -> 
              ((exists t1, In t1 l1 /\ (p t1 t2 = Some Equivalent \/
                p t1 t2 = Some Greater_than)) \/ 
              p s1 t2 = Some Greater_than)) /\
            l1 = map (fun st => fst st) ll ++ t1 :: l1' /\
            l2 = map (fun st => snd st) ll ++ t2 :: l2')
        | _ => True
      end.
  Proof. 
    intros p s1 s2 l1; induction l1 as [ | t1 l1]; intros [ | t2 l2].
    simpl; exists (@nil (term * term)); simpl; intuition.
    simpl; left; split; [apply refl_equal | discriminate].
    simpl; left; split; [discriminate | apply refl_equal].
    simpl; case_eq (p t1 t2); [idtac | trivial].
    intros [ | | | ] Ht; generalize (IHl1 l2).
      (* 1/4 p t1 t2 = Some Equivalent *)
    case_eq (lexico_eval p s1 s2 l1 l2); [intros [ | | | ] Hl | trivial].
      (* 1/7 lexico_eval p s1 s2 l1 l2 = Some Equivalent *)
    intros [ll [Hll [H1 H2]]]; exists ((t1,t2) :: ll); split.
    simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_ll]; [injection u1u2_eq_t1t2; intros; subst | apply Hll]; assumption.
    simpl; split; subst; apply refl_equal.
      (* 1/6 lexico_eval p s1 s2 l1 l2 = Some Less_than *)
    intros [[H1 H2] | [[ll [a2 [l2' [Hll [H1 H2]]]]] | [ll [a1 [a2 [l1' [l2' [Hll [Ha [H [H1 H2]]]]]]]]]]].
    right; left; subst; destruct l2 as [ | a2 l2].
    discriminate.
    exists ((t1,t2) :: nil); exists a2; exists l2; split.
    simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_nil]; [injection u1u2_eq_t1t2; intros; subst; assumption | contradiction].
    split; apply refl_equal.
    right; left; exists ((t1,t2) :: ll); exists a2; exists l2'; split.
    simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_ll]; [injection u1u2_eq_t1t2; intros; subst | apply Hll]; assumption.
    split; subst; apply refl_equal.
    do 2 right; exists ((t1,t2) :: ll); exists a1; exists a2; exists l1'; exists l2'; split.
    simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_ll]; [injection u1u2_eq_t1t2; intros; subst | apply Hll]; assumption.
    split.
    assumption.
    split.
    intros u [t1_eq_u | u_in_l1].
    subst u; left; exists t2; split; left; trivial.
    destruct (H _ u_in_l1) as [[u2 [u2_in_l2 H']] | H'].
    left; exists u2; split; [right | idtac]; assumption.
    right; assumption.
    split; subst; apply refl_equal.
(* 1/5 lexico_eval p s1 s2 l1 l2 = Some Greater_than *)
    intros [[H1 H2] | [[ll [a1 [l1' [Hll [H1 H2]]]]] | [ll [a1 [a2 [l1' [l2' [Hll [Ha [H [H1 H2]]]]]]]]]]].
    right; left; subst; destruct l1 as [ | a1 l1].
    discriminate.
    exists ((t1,t2) :: nil); exists a1; exists l1; split.
    simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_nil]; [injection u1u2_eq_t1t2; intros; subst; assumption | contradiction].
    split; apply refl_equal.
    right; left; exists ((t1,t2) :: ll); exists a1; exists l1'; split.
    simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_ll]; [injection u1u2_eq_t1t2; intros; subst | apply Hll]; assumption.
    split; subst; apply refl_equal.
    do 2 right; exists ((t1,t2) :: ll); exists a1; exists a2; exists l1'; exists l2'; split.
    simpl; intros u1 u2 [u1u2_eq_t1t2 | u1u2_in_ll]; [injection u1u2_eq_t1t2; intros; subst | apply Hll]; assumption.
    split.
    assumption.
    split.
    intros u [t2_eq_u | u_in_l2].
    subst u; left; exists t1; split; left; trivial.
    destruct (H _ u_in_l2) as [[u1 [u1_in_l1 H']] | H'].
    left; exists u1; split; [right | idtac]; assumption.
    right; assumption.
    split; subst; apply refl_equal.
      (* 1/4 lexico_eval p s1 s2 l1 l2 = Some Uncomparable *)
    trivial.
      (* 1/3 p t1 t2 = Some Less_than *)
    case_eq (lexico_eval p s1 s2 l1 l2).
    intros [ | | | ] Hl.
      (* 1/7 lexico_eval p s1 s2 l1 l2 = Some Equivalent *)
    intros [ll [Hll [H1 H2]]].
    generalize (term_gt_list_is_sound p s2 (t1 :: l1)).
    destruct (term_gt_list p s2 (t1 :: l1)) as [[ | ] | ].
    intro H; do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
    intros; contradiction.
    split.
    assumption.
    split.
    intros u u_in_t1l1; right; apply H; trivial.
    simpl; split; subst; apply refl_equal.
    trivial.
    trivial.
      (* 1/6 lexico_eval p s1 s2 l1 l2 = Some Less_than *)
    intros [[H1 H2] | [[ll [a2 [l2' [Hll [H1 H2]]]]] | [ll [a1 [a2 [l1' [l2' [Hll [Ha [H [H1 H2]]]]]]]]]]];
      generalize (term_gt_list_is_sound p s2 (t1 :: l1)); destruct (term_gt_list p s2 (t1 :: l1)) as [[ | ] | ]; intro H'; trivial;
        do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
    intros; contradiction.
    split.
    assumption.
    split.
    intros u u_in_t1l1; right; apply H'; assumption.
    split; apply refl_equal.
    intros; contradiction.
    split.
    assumption.
    split.
    intros u u_in_t1l1; right; apply H'; assumption.
    split; apply refl_equal.
    intros; contradiction.
    split.
    assumption.
    split.
    intros u u_in_t1l1; right; apply H'; assumption.
    split; apply refl_equal.
      (* 1/5 lexico_eval p s1 s2 l1 l2 = Some Greater_than *)
    intros _.
    generalize (term_gt_list_is_sound p s2 (t1 :: l1));
      destruct (term_gt_list p s2 (t1 :: l1)) as [[ | ] | ]; intro H'; trivial.
    do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
    intros; contradiction.
    split.
    assumption.
    split.
    intros u u_in_t1l1; right; apply H'; assumption.
    split; apply refl_equal.
      (* 1/4 lexico_eval p s1 s2 l1 l2 = Some  Some Uncomparable *)
    intros _.
    generalize (term_gt_list_is_sound p s2 (t1 :: l1));
      destruct (term_gt_list p s2 (t1 :: l1)) as [[ | ] | ]; intro H'; trivial.
    do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
    intros; contradiction.
    split.
    assumption.
    split.
    intros u u_in_t1l1; right; apply H'; assumption.
    split; apply refl_equal.
      (* 1/3 lexico_eval p s1 s2 l1 l2 = None *)
    intros _.
    generalize (term_gt_list_is_sound p s2 (t1 :: l1));
      destruct (term_gt_list p s2 (t1 :: l1)) as [[ | ] | ]; intro H'; trivial.
    do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
    intros; contradiction.
    split.
    assumption.
    split.
    intros u u_in_t1l1; right; apply H'; assumption.
    split; apply refl_equal.
      (* 1/3 p t1 t2 = Some Greater_than *)
    case_eq (lexico_eval p s1 s2 l1 l2).
    intros [ | | | ] Hl.
      (* 1/6 lexico_eval p s1 s2 l1 l2 = Some Equivalent *)
    intros [ll [Hll [H1 H2]]].
    generalize (term_gt_list_is_sound p s1 (t2 :: l2)).
    destruct (term_gt_list p s1 (t2 :: l2)) as [[ | ] | ].
    intro H; do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
    intros; contradiction.
    split.
    assumption.
    split.
    intros u u_in_t1l2; right; apply H; trivial.
    simpl; split; subst; apply refl_equal.
    trivial.
    trivial.
      (* 1/5 lexico_eval p s1 s2 l1 l2 = Some Less_than *)
    intros [[H1 H2] | [[ll [a2 [l2' [Hll [H1 H2]]]]] | [ll [a1 [a2 [l1' [l2' [Hll [Ha [H [H1 H2]]]]]]]]]]];
      generalize (term_gt_list_is_sound p s1 (t2 :: l2));
        destruct (term_gt_list p s1 (t2 :: l2)) as [[ | ] | ]; intro H'; trivial;
          do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
    intros; contradiction.
    split.
    assumption.
    split.
    intros u u_in_t2l2; right; apply H'; assumption.
    split; apply refl_equal.
    intros; contradiction.
    split.
    assumption.
    split.
    intros u u_in_t2l2; right; apply H'; assumption.
    split; apply refl_equal.
    intros; contradiction.
    split.
    assumption.
    split.
    intros u u_in_t2l2; right; apply H'; assumption.
    split; apply refl_equal.
      (* 1/4 lexico_eval p s1 s2 l1 l2 = Some Greater_than *)
    intros _.
    generalize (term_gt_list_is_sound p s1 (t2 :: l2));
      destruct (term_gt_list p s1 (t2 :: l2)) as [[ | ] | ]; intro H'; trivial.
    do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
    intros; contradiction.
    split.
    assumption.
    split.
    intros u u_in_t2l2; right; apply H'; assumption.
    split; apply refl_equal.
      (* 1/3 lexico_eval p s1 s2 l1 l2 = Some  Some Uncomparable *)
    intros _.
    generalize (term_gt_list_is_sound p s1 (t2 :: l2));
      destruct (term_gt_list p s1 (t2 :: l2)) as [[ | ] | ]; intro H'; trivial.
    do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
    intros; contradiction.
    split.
    assumption.
    split.
    intros u u_in_t2l2; right; apply H'; assumption.
    split; apply refl_equal.
      (* 1/2 lexico_eval p s1 s2 l1 l2 = None *)
    intros _.
    generalize (term_gt_list_is_sound p s1 (t2 :: l2));
      destruct (term_gt_list p s1 (t2 :: l2)) as [[ | ] | ]; intro H'; trivial.
    do 2 right; exists (@nil (term * term)); exists t1; exists t2; exists l1; exists l2; split.
    intros; contradiction.
    split.
    assumption.
    split.
    intros u u_in_t2l2; right; apply H'; assumption.
    split; apply refl_equal.
      (* 1/1 p t1 t2 = Some Uncomparable *)
    trivial.
  Qed.

Lemma list_gt_list_is_sound :
  forall p lg ls,
   match list_gt_list p lg ls with
   | Some true => forall s, In s ls -> exists g, In g lg /\ p g s = Some Greater_than
   | _ => True
   end.
Proof.
intros p lg ls; revert lg; induction ls as [ | s ls]; intro lg.
simpl; intros; contradiction.
unfold list_gt_list; simpl.
generalize (list_exists_option_is_sound 
  (fun g : term =>
       match p g s with
       | Some Equivalent => Some false
       | Some Less_than => Some false
       | Some Greater_than => Some true
       | Some Uncomparable => Some false
       | None => None
       end) lg).
destruct 
(list_exists_option
    (fun g : term =>
     match p g s with
     | Some Equivalent => Some false
     | Some Less_than => Some false
     | Some Greater_than => Some true
     | Some Uncomparable => Some false
     | None => None
     end) lg) as [[ | ] | ].
intros [g [g_in_ls H]].
generalize (IHls lg); unfold list_gt_list;
destruct 
(list_forall_option
    (fun s0 : term =>
     list_exists_option
       (fun g0 : term =>
        match p g0 s0 with
        | Some Equivalent => Some false
        | Some Less_than => Some false
        | Some Greater_than => Some true
        | Some Uncomparable => Some false
        | None => None
        end) lg) ls) as [[ | ] | ].
intros H' u [s_eq_u | u_in_ls].
subst u; exists g; split; trivial.
destruct (p g s) as [[ | | | ] | ]; (apply refl_equal || discriminate).
apply H'; assumption.
trivial.
trivial.
intros _;
destruct 
(list_forall_option
    (fun s0 : term =>
     list_exists_option
       (fun g0 : term =>
        match p g0 s0 with
        | Some Equivalent => Some false
        | Some Less_than => Some false
        | Some Greater_than => Some true
        | Some Uncomparable => Some false
        | None => None
        end) lg) ls) as [[ | ] | ]; trivial.
trivial.
Qed. 

Lemma mult_eval_is_sound_weak                              :
  forall p l1 l2, 
   match mult_eval p l1 l2 with
     | Some Equivalent => False
     | Some Less_than =>  
       forall t1, In t1 l1 -> exists t2, In t2 l2 /\ p t2 t1 = Some Greater_than
     | Some Greater_than =>  
       forall t2, In t2 l2 -> exists t1, In t1 l1 /\ p t1 t2 = Some Greater_than
     | _ => True
     end.
Proof.
intros p l1 l2; unfold mult_eval.
generalize (list_gt_list_is_sound p l1 l2); destruct (list_gt_list p l1 l2) as [[ | ] | ]; trivial.
intros; generalize (list_gt_list_is_sound p l2 l1); destruct (list_gt_list p l2 l1) as [[ | ] | ]; trivial.
Qed.

Lemma prec_eval_is_sound :  
    forall f1 f2, 
      match prec_eval f1 f2 with
        | Equivalent => prec_eq P f1  f2
        | Less_than => prec P f1 f2
        | Greater_than => prec P f2 f1 
        | Uncomparable => ~ prec_eq P f1 f2 /\ ~prec P f1 f2 /\ ~prec P f2 f1
      end.
  Proof.
    intros f1 f2; unfold prec_eval.
    case_eq (prec_eq_bool P f1 f2). intros.
    assert (H1:= prec_eq_bool_ok). assert (H1':= H1 _ P f1 f2).
    rewrite H in H1'. trivial.
    intro.
    case_eq (prec_bool P f1 f2).
    intros.
    assert (H1:= prec_bool_ok). assert (H1':= H1 _ P f1 f2).
    rewrite H0 in H1'. trivial.
    intros.
    case_eq (prec_bool P f2 f1).
    intro prec'.
    assert (H1:= prec_bool_ok). assert (H1':= H1 _ P f2 f1).
    rewrite prec' in H1'. trivial.
    intros.
    split.
    assert (H3:= prec_eq_bool_ok). assert (H3':= H3 _ P f1 f2).
    rewrite H in H3'. trivial.
    split. 
    assert (H3:= prec_bool_ok). assert (H3':= H3 _ P f1 f2).
    rewrite H0 in H3'. trivial.
    assert (H3:= prec_bool_ok). assert (H3':= H3 _ P f2 f1).
    rewrite H1 in H3'. trivial.
  Qed.
  
  (* The proof of lemma [rpo_eval_is_sound_weak] used to define a
     function [bsucc_rpo] in Coccinelle2.v *)
  
  Lemma rpo_eval_is_sound_weak :
    forall rpo_infos n t1 t2, 
      match rpo_eval rpo_infos n t1 t2 with
        | Some Equivalent => equiv t1 t2
        | Some Greater_than => rpo rpo_infos.(bb) t2 t1
        | Some Less_than => rpo rpo_infos.(bb) t1 t2
        | _ => True
      end.
Proof.
intros rpo_infos n; induction n as [ | n].
intros t1 t2. simpl.
case_eq (mem_bool eq_tt_bool (t1, t2) (rpo_l rpo_infos)). 
intros Hfind;apply (find_is_sound (rpo rpo_infos.(bb)) _ (rpo_l_valid rpo_infos) _ _ (Hfind)).
intro;
case_eq (mem_bool eq_tt_bool (t2, t1) (rpo_l rpo_infos)). 
intros Hfind;apply (find_is_sound (rpo rpo_infos.(bb)) _ (rpo_l_valid rpo_infos) _ _ (Hfind)).
intro. 
case_eq (mem_bool eq_tt_bool (t1, t2) (equiv_l rpo_infos)). 
intros Hfind;apply (find_is_sound equiv _ (equiv_l_valid rpo_infos) _ _ (Hfind)).
intro;
case_eq (mem_bool eq_tt_bool (t2, t1) (equiv_l rpo_infos)). 
intros Hfind; apply equiv_sym.
apply equiv_equiv.
apply (find_is_sound equiv _ (equiv_l_valid rpo_infos) _ _ (Hfind)).
tauto.
(* induction step *)
intros t1 t2; rewrite rpo_eval_equation.
case_eq (mem_bool eq_tt_bool (t1, t2) (rpo_l rpo_infos)). 
intros Hfind;apply (find_is_sound (rpo rpo_infos.(bb)) _ (rpo_l_valid rpo_infos) _ _ (Hfind)).
intros _;
case_eq (mem_bool eq_tt_bool (t2, t1) (rpo_l rpo_infos)). 
intros Hfind;apply (find_is_sound (rpo rpo_infos.(bb)) _ (rpo_l_valid rpo_infos) _ _ (Hfind)).
intros _. 
case_eq (mem_bool eq_tt_bool (t1, t2) (equiv_l rpo_infos)). 
intros Hfind;apply (find_is_sound equiv _ (equiv_l_valid rpo_infos) _ _ (Hfind)).
intros _;
case_eq (mem_bool eq_tt_bool (t2, t1) (equiv_l rpo_infos)). 
intros Hfind; apply equiv_sym.
apply equiv_equiv.
apply (find_is_sound equiv _ (equiv_l_valid rpo_infos) _ _ (Hfind)).
intros _.
assert (E1 := equiv_eval_is_sound_weak rpo_infos (S n) t1 t2); 
destruct (equiv_eval rpo_infos (S n) t1 t2) as [ [ | ] | ].
(* 1/3 t1 and t2 are equivalent *)
apply E1; trivial.
(* 1/2 t1 and t2 are not equivalent *)
clear E1; 
assert (H : forall v f l, var_in_term_list v l = true -> rpo rpo_infos.(bb) (Var _ v) (Term f l)).
intros v f l H; apply trans_clos_subterm_rpo; trivial.
assert (H' : (In (Var _ v) l \/ 
                  (exists t, In t l /\ trans_clos (@direct_subterm Sig) (@Var Sig v) t)) -> trans_clos (@direct_subterm Sig) (@Var Sig v) (Term f l)).
intros [v_in_l | [t [t_in_l H']]].
left; trivial.
apply trans_clos_is_trans with t; trivial; left; trivial.
apply H'; clear H'.
generalize H; clear H; pattern l; refine (list_rec3 size _ _ _); clear l.
intros m; induction m as [ | m]; intros [ | t l] L.
intros; discriminate.
simpl in L; absurd (1 <= 0); auto with arith;
refine (le_trans _ L); apply le_trans with (size t); auto with arith;
apply size_ge_one.
intros; discriminate.
simpl in L; assert (Sl : list_size size l <= m).
apply le_S_n; refine (le_trans  _ L); 
apply (plus_le_compat_r 1 (size t) (list_size size l));
apply size_ge_one.
destruct t as [v' | f' l']; rewrite var_in_term_list_equation.
generalize (eq_var_bool_ok v v'); case (eq_var_bool v v'); [intros v_eq_v' _ | intro v_diff_v'].
left; subst; left; trivial.
intro H; destruct (IHm _ Sl H) as [v_in_l | [t [t_in_l H']]].
left; right; trivial.
right; exists t; split; trivial; right; trivial.
assert (Sl' : list_size size l' <= m).
apply le_S_n; refine (le_trans _ L); rewrite size_unfold; simpl;
apply le_n_S; auto with arith.
generalize (IHm _ Sl'); destruct (var_in_term_list v l').
intro H; destruct (H (refl_equal _)) as [v_in_l' | [t [t_in_l' H']]].
right; exists (Term f' l'); split.
left; trivial.
left; trivial.
right; exists (Term f' l'); split.
left; trivial.
apply trans_clos_is_trans with t; trivial; left; trivial.
intros _; generalize (IHm _ Sl); destruct (var_in_term_list v l).
intro H; destruct (H (refl_equal _)) as [v_in_l' | [t [t_in_l' H']]].
left; right; trivial.
right; exists t; split; trivial; right; trivial.
intros; discriminate.
destruct t1 as [v1 | f1 l1]; destruct t2 as [v2 | f2 l2]; trivial.
generalize (H v1 f2 l2); destruct (var_in_term_list v1 l2); 
intro H'; trivial; apply H'; trivial.
generalize (H v2 f1 l1); destruct (var_in_term_list v2 l1); 
intro H'; trivial; apply H'; trivial.
(* 1/2 t1 = Term f1 l1, t2 = Term f2 l2 *)
generalize (list_exists_option_is_sound 
  (fun t : term =>
        match rpo_eval rpo_infos n t (Term f2 l2) with
        | Some Equivalent => Some true
        | Some Less_than => Some false
        | Some Greater_than => Some true
        | Some Uncomparable => Some false
        | None => None (A:=bool)
        end) l1);
destruct (list_exists_option
     (fun t : term =>
      match rpo_eval rpo_infos n t (Term f2 l2) with
      | Some Equivalent => Some true
      | Some Less_than => Some false
      | Some Greater_than => Some true
      | Some Uncomparable => Some false
      | None => None (A:=bool)
      end) l1) as [ [ | ] | ].
(* 1/4 there is a term in l1 which is greater than (Term f2 l2) *)
intros [t1 [t1_in_l1 t1_gt_f2l2]]; simpl; 
apply Subterm with t1; trivial.
apply in_impl_mem; trivial.
exact Eq.
generalize (IHn t1 (Term f2 l2)); 
destruct (rpo_eval rpo_infos n t1 (Term f2 l2)) as [ [ | | | ] | ]; try discriminate.
intro H1; apply Equiv; apply (equiv_sym _ _ equiv_equiv); trivial.
intro H1; apply Lt; trivial.
(* 1/3 there are no terms in l1 which are greater than (Term f2 l2) *)
intros _;
generalize (list_exists_option_is_sound 
  (fun t : term =>
        match rpo_eval rpo_infos n (Term f1 l1) t with
        | Some Equivalent => Some true
        | Some Less_than => Some true
        | Some Greater_than => Some false
        | Some Uncomparable => Some false
        | None => None (A:=bool)
        end) l2);
destruct (list_exists_option
     (fun t : term =>
      match rpo_eval rpo_infos n (Term f1 l1) t with
      | Some Equivalent => Some true
      | Some Less_than => Some true
      | Some Greater_than => Some false
      | Some Uncomparable => Some false
      | None => None (A:=bool)
      end) l2) as [ [ | ] | ].
(* 1/5 there is a term in l2 which is greater than (Term f1 l1) *)
intros [t2 [t2_in_l2 t2_gt_f1l1]]; simpl; apply Subterm with t2; trivial.
apply in_impl_mem; trivial.
exact Eq.
generalize (IHn (Term f1 l1) t2); 
destruct (rpo_eval rpo_infos n (Term f1 l1) t2) as [ [ | | | ] | ]; try discriminate.
intro; apply Equiv; trivial.
intro; apply Lt; trivial.
(* 1/4 there are no terms in l2 which are greater than (Term f1 l1) *)
intros _;
generalize (prec_eval_is_sound f1 f2); destruct (prec_eval f1 f2).
(* 1/7 f1 = f2 *)
intro f1_eq_f2. 
assert (Sf1:status P f1 = status P f2).
 apply prec_eq_status; trivial.
destruct (status P f2). rewrite Sf1.
(* 1/8 f1 has a Lex status *)
simpl; assert (H' := lexico_eval_is_sound (rpo_eval rpo_infos n) (Term f1 l1)
                                (Term f2 l2) l1 l2).
destruct (lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f2 l2) l1 l2) as [ [ | | | ] | ].
(* 1/12 lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f1 l2) l1 l2 = Some Equivalent *)
destruct H' as [ll [E_ll [H1 H2]]].
rewrite (f_equal (@length _) H1); rewrite (f_equal (@length _) H2); do 2 rewrite length_map.
rewrite <- beq_nat_refl; simpl.
apply (@Eq_lex f1 f2 l1 l2 Sf1). assert (H3:= prec_eq_status). assert (H3':= H3 _ P f1 f2). assert (H4: status P f1 = status P f2). apply H3'; trivial. rewrite <- H4; trivial. trivial.
subst l1 l2; induction ll as [ | [t1 t2] ll]; simpl.
apply Eq_list_nil.
apply Eq_list_cons.
generalize (IHn t1 t2); rewrite (E_ll _ _ (or_introl _ (refl_equal _))); intro; assumption.
apply IHll; intros; apply E_ll; right; assumption.
(* 1/11 lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f1 l2) l1 l2 = Some Less_than *)
case_eq (var_eq_bool (length l1) (length l2)); simpl.
intro L; apply (@Top_eq_lex rpo_infos.(bb) f1 f2 l2 l1 Sf1).  assert (H3:= prec_eq_status). assert (H3':= H3 _ P f1 f2). assert (H4: status P f1 = status P f2). apply H3'; trivial. rewrite <- H4; trivial. trivial.
left; apply sym_eq; apply beq_nat_true; assumption.
destruct H' as [[H1 H2] | [[ll [t2 [l2' [ _ [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
destruct l2 as [ | a2 l2]; [apply False_rect; apply H2; apply refl_equal | subst l1; discriminate].
subst l1 l2; rewrite length_app in L; do 2 rewrite length_map in L.
apply False_rect; generalize (beq_nat_true _ _ L); clear L; induction ll as [ | [u1 u2] ll].
discriminate.
intro L; injection L; clear L; intro L; apply IHll; assumption.
clear L H'; subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 1; generalize (IHn t1 t2); rewrite Ht; intro; assumption.
simpl; constructor 2.
generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (refl_equal _))); intro; assumption.
apply IHll; intros; apply Hll; right; assumption.
destruct H' as [[H1 H2] | [[ll [t2 [l2' [_ [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
intros; subst l1; contradiction.
subst l1 l2; rewrite length_app in L; do 2 rewrite length_map in L.
apply False_rect; generalize (beq_nat_true _ _ L); clear L; induction ll as [ | [u1 u2] ll].
discriminate.
intro L; injection L; clear L; intro L; apply IHll; assumption.
intros u u_in_l1; rewrite mem_in_eq in u_in_l1; destruct u_in_l1 as [u' [u_eq_u' u'_in_l1]].
destruct (H' _ u'_in_l1) as [ [u2 [u2_in_l2 u'_le_u2]] | H''].
apply Subterm with u2.
apply in_impl_mem; trivial.
intros; apply Eq.
destruct u'_le_u2 as [u'_eq_u2 | u'_lt_u2].
left; apply (equiv_trans _ _ equiv_equiv) with u'; trivial.
generalize (IHn u' u2); rewrite u'_eq_u2; intro; assumption.
right; rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn u' u2); rewrite u'_lt_u2; intro; assumption.
rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn (Term f2 l2) u'); rewrite H''; intro; assumption.
intros _; generalize (leb_complete (length l1) (rpo_infos.(bb))); case (leb (length l1) rpo_infos.(bb)); [idtac | simpl; trivial].
generalize (leb_complete (length l2) (rpo_infos.(bb))); case (leb (length l2) (bb rpo_infos)); simpl; [idtac | trivial].
intros L2 L1; apply (@Top_eq_lex rpo_infos.(bb) f1 f2 l2 l1 Sf1).  assert (H3:= prec_eq_status). assert (H3':= H3 _ P f1 f2). assert (H4: status P f1 = status P f2). apply H3'; trivial. rewrite <- H4; trivial. trivial.
right; split; [apply L1 | apply L2]; apply refl_equal.
clear L1 L2; destruct H' as [[H1 H2] | [[ll [t2 [l2' [Hll [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
subst l1; destruct l2 as [ | a2 l2]; [apply False_rect; apply H2; apply refl_equal | constructor 3].
subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 3.
simpl; constructor 2.
generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (refl_equal _))); intro; assumption.
apply IHll; intros; apply Hll; right; assumption.
clear H'; subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 1; generalize (IHn t1 t2); rewrite Ht; intro; assumption.
simpl; constructor 2.
generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (refl_equal _))); intro; assumption.
apply IHll; intros; apply Hll; right; assumption.
clear L1 L2; destruct H' as [[H1 H2] | [[ll [t2 [l2' [Hll [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
intros; subst l1; contradiction.
intros u u_in_l1; rewrite mem_in_eq in u_in_l1; destruct u_in_l1 as [u' [u_eq_u' u'_in_l1]].
subst l1; rewrite in_map_iff in u'_in_l1; destruct u'_in_l1 as [[u1 u2] [H1 K2]].
apply Subterm with u2.
subst l2; rewrite <- mem_or_app; left; apply in_impl_mem.
apply Eq.
rewrite in_map_iff; exists (u1,u2); split; trivial.
simpl in H1; subst u1; left; apply (equiv_trans _ _ equiv_equiv) with u'; trivial.
generalize (IHn u' u2); rewrite (Hll _ _ K2); intro; assumption.
intros u u_in_l1; rewrite mem_in_eq in u_in_l1; destruct u_in_l1 as [u' [u_eq_u' u'_in_l1]].
destruct (H' _ u'_in_l1) as [ [u2 [u2_in_l2 u'_le_u2]] | H''].
apply Subterm with u2.
apply in_impl_mem; trivial.
intros; apply Eq.
destruct u'_le_u2 as [u'_eq_u2 | u'_lt_u2].
left; apply (equiv_trans _ _ equiv_equiv) with u'; trivial.
generalize (IHn u' u2); rewrite u'_eq_u2; intro; assumption.
right; rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn u' u2); rewrite u'_lt_u2; intro; assumption.
rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn (Term f2 l2) u'); rewrite H''; intro; assumption.
(* 1/10 lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f1 l2) l1 l2 = Some Greater_than *)
case_eq (var_eq_bool (length l1) (length l2)); simpl.
assert (Sf2: status P f2 = Lex).
 assert (H3:= prec_eq_status). assert (H3':= H3 _ P f1 f2). assert (H4: status P f1 = status P f2). apply H3'; trivial. rewrite <- H4; trivial. trivial.
intro L; apply (@Top_eq_lex rpo_infos.(bb) f2 f1 l1 l2 Sf2). trivial. apply prec_eq_sym; trivial.
left; apply beq_nat_true; assumption.
destruct H' as [[H1 H2] | [[ll [t1 [l1' [ _ [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
destruct l1 as [ | a1 l1]; [apply False_rect; apply H1; apply refl_equal | subst l2; discriminate].
subst l1 l2; rewrite length_app in L; do 2 rewrite length_map in L.
apply False_rect; generalize (beq_nat_true _ _ L); clear L; induction ll as [ | [u1 u2] ll].
discriminate.
intro L; injection L; clear L; intro L; apply IHll; assumption.
clear L H'; subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 1; generalize (IHn t1 t2); rewrite Ht; intro; assumption.
simpl; constructor 2.
apply (equiv_sym _ _ equiv_equiv); generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (refl_equal _))); intro; assumption.
apply IHll; intros; apply Hll; right; assumption.
destruct H' as [[H1 H2] | [[ll [t1 [l1' [_ [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
intros; subst l2; contradiction.
subst l1 l2; rewrite length_app in L; do 2 rewrite length_map in L.
apply False_rect; generalize (beq_nat_true _ _ L); clear L; induction ll as [ | [u1 u2] ll].
discriminate.
intro L; injection L; clear L; intro L; apply IHll; assumption.
intros u u_in_l2; rewrite mem_in_eq in u_in_l2; destruct u_in_l2 as [u' [u_eq_u' u'_in_l2]].
destruct (H' _ u'_in_l2) as [ [u1 [u1_in_l1 u'_le_u1]] | H''].
apply Subterm with u1.
apply in_impl_mem; trivial.
intros; apply Eq.
destruct u'_le_u1 as [u'_eq_u1 | u'_lt_u1].
left; apply (equiv_trans _ _ equiv_equiv) with u'; trivial.
apply (equiv_sym _ _ equiv_equiv); generalize (IHn u1 u'); rewrite u'_eq_u1; intro; assumption.
right; rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn u1 u'); rewrite u'_lt_u1; intro; assumption.
rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn (Term f1 l1) u'); rewrite H''; intro; assumption.
intros _; generalize (leb_complete (length l1) (rpo_infos.(bb))); case (leb (length l1) rpo_infos.(bb)); [idtac | simpl; trivial].
generalize (leb_complete (length l2) (rpo_infos.(bb))); case (leb (length l2) (bb rpo_infos)); simpl; [idtac | trivial].
 assert (H3:= prec_eq_status). assert (H3':= H3 _ P f1 f2). assert (H4: status P f1 = status P f2). apply H3'; trivial. assert (Sf2: status P f2 = Lex). rewrite <- H4; trivial.
intros L2 L1; apply (@Top_eq_lex rpo_infos.(bb) f2 f1 l1 l2 Sf2). trivial. apply prec_eq_sym;
trivial.
right; split; [apply L2 | apply L1]; apply refl_equal.
clear L1 L2; destruct H' as [[H1 H2] | [[ll [t1 [l2' [Hll [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
subst l2; destruct l1 as [ | a1 l2]; [apply False_rect; apply H1; apply refl_equal | constructor 3].
subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 3.
simpl; constructor 2.
apply (equiv_sym _ _ equiv_equiv); generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (refl_equal _))); intro; assumption.
apply IHll; intros; apply Hll; right; assumption.
clear H'; subst l1 l2; induction ll as [ | [u1 u2] ll].
simpl; constructor 1; generalize (IHn t1 t2); rewrite Ht; intro; assumption.
simpl; constructor 2.
apply (equiv_sym _ _ equiv_equiv); generalize (IHn u1 u2); rewrite (Hll _ _ (or_introl _ (refl_equal _))); intro; assumption.
apply IHll; intros; apply Hll; right; assumption.
clear L1 L2; destruct H' as [[H1 H2] | [[ll [t1 [l1' [Hll [H1 H2]]]]] | [ll [t1 [t2 [l1' [l2' [Hll [Ht [H' [H1 H2]]]]]]]]]]].
intros; subst l2; contradiction.
intros u u_in_l2; rewrite mem_in_eq in u_in_l2; destruct u_in_l2 as [u' [u_eq_u' u'_in_l2]].
subst l2; rewrite in_map_iff in u'_in_l2; destruct u'_in_l2 as [[u1 u2] [K1 K2]].
apply Subterm with u1.
subst l1; rewrite <- mem_or_app; left; apply in_impl_mem.
apply Eq.
rewrite in_map_iff; exists (u1,u2); split; trivial.
simpl in K1; subst u2; left; apply (equiv_trans _ _ equiv_equiv) with u'; trivial.
apply (equiv_sym _ _ equiv_equiv); generalize (IHn u1 u'); rewrite (Hll _ _ K2); intro; assumption.
intros u u_in_l2; rewrite mem_in_eq in u_in_l2; destruct u_in_l2 as [u' [u_eq_u' u'_in_l2]].
destruct (H' _ u'_in_l2) as [ [u1 [u1_in_l1 u'_le_u1]] | H''].
apply Subterm with u1.
apply in_impl_mem; trivial.
intros; apply Eq.
destruct u'_le_u1 as [u'_eq_u1 | u'_lt_u1].
left; apply (equiv_trans _ _ equiv_equiv) with u'; trivial.
apply (equiv_sym _ _ equiv_equiv); generalize (IHn u1 u'); rewrite u'_eq_u1; intro; assumption.
right; rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn u1 u'); rewrite u'_lt_u1; intro; assumption.
rewrite (equiv_rpo_equiv_2 _ u_eq_u'); generalize (IHn (Term f1 l1) u'); rewrite H''; intro; assumption.
(* 1/9 lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f1 l2) l1 l2 = Some Uncomparable *)
case (var_eq_bool (length l1) (length l2)
      || leb (length l1) (bb rpo_infos) && leb (length l2) (bb rpo_infos)); trivial.
(* 1/8 lexico_eval (rpo_eval rpo_infos n) (Term f1 l1) (Term f1 l2) l1 l2 = None *)
case (var_eq_bool (length l1) (length l2)
      || leb (length l1) (bb rpo_infos) && leb (length l2) (bb rpo_infos)); trivial.
(* 1/7 f1 has a Mul status *)
 assert (H3:= prec_eq_status). assert (H3':= H3 _ P f1 f2). assert (H4: status P f1 = status P f2). apply H3'; trivial. assert (Sf2: status P f2 = Mul). rewrite <- H4; trivial. 
simpl; assert (H' := remove_equiv_eval_list_is_sound (equiv_eval rpo_infos n) l1 l2).
rewrite Sf1.
destruct (remove_equiv_eval_list (equiv_eval rpo_infos n) l1 l2) as [ [[ | t1' l1'] [ | t2' l2']] | ].
destruct H' as [ll [E_ll [P1 [P2 _]]]]. apply (@Eq_mul f1 f2 l1 l2 Sf1); trivial.
simpl in P1; simpl in P2. 
apply permut0_trans with (map (fun st : term * term => fst st) ll); trivial. apply equiv_equiv.
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.
apply permut0_trans with (map (fun st : term * term => snd st) ll); trivial. apply equiv_equiv.
assert (E_ll' : forall t1 t2, In (t1,t2) ll -> equiv t1 t2).
intros t1 t2 t1t2_in_ll; 
assert (H' := equiv_eval_is_sound_weak rpo_infos n t1 t2);
rewrite (E_ll t1 t2 t1t2_in_ll) in H'; apply H'; trivial.
clear E_ll P1 P2; induction ll as [ | [t1 t2] ll].
reflexivity.
simpl; rewrite <- permut0_cons.
apply IHll.
intros; apply E_ll'; right; trivial. apply equiv_equiv.
apply E_ll'; left; trivial.
symmetry; 
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.
destruct H' as [ll [E_ll [P1 [P2 _]]]].
apply Top_eq_mul; trivial.
apply (@List_mul _ t2' l2' nil l1); trivial.
reflexivity.
transitivity ((t2' :: l2') ++ (map (fun st : term * term => snd st) ll)).
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.
rewrite app_comm_cons; rewrite <- permut_app1.
transitivity (map (fun st : term * term => fst st) ll).
symmetry.
assert (E_ll' : forall t1 t2, In (t1,t2) ll -> equiv t1 t2).
intros t1 t2 t1t2_in_ll; 
assert (H' := equiv_eval_is_sound_weak rpo_infos n t1 t2);
rewrite (E_ll t1 t2 t1t2_in_ll) in H'; apply H'; trivial.
clear E_ll P1 P2; induction ll as [ | [t1 t2] ll].
reflexivity.
simpl; rewrite <- permut0_cons.
apply IHll.
intros; apply E_ll'; right; trivial. apply equiv_equiv.
apply E_ll'; left; trivial.
symmetry; 
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity. apply equiv_equiv.
intros; contradiction.
destruct H' as [ll [E_ll [P1 [P2 _]]]].
apply Top_eq_mul; trivial. apply prec_eq_sym; trivial.
apply (@List_mul _ t1' l1' nil l2); trivial.
reflexivity.
transitivity ((t1' :: l1') ++ (map (fun st : term * term => fst st) ll)).
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.
rewrite app_comm_cons; rewrite <- permut_app1.
transitivity (map (fun st : term * term => snd st) ll).
assert (E_ll' : forall t1 t2, In (t1,t2) ll -> equiv t1 t2).
intros t1 t2 t1t2_in_ll; 
assert (H' := equiv_eval_is_sound_weak rpo_infos n t1 t2);
rewrite (E_ll t1 t2 t1t2_in_ll) in H'; apply H'; trivial.
clear E_ll P1 P2; induction ll as [ | [t1 t2] ll].
reflexivity.
simpl; rewrite <- permut0_cons.
apply IHll.
intros; apply E_ll'; right; trivial. apply equiv_equiv.
apply E_ll'; left; trivial.
symmetry; 
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.  apply equiv_equiv.
intros; contradiction.
assert (H'' := mult_eval_is_sound_weak (rpo_eval rpo_infos n) (t1' :: l1') (t2' :: l2')).
destruct (mult_eval (rpo_eval rpo_infos n) (t1' :: l1') (t2' :: l2')) as [ [ | | | ] | ].
contradiction.
destruct H' as [ll [E_ll [P1 [P2 _]]]].
assert (E_ll' : forall t1 t2, In (t1,t2) ll -> equiv t1 t2).
intros t1 t2 t1t2_in_ll; 
assert (H' := equiv_eval_is_sound_weak rpo_infos n t1 t2);
rewrite (E_ll t1 t2 t1t2_in_ll) in H'; apply H'; trivial.
apply Top_eq_mul; trivial.
apply (@List_mul _ t2' l2' (t1' :: l1') (map (fun st : term * term => fst st) ll)); trivial.
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.
transitivity ((t2' :: l2') ++ map (fun st : term * term => snd st) ll).
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.
rewrite app_comm_cons; rewrite <- permut_app1.
clear E_ll P1 P2; induction ll as [ | [t1 t2] ll].
reflexivity.
simpl; rewrite <- permut0_cons.
apply IHll.
intros; apply E_ll'; right; trivial. apply equiv_equiv.
symmetry; apply E_ll'; left; trivial. apply equiv_equiv.
intros u1 u1_mem_l1'.
destruct (mem_split_set _ _ equiv_bool_ok _ _ u1_mem_l1') as [u1' [k1 [k1' [u1_eq_u1' [H' _]]]]].
simpl in u1_eq_u1'; simpl in H'.
assert (u1'_in_l1' : In u1' (t1' :: l1')).
rewrite H'; apply in_or_app; right; left; trivial.
destruct (H'' _ u1'_in_l1') as [u2 [u2_in_l2' u1_lt_u2]];
exists u2; split.
apply in_impl_mem; trivial.
exact Eq.
assert (H''' := IHn u2 u1').
rewrite u1_lt_u2 in H'''.
rewrite (equiv_rpo_equiv_2 _ u1_eq_u1'); trivial.
destruct H' as [ll [E_ll [P1 [P2 _]]]].
assert (E_ll' : forall t1 t2, In (t1,t2) ll -> equiv t1 t2).
intros t1 t2 t1t2_in_ll; 
assert (H' := equiv_eval_is_sound_weak rpo_infos n t1 t2);
rewrite (E_ll t1 t2 t1t2_in_ll) in H'; apply H'; trivial.
(* destruct (equiv_swap _ equiv ll E_ll') as [ll' [E_ll'' [H1 [H2 H3]]]]. *)
apply Top_eq_mul; trivial. apply prec_eq_sym; trivial.
apply (@List_mul _ t1' l1' (t2' :: l2') (map (fun st : term * term => fst st) ll)); trivial.
transitivity ((t2' :: l2') ++ map (fun st : term * term => snd st) ll).
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.
rewrite <- permut_app1.
clear E_ll P1 P2; induction ll as [ | [t1 t2] ll].
reflexivity.
simpl; rewrite <- permut0_cons.
apply IHll.
intros; apply E_ll'; right; trivial. apply equiv_equiv.
symmetry; apply E_ll'; left; trivial. apply equiv_equiv.
apply permut_impl with (@eq term); trivial; intros; subst; reflexivity.
intros u2 u2_mem_l2'.
destruct (mem_split_set _ _ equiv_bool_ok _ _ u2_mem_l2') as [u2' [k2 [k2' [u2_eq_u2' [H' _]]]]].
simpl in u2_eq_u2'; simpl in H'.
assert (u2'_in_l2' : In u2' (t2' :: l2')).
rewrite H'; apply in_or_app; right; left; trivial.
destruct (H'' _ u2'_in_l2') as [u1 [u1_in_l1' u2_lt_u1]];
exists u1; split.
apply in_impl_mem; trivial.
exact Eq.
assert (H''' := IHn u1 u2').
rewrite u2_lt_u1 in H'''.
rewrite (equiv_rpo_equiv_2 _ u2_eq_u2'); trivial.
trivial.
trivial.
trivial.
(* 1/6 f1 < f2 *)
intro f1_lt_f2; simpl.
generalize (list_forall_option_is_sound
      (fun t : term =>
       match rpo_eval rpo_infos n t (Term f2 l2) with
       | Some Equivalent => Some false
       | Some Less_than => Some true
       | Some Greater_than => Some false
       | Some Uncomparable => Some false
       | None => None (A:=bool)
       end) l1);
destruct (list_forall_option
      (fun t : term =>
       match rpo_eval rpo_infos n t (Term f2 l2) with
       | Some Equivalent => Some false
       | Some Less_than => Some true
       | Some Greater_than => Some false
       | Some Uncomparable => Some false
       | None => None (A:=bool)
       end) l1) as [ [ | ] | ].
intros l1_lt_s2; apply Top_gt; trivial.
intros t1 t1_mem_l1;
destruct (mem_split_set _ _ equiv_bool_ok _ _ t1_mem_l1) as [t1' [k1 [k1' [t1_eq_t1' [H' _]]]]].
simpl in t1_eq_t1'; simpl in H'.
assert (t1'_in_l1 : In t1' l1).
rewrite H'; apply in_or_app; right; left; trivial.
rewrite (equiv_rpo_equiv_2 _ t1_eq_t1').
assert (H'' := l1_lt_s2 t1' t1'_in_l1).
assert (H''' := IHn t1' (Term f2 l2));
destruct (rpo_eval rpo_infos n t1' (Term f2 l2)) as [ [ | | | ] | ]; trivial; discriminate.
trivial.
trivial.
(* 1/5 f2 < f1 *)
intro f2_lt_f1; simpl.
generalize (list_forall_option_is_sound
      (fun t : term =>
       match rpo_eval rpo_infos n (Term f1 l1) t with
       | Some Equivalent => Some false
       | Some Less_than => Some false
       | Some Greater_than => Some true
       | Some Uncomparable => Some false
       | None => None (A:=bool)
       end) l2); 
destruct (list_forall_option
      (fun t : term =>
       match rpo_eval rpo_infos n (Term f1 l1) t with
       | Some Equivalent => Some false
       | Some Less_than => Some false
       | Some Greater_than => Some true
       | Some Uncomparable => Some false
       | None => None (A:=bool)
       end) l2) as [ [ | ] | ].
intros s1_gt_l2; apply Top_gt; trivial.
intros t2 t2_mem_l2; 
destruct (mem_split_set _ _ equiv_bool_ok _ _ t2_mem_l2) as [t2' [k2 [k2' [t2_eq_t2' [H' _]]]]].
simpl in t2_eq_t2'; simpl in H'.
assert (t2'_in_l2 : In t2' l2).
rewrite H'; apply in_or_app; right; left; trivial.
rewrite (equiv_rpo_equiv_2 _ t2_eq_t2').
assert (H'' := s1_gt_l2 t2' t2'_in_l2).
assert (H''' := IHn (Term f1 l1) t2');
destruct (rpo_eval rpo_infos n (Term f1 l1) t2') as [ [ | | | ] | ]; trivial; discriminate.
trivial.
trivial.
simpl; trivial.
simpl; trivial.
simpl; trivial.
trivial.
Qed.

  (* The proof of [rpo_add_context] used in the proof of [cc_succ_rpo] in Coccinelle2.v *)

  Lemma rpo_add_context :
    forall bb p ctx s t, rpo bb s t -> is_a_pos ctx p = true -> 
      rpo bb (replace_at_pos ctx s p) (replace_at_pos ctx t p).

  Proof.
    intros bb p; induction p as [ | i p ]; intros ctx s t R H; trivial;
      destruct ctx as [ v | f l ].
    discriminate.
    assert (Status : forall g, g = f -> status P g = status P f).
    intros; subst; trivial.
    do 2 (rewrite replace_at_pos_unfold);
      destruct (status P f); generalize (Status f (refl_equal _)); clear Status; 
        intro Status.
      (* 1/2 Lex case *)
    apply Top_eq_lex; trivial. 
    apply prec_eq_refl.
    left; clear; revert l; induction i as [ | i]; intros [ | a l]; simpl; trivial.
    rewrite IHi; apply refl_equal.
    generalize i H; clear i H; induction l as [ | u l]; intros i H; simpl.
    simpl in H; destruct i; discriminate.
    destruct i as [ | i].
    apply List_gt; trivial.
    simpl in H; apply IHp; trivial.
    apply List_eq.
    reflexivity.
    apply IHl; trivial.
    intros s' s'_mem_ls;
      assert (H' : exists s'', rpo_eq bb s' s'' /\ mem equiv s'' (replace_at_pos_list l t i p)). 
    generalize i H s' s'_mem_ls; clear i H s' s'_mem_ls; 
      induction l as [ | u l]; intros i H; simpl.
    intros; contradiction.
    destruct i as [ | i].
    intros s' [s'_eq_s'' | s'_mem_l].
    exists (replace_at_pos u t p); split.
    apply Lt; rewrite (equiv_rpo_equiv_2 _ s'_eq_s'').
    apply IHp; trivial.
    left; reflexivity.
    exists s'; split.
    apply Equiv; apply Eq.
    right; trivial.
    intros s' [s'_eq_u | s'_mem_l].
    exists u; split.
    apply Equiv; trivial.
    left; reflexivity.
    simpl in IHl; simpl in H.
    destruct (IHl i H s' s'_mem_l) as [s'' [s'_le_s'' s''_mem_l']].
    exists s''; split; trivial.
    right; trivial.
    destruct H' as [s'' [s'_le_s'' s''_mem_l']].
    apply Subterm with s''; trivial.
      (* 1/1 Mul case *)
    apply Top_eq_mul; trivial.
    apply prec_eq_refl.
    generalize i H; clear i H; induction l as [ | u l]; intros i H; simpl.
    simpl in H; destruct i; discriminate.
    destruct i as [ | i].
    apply (@List_mul bb (replace_at_pos u t p) nil (replace_at_pos u s p :: nil) l); reflexivity || auto.
    intros b [b_eq_s' | b_mem_nil].
    exists (replace_at_pos u t p); split.
    left; reflexivity.
    rewrite (equiv_rpo_equiv_2 _ b_eq_s').
    apply IHp; trivial.
    contradiction.
    simpl in IHl; simpl in H; assert (H' := IHl i H).
    inversion H' as [a lg ls lc l' l'' ls_lt_alg P1 P2]; subst.
    apply (@List_mul bb a lg ls (u :: lc)); trivial.
    rewrite <- permut0_cons_inside; trivial; try reflexivity. apply equiv_equiv.
    rewrite app_comm_cons.
    rewrite <- permut0_cons_inside; trivial; try reflexivity. apply equiv_equiv.
  Qed.

  (* The proof of [equiv_add_context] used in the proof of [cc_equiv_aterm] in Coccinelle2.v *)

  (** ** RPO is compatible with adding context. *)

  Lemma equiv_add_context :
    forall p ctx s t, equiv s t -> is_a_pos ctx p = true -> 
      equiv (replace_at_pos ctx s p) (replace_at_pos ctx t p).

  Proof.
    intro p; induction p as [ | i p ]; intros ctx s t R H; trivial;
      destruct ctx as [ v | f l ].
    discriminate.
    assert (Status : forall g, g = f -> status P g = status P f).
    intros; subst; trivial.
    do 2 (rewrite replace_at_pos_unfold);
      destruct (status P f); generalize (Status f (refl_equal _)); clear Status; 
        intro Status.
      (* 1/2 Lex case *)
    apply Eq_lex; trivial.
    apply prec_eq_refl.
    generalize i H; clear i H; induction l as [ | u l]; intros i H; simpl. 
    apply Eq_list_nil.
    destruct i as [ | i].
    apply Eq_list_cons. 
    simpl in H; apply IHp; trivial.
    generalize l; intro l'; induction l' as [ | u' l'].
    apply Eq_list_nil.
    apply Eq_list_cons; trivial; reflexivity.
    apply Eq_list_cons.
    reflexivity.
    apply IHl; trivial.
      (* 1/1 Mul case *)
    apply Eq_mul; trivial.
    apply prec_eq_refl.
    generalize i H; clear i H; induction l as [ | u l]; intros i H; simpl; reflexivity || auto.
    destruct i as [ | i].
    rewrite <- permut0_cons.
    reflexivity.
    apply equiv_equiv. 
    simpl in H; apply IHp; trivial.
    rewrite <- permut0_cons.
    apply IHl; trivial. apply equiv_equiv.
    reflexivity.
  Qed.

End RPO.
