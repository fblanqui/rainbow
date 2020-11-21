(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-02-22, 2009-10-20 (rpo)

convert CoLoR terms into Coccinelle terms 
*)

Set Implicit Arguments.

Require Import Relation_Definitions Setoid Bool Arith ATerm VecUtil
EqUtil LogicUtil List more_list term_spec NatUtil.

(* Define symbol. *)

Section symb.

  Variable Sig: Signature.

  Definition A_symb       := symbol Sig.
  Definition eq_bool_symb := @beq_symb Sig.

  Lemma eq_bool_symb_ok : forall a1 a2,
    match eq_bool_symb a1 a2 with
      | true  => a1 = a2 
      | false => ~ a1 = a2
    end.

  Proof.
    intros a1 a2. unfold eq_bool_symb. case_beq_symb Sig a1 a2. auto.
    rewrite <- (beq_ko (@beq_symb_ok Sig)). apply H.
   Qed.

  Definition symb_arity (f: Sig) : arity_type  := Free (ASignature.arity f).

End symb.

(* Define var *)

Section var.

  Definition var         := nat.
  Definition var_eq_bool := beq_nat.

  Lemma var_eq_bool_ok: forall a1 a2,
    match var_eq_bool a1 a2 with 
      | true => a1 = a2 
      | false => ~ a1 = a2
    end.

  Proof.
    intros a1 a2. unfold var_eq_bool. case_beq_nat a1 a2. auto.
    rewrite <- (beq_ko beq_nat_ok). hyp.
  Qed.

End var.

(* [term] in cocc *)

Section Term.

  Variable Sig: Signature.
  
  Notation A               := (symbol Sig).
  Notation eq_symb_bool    := (eq_bool_symb Sig).
  Notation eq_symb_bool_ok := (eq_bool_symb_ok Sig).
  Notation eq_var_bool     := var_eq_bool.
  Notation eq_var_bool_ok  := var_eq_bool_ok.
  Notation symbol          := (symbol Sig).
  Notation variable        := nat (only parsing).
  
  Inductive term : Type :=
  | Var  : variable -> term
  | Term : symbol   -> list term -> term.
  
  Fixpoint size (t: term) : nat :=
    match t with
      | Var v    => 1
      | Term _ l =>
        let size_list :=
          (fix size_list (l : list term) {struct l} : nat :=
            match l with
              | nil     => 0
              | t :: lt => size t + size_list lt
            end) in
          1 + size_list l
    end.

   Definition size_unfold :
    forall t,
      size t = match t with
                 | Var _    => 1
                 | Term f l => 1 + list_size size l
               end.
  Proof.
    intro t; case t; clear t.
    intro v; reflexivity.
    intros f l; simpl; apply f_equal.
    revert l; fix 1.
    intro l; case l; clear l.
    reflexivity.
    intros t l; simpl; rewrite size_unfold; reflexivity.
  Defined.

  Lemma size_ge_one : forall t, 1 <= size t.
  Proof.
    intro t; case t; clear t.
    intro v; apply le_n.
    intros f l; rewrite size_unfold; apply le_n_S; apply le_O_n.
  Qed.

   Function var_in_term_list (x : variable) (l : list term) 
    { measure (list_size size) l } : bool :=
    match l with
      | nil              => false
      | (Var y) :: l     => orb (eq_var_bool x y)       (var_in_term_list x l) 
      | (Term _ ll) :: l => orb (var_in_term_list x ll) (var_in_term_list x l)
    end.
  Proof.
    intros _ l t l' y H1 H2;  simpl; auto with arith.
    intros _ l t l' f ll H1 H2; simpl; auto with arith.
    intros _ l t l' f ll H1 H2; simpl; apply lt_le_trans with (size (Term f ll)).
    rewrite size_unfold; simpl; auto with arith.
    simpl; auto with arith.
  Defined.

   Definition direct_subterm t1 t2 : Prop :=
    match t2 with
      | Var _    => False
      | Term _ l => In t1 l
    end.

  Definition size_direct_subterm :
    forall t1 t2, direct_subterm t1 t2 -> size t1 < size t2.

  Proof.
    intros t1 t2; unfold direct_subterm; case t2; clear t2.
    intros a Abs; elim Abs.
    intros f l; rewrite (size_unfold (Term f l)).
    revert t1 l; clear f; fix 2.
    intros t1 l; case l; clear l; simpl.
    intro Abs; elim Abs.
    intros t l t1_in_tl; case t1_in_tl; clear t1_in_tl.
    intro t_eq_t1; subst t1; apply le_n_S; apply le_plus_l.
    intro t_in_l; apply lt_le_trans with (1 + list_size size l).
    apply size_direct_subterm; assumption.
    apply le_n_S; apply le_plus_r.
  Defined.

  Fixpoint t_eq_bool (t1 t2 : term) : bool :=
    match t1, t2 with
      | Var v1,     Var v2     => eq_var_bool v1 v2
      | Var _,      Term _ _   => false
      | Term _ _,   Var _      => false  
      | Term f1 l1, Term f2 l2 =>
        if eq_symb_bool f1 f2 
          then
            let eq_bool_list :=
              (fix eq_bool_list (l1 l2: list term) {struct l1} : bool :=
                match l1, l2 with
                  | nil, nil      => true
                  | nil, (_ :: _) => false
                  | (_::_), nil   => false
                  | t1 :: k1, t2 :: k2 =>
                    if   t_eq_bool t1 t2
                    then eq_bool_list k1 k2
                    else false
                end) in
              eq_bool_list l1 l2
          else false
    end.
 
  Lemma t_eq_bool_ok : forall t1 t2,
    match t_eq_bool t1 t2 with 
      | true => t1 = t2
      | false => t1<> t2
    end.

    fix 1.
    intro t1; case t1; [intro v1 | intros f1 l1];
      (intro t2; case t2; [intro v2 | intros f2 l2]); simpl.
    generalize (eq_var_bool_ok v1 v2); case (eq_var_bool v1 v2).
    intros v1_eq_v2; rewrite v1_eq_v2; reflexivity.
    intros v1_diff_v2 v1_eq_v2; apply v1_diff_v2;
      injection v1_eq_v2; intro; assumption.
    discriminate.
    discriminate.
    generalize (eq_symb_bool_ok f1 f2); case (eq_symb_bool f1 f2).
    intros f1_eq_f2; rewrite f1_eq_f2.
    assert (eq_bool_list_ok : match (fix eq_bool_list (l0 l3 : list term) : bool :=
      match l0 with
        | nil => match l3 with
                   | nil => true
                   | _ :: _ => false
                 end
        | t3 :: k1 =>
          match l3 with
            | nil => false
            | t4 :: k2 => if t_eq_bool t3 t4 then eq_bool_list k1 k2 else false
          end
      end) l1 l2 with true => l1 = l2 | false => l1 <> l2 end).
    revert l1 l2; clear -t_eq_bool_ok.
    fix t_eq_bool_list_ok 1.
    intro l1; case l1; [idtac | intros t1 k1]; (intro l2; case l2; [idtac | intros t2 k2]).
    reflexivity.
    discriminate.
    discriminate.
    generalize (t_eq_bool_ok t1 t2); case (t_eq_bool t1 t2).
    intro t1_eq_t2; rewrite t1_eq_t2.
    generalize (t_eq_bool_list_ok k1 k2); 
      case ((fix eq_bool_list (l0 l3 : list term) : bool :=
        match l0 with
          | nil => match l3 with
                     | nil => true
                     | _ :: _ => false
                   end
          | t3 :: k3 =>
            match l3 with
              | nil => false
              | t4 :: k4 => if t_eq_bool t3 t4 then eq_bool_list k3 k4 else false
            end
        end) k1 k2).
    intro k1_eq_k2; rewrite k1_eq_k2; reflexivity.
    intros k1_diff_k2 tk1_eq_tk2; apply k1_diff_k2; injection tk1_eq_tk2; intro; assumption.
    intros t1_diff_t2 tk1_eq_tk2; apply t1_diff_t2; injection tk1_eq_tk2; intros; assumption.
    revert eq_bool_list_ok;
      case ((fix eq_bool_list (l0 l3 : list term) : bool :=
        match l0 with
          | nil =>
            match l3 with
              | nil => true
              | _ :: _ => false
            end
          | t3 :: k1 =>
            match l3 with
              | nil => false
              | t4 :: k2 =>
                if t_eq_bool t3 t4
                  then eq_bool_list k1 k2
                  else false
            end
        end) l1 l2).
    intro l1_eq_l2; rewrite l1_eq_l2; reflexivity.
    intros l1_diff_l2 fl1_eq_fl2; apply l1_diff_l2; injection fl1_eq_fl2; intros; assumption.
    intros f1_diff_f2 fl1_eq_fl2; apply f1_diff_f2; injection fl1_eq_fl2; intros; assumption.
  Defined.

  Definition term_A          := term.
  Definition term_eq_bool    := t_eq_bool.
  Definition term_eq_bool_ok := t_eq_bool_ok.

  Definition eq_term_dec : forall t t': term, {t=t'}+{t<>t'}.
  intros t t'; generalize (t_eq_bool_ok t t').
  case (t_eq_bool t t').
  intro t_eq_t'; left; assumption.
  intro t_diff_t'; right; assumption.
  Defined.

  (** ** Recursion on terms. *)

  Section Recursion.

    Variable P  : term      -> Type.
    Variable Pl : list term -> Type.

    Definition term_rec2 : (forall n t, size t <= n -> P t) -> forall t, P t.

    Proof.
      intros H t; apply (H (size t) t); apply le_n.
    Defined.

    Definition term_rec3 :
      (forall v, P (Var v)) -> (forall f l, (forall t, In t l -> P t)
        -> P (Term f l)) -> forall t, P t.

    Proof.
      intros Hv Halg. 
      fix 1.
      intro t;case t.
      exact Hv.
      intro a.
      intro l. apply Halg.
      revert l.
      fix term_list_rec_3 1  .
      intro l;case l.
      simpl;intros t0 abs;elim abs.
      intros t0 l0 t1 .
      simpl.
      intros H. 
      case (eq_term_dec t0 t1).
      intros t_eq_t1.
      rewrite <- t_eq_t1.
      apply term_rec3.
      intro t_eq_t1. assert (In t1 l0).
      case H. intro abs;elim t_eq_t1;exact abs.
      intro h;exact h.
      apply term_list_rec_3 with l0.
      exact H0.
    Defined.

  End Recursion.

  (** ** Substitutions. *)

  Definition substitution := list (variable * term).

  Fixpoint apply_subst (sigma : substitution) (t : term) {struct t} : term :=
    match t with
      | Var v => 
        match find eq_var_bool v sigma with
          | None         => t
          | Some v_sigma => v_sigma
        end
      | Term f l => Term f (map (apply_subst sigma) l)
    end.

  (** ** Positions in a term.*)

  Fixpoint is_a_pos (t : term) (p : list nat) {struct p}: bool :=
    match p with
  | nil => true
      | i :: q =>
        match t with
          | Var _    => false
          | Term _ l => 
            match nth_error l i with
              | Some ti => is_a_pos ti q
              | None    => false
            end
        end
    end.

  Fixpoint replace_at_pos (t u : term) (p : list nat) {struct p} : term :=
    match p with
      | nil    => u
      | i :: q =>
        match t with
          | Var _    => t
          | Term f l =>
            let replace_at_pos_list :=
              (fix replace_at_pos_list j (l : list term) {struct l}: list term :=
                match l with
                  | nil     => nil
                  | h :: tl =>
                    match j with
                      | O   => (replace_at_pos h u q) :: tl
                      | S k => h :: (replace_at_pos_list k tl)
                    end
                end) in
              Term f (replace_at_pos_list i l)
        end
    end.

  Fixpoint replace_at_pos_list (l : list term) (u : term) (i : nat) (p : list nat) 
    {struct l}: list term :=
    match l with
      | nil     => nil
      | h :: tl =>
        match i with
          | O   =>      (replace_at_pos h u p)         :: tl
          | S j => h :: (replace_at_pos_list tl  u j p)
        end
    end.

  Lemma replace_at_pos_unfold :
    forall f l u i q,
      replace_at_pos (Term f l) u (i :: q) = Term f (replace_at_pos_list l u i q).

  Proof.
    intros f l u i q; simpl; apply (f_equal (fun l => Term f l)); 
      generalize u i q; clear u i q; 
        induction l as [| t l]; intros u i q; trivial.
    simpl; destruct i as [ | i ]; trivial.
    rewrite <- IHl; trivial.
  Qed.

  Lemma replace_at_pos_list_replace_at_pos_in_subterm :
    forall l1 ui l2 u i p, length l1 = i ->
      replace_at_pos_list (l1 ++ ui :: l2) u i p = 
      l1 ++ (replace_at_pos ui u p) :: l2.

  Proof.
    intros l1; induction l1 as [ | u1 l1 ]; intros ui l2 u i p L; simpl in L.
    subst i; trivial.
    destruct i as [ | i ].
    discriminate.
    simpl; rewrite IHl1; trivial.
    inversion L; trivial.
  Qed.

End Term.