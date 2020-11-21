
(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-20
- Frederic Blanqui, 2005-02-24

polynomials with multiple variables and integer coefficients
*)

Set Implicit Arguments.

Require Import VecUtil LogicUtil List ZArith OrdSemiRing2 Arith.

(***********************************************************************)
(** monomials with n variables *)

Notation monom := (vector nat).

Lemma monom_eq_dec : forall n (m1 m2 : monom n), {m1 = m2} + {~m1 = m2}.

Proof.
intros. eapply eq_vec_dec. apply eq_nat_dec.
Defined.

(* monomial 1 *)
(*
Notation mone := (Vconst 0).

(* monomial x_i^k *)

Fixpoint mxi n : forall i, i < n -> nat -> monom n :=
  match n as n return forall i, i < n -> nat -> monom n with
    | O => fun i h _ => False_rec (monom O) (lt_n_O h)
    | S n' => fun i =>
      match i as i return lt i (S n') -> nat -> monom (S n') with
        | O => fun _ k => Vcons k (mone n')
	| S _ => fun h k => Vcons O (mxi (lt_S_n h) k)
      end
  end.

(* monomial multiplication *)

Definition mmult n (m1 m2 : monom n) := Vmap2 plus m1 m2. *)
 
(***********************************************************************)
(** polynomials on a Semi-ring *)

Section S.

  Context {R: Ring}.

  Import SR_Notations.

  Add Ring R : r_th.

  (* polynomials with n variables *)
  
  Definition poly n := list (s_typ * monom n).
  
  Delimit Scope poly_scope with poly.
  Bind Scope poly_scope    with poly.

  (***********************************************************************)
  (** coefficient of monomial m in polynomial p *)

  Fixpoint coef n (m : monom n) (p : poly n) {struct p} : s_typ :=
    match p with
      | nil => 0
      | cons (c,m') p' =>
        match monom_eq_dec m m' with
	  | left _ => c + coef m p'
	  | right _ => coef m p'
        end
    end.

  (***********************************************************************)
  (** simple polynomials *)

  Notation mone := (Vconst O).

  (* monomial x_i^1 *)
  
  Fixpoint mxi n : forall i, i < n -> monom n :=
    match n as n return forall i, i < n -> monom n with
      | O => fun i h => False_rec (monom O) (lt_n_O h)
      | S n' => fun i =>
                  match i as i return lt i (S n') -> monom (S n') with
                    | O => fun _ => Vcons (S O) (mone n')
	            | S _ => fun h => Vcons O (mxi (lt_S_n h))
                  end
    end.

  (* polynomial x_i for i<n *)
  
  Definition pxi n i (h : i < n) := (1, mxi h) :: nil.
  
  (* null polynomial *)
  
  Definition pzero n : poly n := nil.
  
  (* constant polynomial *)
  
  Definition pconst n (c : s_typ) : poly n := (c, mone n) :: nil.
  
  (***********************************************************************)
  (** multiplication by a constant *)
  
  Definition cpmult c n (p : poly n) := map (fun cm => (c * fst cm, snd cm)) p.

  (***********************************************************************)
  (** opposite *)
  
  Definition popp (n: nat) (p: poly n) := map (fun cm => (- fst cm, snd cm)) p.

  Notation "'-' p" := (popp p) (at level 35, right associativity) : poly_scope.
  
  (***********************************************************************)
  (** addition *)

  Fixpoint mpadd n (c : s_typ) (m : monom n) (p : poly n) {struct p} : poly n :=
    match p with
      | nil => (c,m) :: nil
      | cons (c',m') p' =>
        match monom_eq_dec m m' with
	  | left _ => (c+c',m) :: p'
	  | right _ => (c',m') :: mpadd c m p'
        end
    end.
  
  Fixpoint padd n (p1 p2 : poly n) {struct p1} : poly n :=
    match p1 with
      | nil => p2
      | cons (c,m) p' => mpadd c m (padd p' p2)
    end.
  
  Infix "+" := padd : poly_scope.

  (***********************************************************************)
  (** substraction *)
  
  Open Local Scope poly_scope.
  
  Definition pminus (n: nat) (p1 p2: poly n)  :=  p1  + (- p2).
  
  Infix "-" := pminus : poly_scope.

  (***********************************************************************)
  (** multiplication *)

  Definition mmult n (m1 m2 : monom n) := Vmap2 plus m1 m2.

  Definition mpmult n c (m : monom n) (p : poly n) :=
    map (fun cm => (c * fst cm, mmult m (snd cm))) p.
  
  Fixpoint pmult n (p1 p2 : poly n) {struct p1} : poly n :=
    match p1 with
      | nil => nil
      | cons (c,m) p' => mpmult c m p2 + pmult p' p2
    end.

  Infix "*" := pmult : poly_scope.

  (***********************************************************************)
  (** power *)
  
  Fixpoint ppower n (p : poly n) (k : nat) {struct k} : poly n :=
    match k with
      | O => pconst n 1
      | S k' => p * ppower p k'
    end.
  
  Infix "^" := ppower : poly_scope.

  (***********************************************************************)
  (** composition *)
  
  Fixpoint mcomp n : monom n -> forall k, vector (poly k) n -> poly k :=
    match n as n return monom n -> forall k, vector (poly k) n -> poly k with
      | O => fun _ k _ => pconst k 1
      | S _ => fun m _ ps => Vhead ps ^ Vhead m * mcomp (Vtail m) (Vtail ps)
    end.

  Fixpoint pcomp n (p : poly n) k (ps : vector (poly k) n) {struct p} : poly k :=
    match p with
      | nil => nil
      | cons (c,m) p' => cpmult c (mcomp m ps) + pcomp p' ps
    end.
  
  Close Local Scope poly_scope.
  
  (***********************************************************************)
  (** evaluation *)
  
  Notation vec := (vector s_typ).

  Fixpoint meval n : monom n -> vec n -> s_typ :=
    match n as n return monom n -> vec n -> s_typ with
      | O => fun _ _ => 1
      | S _ => fun m v => power _ (Vhead v) (Vhead m) * meval (Vtail m) (Vtail v)
    end.
  
  Fixpoint peval n (p : poly n) (v : vec n) {struct p} : s_typ :=
    match p with
      | nil => 0
      | cons (c,m) p' => c * meval m v + peval p' v
    end.

  Lemma meval_app : forall n1 (m1 : monom n1) (v1 : vec n1)
                           n2 (m2 : monom n2) (v2 : vec n2),
    meval (Vapp m1 m2) (Vapp v1 v2) == meval m1 v1 * meval m2 v2.

  Proof. 
    induction m1. intros. VOtac. simpl. ring.
    intros. VSntac v1. simpl. rewrite IHm1. ring. 
  Qed.

  Lemma meval_one : forall n (v : vec n), meval (mone n) v == 1.

  Proof. 
    intros n v. induction v; simpl. refl. rewrite IHv. ring.
  Qed.

  Lemma meval_xi : forall n i (H: i<n) (v: vec n),
    meval (mxi H) v == Vnth v H.

  Proof.
  induction n. intros. absurd(lt i 0). omega. hyp.
  intro. destruct i; intros; VSntac v. simpl.
  rewrite meval_one. ring. simpl. rewrite IHn. ring.
  Qed.

  Lemma peval_const : forall n c (v : vec n), peval (pconst n c) v == c.

  Proof. 
    intros. simpl. rewrite meval_one. ring. 
  Qed.

  Lemma peval_app : forall n (p1 p2 : poly n) (v : vec n),
    peval (p1 ++ p2) v == peval p1 v + peval p2 v.

  Proof.
    intros. elim p1. simpl. auto. ring. 
    intros (c, m). intros. simpl. rewrite H. ring.  
  Qed.
  
  Lemma peval_opp : forall n (p : poly n) (v : vec n),
    peval (- p) v == - peval p v.

  Proof. 
    intros. elim p. simpl. ring.
    intros (c, m). intros. simpl. rewrite H. ring.  
  Qed.

  Lemma peval_mpadd : forall n c (m : monom n) (p : poly n) (v : vec n),
    peval (mpadd c m p) v == c * meval m v + peval p v.

  Proof. 
    intros. elim p. simpl. ring. 
    intros (c', m'). intros. simpl.
    case (monom_eq_dec m m'); simpl; intro. subst m'. ring.
    rewrite H. ring.
  Qed.

  Lemma peval_add : forall n (p1 p2 : poly n) (v : vec n),
    peval (p1 + p2) v == peval p1 v + peval p2 v.

  Proof. intros. elim p1. simpl. ring. auto.
    intros (c, m). intros. simpl. rewrite peval_mpadd. rewrite H. ring.
  Qed.

  Lemma peval_minus : forall n (p1 p2 : poly n) (v : vec n),
    peval (p1 - p2) v == peval p1 v - peval p2 v.

  Proof.
    intros. unfold pminus. rewrite peval_add. rewrite peval_opp. ring.
  Qed.

  Lemma meval_mult : forall n (m1 m2 : monom n) (v : vec n),
    meval (mmult m1 m2) v == meval m1 v * meval m2 v.

  Proof.
    induction n; intros. VOtac. simpl. ring. VSntac m1. VSntac m2.
    simpl. unfold mmult in IHn. rewrite IHn. rewrite power_add. ring.
  Qed.

  Lemma peval_mpmult : forall n c (m : monom n) (p : poly n) (v : vec n),
    peval (mpmult c m p) v == c * meval m v * peval p v.

  Proof.
    induction p; intros; simpl. ring. destruct a. simpl. rewrite IHp.
    rewrite meval_mult. ring.
  Qed.

  Lemma peval_mult : forall n (p1 p2 : poly n) (v : vec n),
    peval (p1 * p2) v == peval p1 v * peval p2 v.

  Proof.
    induction p1; intros; simpl. ring. destruct a. simpl. rewrite peval_add.
    rewrite peval_mpmult. rewrite IHp1. ring.
  Qed.

  Lemma peval_power : forall n (p : poly n) (k : nat) (v : vec n),
    peval (ppower p k) v == power _ (peval p v) k.

  Proof.
    induction k; intros; simpl. rewrite meval_one. ring.
    rewrite peval_mult. rewrite IHk. ring.
  Qed.

  Lemma peval_mcomp : forall n k (m: monom n) (ps: vector (poly k) n)
    (v: vec k), peval (mcomp m ps) v == meval m (Vmap (fun p => peval p v) ps).

  Proof.
    induction n; intros. VOtac. simpl. rewrite meval_one. ring.
    VSntac m. VSntac ps. simpl. rewrite peval_mult. rewrite peval_power.
    rewrite IHn. refl.
  Qed.

  Lemma peval_cpmult : forall n c (p : poly n) (v : vec n),
    peval (cpmult c p) v == c * peval p v.

  Proof.
    induction p; intros; simpl. ring. destruct a. simpl. rewrite IHp. ring.
  Qed.

  Lemma peval_comp : forall n k (p: poly n) (ps: vector (poly k) n) (v: vec k),
    peval (pcomp p ps) v == peval p (Vmap (fun p => peval p v) ps).

  Proof.
    induction p; intros; simpl. ring. destruct a. rewrite peval_add.
    rewrite peval_cpmult. rewrite IHp. rewrite peval_mcomp. ring. 
  Qed.

End S.