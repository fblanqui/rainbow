
(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-20
- Frederic Blanqui, 2005-02-24

polynomials with multiple variables and integer coefficients

- Kim Quyen Ly, 2013-08-23

Polynomials with multiple variables and rational coefficients.

*)

Set Implicit Arguments.

Require Import VecUtil LogicUtil List ZArith Arith RingType2 QArith.

(***********************************************************************)
(** monomials with n variables *)

Notation monom := (vector nat).

Lemma monom_eq_dec : forall n (m1 m2 : monom n), {m1 = m2} + {~m1 = m2}.
  
Proof.
  intros. eapply eq_vec_dec. apply eq_nat_dec.
Qed.

(***********************************************************************)
(** polynomials on a ring *)

Notation A := Q.
Notation "0" := QA0.
Notation "1" := QA1.

Notation "x + y" := (QAadd x y).
Notation "x * y" := (QAmul x y).
Notation "- x" := (QAopp x).

Definition Qpoly n := list (A * monom n).

Delimit Scope Qpoly_scope with Qpoly.

Bind Scope Qpoly_scope with Qpoly.

(***********************************************************************)
(** coefficient of monomial m in polynomial p *)

Open Local Scope Q_scope.

Fixpoint Qcoef n (m : monom n) (p : Qpoly n) {struct p} : A :=
  match p with
    | nil => 0
    | cons (c,m') p' =>
      match monom_eq_dec m m' with
	| left _ => c + Qcoef m p'
	| right _ => Qcoef m p'
      end
  end.

(***********************************************************************)
(** simple polynomials *)

(* monomial 1 *)

Open Local Scope nat_scope.

Notation mone := (Vconst O).

(* monomial x_i^1 *)

Fixpoint Qmxi n : forall i, lt i n -> monom n :=
  match n as n return forall i, lt i n -> monom n with
    | O => fun i h => False_rec (monom O) (lt_n_O h)
    | S n' => fun i =>
      match i as i return lt i (S n') -> monom (S n') with
        | O => fun _ => Vcons (S O) (mone n')
	| S _ => fun h => Vcons O (Qmxi (lt_S_n h))
      end
  end.

Close Scope nat_scope.

(* polynomial x_i for i<n *)

(* REMARK: mxi in the improving has kmax in the NewPolynom.v *)

Definition Qpxi n i (h : lt i n) : list (A * monom n) := (1, Qmxi h) :: nil.

(* null polynomial *)

Definition Qpzero n : Qpoly n := nil.

(* constant polynomial *)

Definition Qpconst n (c : A) : Qpoly n := (c, mone n) :: nil.

(***********************************************************************)
(** multiplication by a constant *)

Definition cpmult c n (p : Qpoly n) := map (fun cm => (c * fst cm, snd cm)) p.

(***********************************************************************)
(** opposite *)

Definition popp n (p : Qpoly n) := map (fun cm => (- fst cm, snd cm)) p.

Notation "'-' p" := (popp p) (at level 35, right associativity) : Qpoly_scope.

(***********************************************************************)
(** addition *)

Fixpoint mpadd n (c : A) (m : monom n) (p : Qpoly n) {struct p} : Qpoly n :=
  match p with
    | nil => (c,m) :: nil
    | cons (c',m') p' =>
      match monom_eq_dec m m' with
	| left _ => (c+c',m) :: p'
	| right _ => (c',m') :: mpadd c m p'
      end
  end.

Fixpoint padd n (p1 p2 : Qpoly n) {struct p1} : Qpoly n :=
  match p1 with
    | nil => p2
    | cons (c,m) p' => mpadd c m (padd p' p2)
  end.

Infix "+" := padd : Qpoly_scope.

(***********************************************************************)
(** substraction *)

Open Local Scope Qpoly_scope.

Definition pminus n (p1 p2 : Qpoly n) := p1 + (- p2).

Infix "-" := pminus : Qpoly_scope.

(***********************************************************************)
(** multiplication *)

(* monomial multiplication *)

Definition mmult n (m1 m2 : monom n) := Vmap2 plus m1 m2.

Definition mpmult n c (m : monom n) (p : Qpoly n) :=
  map (fun cm => (c * fst cm, mmult m (snd cm))) p.

Fixpoint pmult n (p1 p2 : Qpoly n) {struct p1} : Qpoly n :=
  match p1 with
    | nil => nil
    | cons (c,m) p' => mpmult c m p2 + pmult p' p2
  end.

Infix "*" := pmult : Qpoly_scope.

(***********************************************************************)
(** power *)

Fixpoint ppower n (p : Qpoly n) (k : nat) {struct k} : Qpoly n :=
  match k with
    | O => Qpconst n 1
    | S k' => p * ppower p k'
  end.

Infix "^" := ppower : Qpoly_scope.

(***********************************************************************)
(** composition *)

Fixpoint mcomp n : monom n -> forall k, vector (Qpoly k) n -> Qpoly k :=
  match n as n return monom n -> forall k, vector (Qpoly k) n -> Qpoly k with
    | O => fun _ k _ => Qpconst k 1
    | S _ => fun m _ ps => Vhead ps ^ Vhead m * mcomp (Vtail m) (Vtail ps)
  end.

Fixpoint pcomp n (p : Qpoly n) k (ps : vector (Qpoly k) n) {struct p} : Qpoly k :=
  match p with
    | nil => nil
    | cons (c,m) p' => cpmult c (mcomp m ps) + pcomp p' ps
  end.

Close Local Scope Qpoly_scope.

(***********************************************************************)
(** evaluation *)

Notation vec := (vector A).

Notation "x * y" := (QAmul x y).
Notation "x + y" := (QAadd x y).

(* Using Qpower Because power has type A and not define in Q. *)

Fixpoint meval n : monom n -> vec n -> A :=
  match n as n return monom n -> vec n -> A with
    | O => fun _ _ => 1
    | S _ => fun m v => Qpower (Vhead v) (Z.of_nat (Vhead m)) * meval (Vtail m) (Vtail v)
  end.

Fixpoint peval n (p : Qpoly n) (v : vec n) {struct p} : A :=
  match p with
    | nil => 0
    | cons (c,m) p' => c * meval m v + peval p' v
  end.

Require Import BoolUtil RelExtras2.

Notation "x =A= y" := (QeqA x y) (at level 70).

Lemma meval_eqA : forall n (m : monom n) (v1 v2 : vec n),
  beq_vec QbeqA v1 v2 = true -> meval m v1 =A= meval m v2.

Proof.
  induction n; simpl; intros. refl. gen H. VSntac v1. VSntac v2. simpl.
  rewrite andb_eq. rewrite QbeqA_ok. intuition.
  rewrite H3. rewrite (IHn _ _ _ H4). refl.
Qed.

Implicit Arguments meval_eqA [n m v1 v2].

Lemma peval_eqA : forall n (p : Qpoly n) (v1 v2 : vec n),
  beq_vec QbeqA v1 v2 = true -> peval p v1 =A= peval p v2.

Proof.
  induction p; simpl; intros. refl. destruct a. rewrite (IHp _ _ H).
  rewrite (meval_eqA H). refl.
Qed.

Lemma meval_app : forall n1 (m1 : monom n1) (v1 : vec n1)
  n2 (m2 : monom n2) (v2 : vec n2),
  meval (Vapp m1 m2) (Vapp v1 v2) =A= meval m1 v1 * meval m2 v2.
  
Proof. 
  induction m1. intros. VOtac. simpl in *. unfold QeqA. ring.
  intros. VSntac v1. simpl. rewrite IHm1. unfold QeqA. ring. 
Qed.

Lemma meval_one : forall n (v : vec n), meval (mone n) v =A= 1.
  
Proof. 
  intros n v. induction v; simpl. refl. rewrite IHv. unfold QeqA.
  ring.
Qed.

Lemma meval_xi : forall (n i: nat) (H: lt i n) (v: vec n),
  meval (Qmxi H) v =A= Vnth v H.
  
Proof.
  induction n. intros. absurd(lt i 0). omega. hyp.
  intro. destruct i; intros; VSntac v. simpl.
  rewrite meval_one. unfold QeqA. ring. simpl. rewrite IHn. 
  unfold QeqA. ring.
Qed.

Lemma peval_const : forall n c (v : vec n), peval (Qpconst n c) v =A= c.
  
Proof. 
  intros. simpl. rewrite meval_one. unfold QeqA. ring.
Qed.

Lemma peval_app : forall n (p1 p2 : Qpoly n) (v : vec n),
  peval (p1 ++ p2) v =A= peval p1 v + peval p2 v.
  
Proof.
  intros. elim p1. simpl. auto. unfold QeqA. ring. 
  intros (c, m). intros. simpl. rewrite H. unfold QeqA. ring.  
Qed.

Lemma peval_opp : forall n (p : Qpoly n) (v : vec n),
  peval (- p) v =A= - peval p v.
  
Proof. 
  intros. elim p. simpl. unfold QeqA. ring.
  intros (c, m). intros. simpl. rewrite H. unfold QeqA. ring.
Qed.

Lemma peval_mpadd : forall n c (m : monom n) (p : Qpoly n) (v : vec n),
  peval (mpadd c m p) v =A= c * meval m v + peval p v.
  
Proof. 
  intros. elim p. simpl in *. unfold QeqA. ring. 
  intros (c', m'). intros. simpl.
  case (monom_eq_dec m m'); simpl; intro. subst m'. unfold QeqA. ring.
  rewrite H. unfold QeqA. ring.
Qed.

Lemma peval_add : forall n (p1 p2 : Qpoly n) (v : vec n),
  peval (p1 + p2) v =A= peval p1 v + peval p2 v.
  
Proof. intros. elim p1. simpl. unfold QeqA. ring. auto.
  intros (c, m). intros. simpl. rewrite peval_mpadd. rewrite H.
  unfold QeqA. ring.
Qed.

Lemma peval_minus : forall n (p1 p2 : Qpoly n) (v : vec n),
  peval (p1 - p2) v =A= peval p1 v - peval p2 v.
  
Proof.
  intros. unfold pminus. rewrite peval_add. rewrite peval_opp.
  unfold QeqA. ring.
Qed.

Lemma Qpower_add : forall x n1 n2, Qpower x (n1 + n2) =A= Qpower x n1 * Qpower x n2.
Proof.
Admitted.

Lemma meval_mult : forall n (m1 m2 : monom n) (v : vec n),
  meval (mmult m1 m2) v =A= meval m1 v * meval m2 v.
  
Proof.
  induction n; intros. VOtac. refl.
  VSntac m1. VSntac m2. simpl. unfold mmult in IHn.
  rewrite IHn. 
  (* TODO: new lemma for power_add in Q. *)
  (*rewrite Qpower_add. ring.
     Qed.*)
Admitted.

Lemma peval_mpmult : forall n c (m : monom n) (p : Qpoly n) (v : vec n),
  peval (mpmult c m p) v =A= c * meval m v * peval p v.
  
Proof.
  induction p; intros; simpl. unfold QeqA. ring.
  destruct a. simpl. rewrite IHp.
  rewrite meval_mult. unfold QeqA. ring.
Qed.

Lemma peval_mult : forall n (p1 p2 : Qpoly n) (v : vec n),
  peval (p1 * p2) v =A= peval p1 v * peval p2 v.
  
Proof.
  induction p1; intros; simpl. unfold QeqA. ring.
  destruct a. simpl. rewrite peval_add.
  rewrite peval_mpmult. rewrite IHp1. unfold QeqA. ring.
Qed.

Lemma peval_power : forall n (p : Qpoly n) (k : nat) (v : vec n),
  peval (ppower p k) v =A= Qpower (peval p v) (Z.of_nat k).
  
Proof.
  induction k; intros; simpl. rewrite meval_one. unfold QeqA. ring.
  rewrite peval_mult. rewrite IHk. 
  (* TODO *)
  (*ring.
     Qed.*)
Admitted.

Lemma peval_mcomp : forall n k (m: monom n) (ps: vector (Qpoly k) n)
  (v: vec k), peval (mcomp m ps) v =A= meval m (Vmap (fun p => peval p v) ps).
  
Proof.
  induction n; intros. VOtac. simpl. rewrite meval_one.
  unfold QeqA. ring.
  VSntac m. VSntac ps. simpl. rewrite peval_mult. rewrite peval_power.
  rewrite IHn. refl.
Qed.

Lemma peval_cpmult : forall n c (p : Qpoly n) (v : vec n),
  peval (cpmult c p) v =A= c * peval p v.
  
Proof.
  induction p; intros; simpl. unfold QeqA. ring.
  destruct a. simpl. rewrite IHp.
  unfold QeqA. ring.
Qed.

Lemma peval_comp : forall n k (p: Qpoly n) (ps: vector (Qpoly k) n) (v: vec k),
  peval (pcomp p ps) v =A= peval p (Vmap (fun p => peval p v) ps).
  
Proof.
  induction p; intros; simpl.
  unfold QeqA. ring. destruct a. rewrite peval_add.
  rewrite peval_cpmult. rewrite IHp. rewrite peval_mcomp.
  unfold QeqA. ring. 
Qed.