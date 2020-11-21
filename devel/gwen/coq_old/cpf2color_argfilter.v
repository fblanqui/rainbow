(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2013-09-30

* Translate CPF type into CoLoR type.

*)

Set Implicit Arguments.

(* REMARK : [filter: term -> term'] inside [AFilterTerm] has a same
   name with [filter] in List. *)

Require Import ATrs BinNat cpf cpf_ind cpf_util LogicUtil
  Compare_dec ZUtil AFilterPerm ListUtil NatUtil AProj.

(* REMARK: AProj: raw_pi : Sig -> option nat.
   AFilterPerm: raw_pi : Sig -> list nat.
   
   Where AFilterPerm is non-collapsing arguments filtering with
   permutations; and AProj is arguments filtering with projections
   only.
   
   - In old Rainbow used:
   AFilterPerm for : RPO + DP_argumentfilterProc and
   AProj for: SubtermProc in DP_subtermProc. *)

Section S.

  (* TEST collapsing is true. *)

  Definition is_collapsing (t: t3) : bool :=
    match t with
      | T3_collapsing _ => true
      | T3_nonCollapsing _ => false
    end.

  Definition is_noncollapsing (t: t3) : bool :=
    match t with
      | T3_collapsing _ => false
      | T3_nonCollapsing _ => true
    end.

  (* Check both collapsing and nonCollapsing is true *)

  Definition is_col_noncol (t: t3) : bool :=
    match t with
      | T3_collapsing _
      | T3_nonCollapsing _ => true
    end.

  (* TODO: MOVE *)
  (* FIXME: in cpf2color_loop. has the same function of list position
     -> list nat. but in result type *)

  (* Define a function translate positive to nat.
     REMARK: minus 1 because positive in Coq started from 1, when
     natural numbers started from 0. *)

  Definition color_positiveInteger (p: positive) : nat :=
    nat_of_P p - 1.

  (* Define a function taking a list of position of type
     [positiveInteger] and return a list nat.
     For example: if the list of position is : [1 2 3 4]
     then the return value is: [0 1 2 3]. *)

  Definition list_position_nat (ps: list position) : list nat :=
    List.map color_positiveInteger ps.
  
  Variable arity : symbol -> nat.

  Variable f : symbol.

  (* Define a function transform arity cpf type into type nat. *)

  Definition color_arity (a: cpf.arity) : nat := nat_of_N a.

  (* Define [raw_pi: Sig -> list nat] in AFilterPerm from a list of
     argument filtering. *)

  (* If the list of position in nonCollapsing is equiv
     with the increase list less than of (arity f) (i.e
     if (arity f = 4) then the increase list less than
     of 3 is: 0 1 2 3) then return nil/None otherwise
     return a list of position in nonCollapsing.
     
     For example: the position list in nonCollapsing is:
     [1 2 3 4] then tranform it to type [nat] by minus 1
     the list become : 0 1 2 3.  Support the (arity f =
     4) then the condition is true, for [0 1 2 3] is
     equivalence with [0 1 2 3] then the return value is
     [nil].  Otherwise if (arity f <> 4) then the
     condition is false and the return value is the list
     of [ps: 0 1 2 3].
     *)

  Fixpoint raw_pi_filter (l: list (symbol * cpf.arity * t3)): list nat :=
    match l with
      | (g, n, t) :: l' =>
        match @eq_symb_dec (Sig arity) g f with
          | left _ =>
            match t with
              | T3_collapsing p => color_positiveInteger p :: nil (* FIXME: nil?*)
              | T3_nonCollapsing ps =>
                if equiv beq_nat (list_position_nat ps) (nats_incr_lt (arity f))
                  then nil
                  else list_position_nat ps
            end
          | right _ => raw_pi_filter l'
        end
      | nil => nats_incr_lt (arity f)
    end.

  (* Define function [raw_pi: option nat] in the case
     projection only from a list of argument filtering. *)

  Fixpoint raw_pi_proj (l: list (symbol * cpf.arity * t3)): option nat :=
    match l with
      | (g, _, t) :: l' =>
        match @eq_symb_dec (Sig arity) g f with
          | left _ =>
            match t with
              | T3_collapsing p => Some (color_positiveInteger p)
              | T3_nonCollapsing _ps => None
            end
          | right _ => raw_pi_proj l'
        end
      | nil => None
    end.

End S.

(******************************************************************************)

Section raw_pi.

  Variable arity : symbol -> nat.
  Variable l : list (symbol * cpf.arity * t3).

  (* raw_pi filter : Sig -> list nat. *)

  Definition color_raw_pi_filter (f: symbol) : list nat := raw_pi_filter arity f l.

  (* raw_pi projection: Sig -> option nat. *)

  Definition color_raw_pi_proj (f: symbol) : option nat := raw_pi_proj arity f l.

End raw_pi.

(******************************************************************************)

Section pi.
  
  Variable arity : symbol -> nat.
  Variable f: symbol.

  (* TODO: proving the lemma [raw_pi_ok]; or make it as a variable and
     then given the boolean function in the cpf2color_argfilter. *)

  (* TODO *)
  Lemma raw_pi_ok : forall ps, 
    forallb (bgt_nat (arity f)) (list_position_nat ps) = true.
  Proof.
  Admitted.

  (*Variable raw_pi_ok : forall ps, 
    forallb (bgt_nat (arity f)) (list_position_nat ps) = true. *)

  (* Define [pi: forall f: Sig, nat_lts (arity f)] in the case of
  non-collapsing (filtering).*)

  (* REMOVE *)
  Fixpoint pi_filter (l : list (symbol * cpf.arity * t3)): nat_lts (arity f) :=
    match l with
      | (g, _, t3) :: l' =>
        match @eq_symb_dec (Sig arity) g f with
          | left _ =>
            match t3 with
              | T3_collapsing _p => mk_nat_lts (arity f)
              | T3_nonCollapsing ps =>
                build_nat_lts (arity f) (list_position_nat ps) (raw_pi_ok ps)
            end
          | right _ => pi_filter l'
        end
      | nil => mk_nat_lts (arity f) (* FIXME *)
    end.
  
  (* Define [pi: forall f: Sig arity, option {k:nat | k < arity f}] in
     the case of projection (collapsing) only from an argument af in CPF. *)

  Fixpoint pi_proj (l: list (symbol * cpf.arity * t3)): option {k : nat | k < arity f}:=
    match l with
      | (g, _, t3) :: l' =>
        match @eq_symb_dec (Sig arity) g f with
          | left _ =>
            match t3 with
              | T3_collapsing p =>
                let n := color_positiveInteger p in
                  match lt_dec n (arity f) with
                    | left h => Some (mk_proj (Sig arity) f h)
                    | right _ => None
                  end
              | T3_nonCollapsing ps => None
            end
          | right _ => pi_proj l'
        end
      | nil => None
    end.

End pi.

(******************************************************************************)
(* FIXME: define [color_pi_filter] by using build_pi to be able to use
the lemma bnon_dup_ok in the correctness proof for AF in DP. *)

Section build_pi.

Require Import AFilterPerm.

Variable arity : symbol -> nat.
Variable l: list (symbol * cpf.arity * t3).

Definition Fs : list (Sig arity) := list_split_triple l.

(* TODO *)
Lemma Fs_ok : forall f, In f Fs.

Proof.
Admitted.

(* Use this function for type: Sig -> list nat. *)

Definition color_raw_pi : (Sig arity) -> list nat :=
  color_raw_pi_filter arity l.

(* TODO *)
Lemma color_raw_pi_ok : bvalid color_raw_pi Fs = true.

Proof.

Admitted.

(* REMARK: this is equal to the function [color_pi_filter] below. *)
Definition color_build_pi :=
  build_pi Fs_ok color_raw_pi_ok.

End build_pi.

(******************************************************************************)

Section color_pi.

  Variable l : list (symbol * cpf.arity * t3).
  Variable arity : symbol -> nat.

  (* TEST: use in the case of rainbow_top_termin. *)
  
  Definition color_pi_filter (f: symbol) : nat_lts (arity f) :=
    pi_filter arity f l.

  (* Define a function [color_pi_proj] transform CPF type into CoLoR
     type [pi_proj] *)

  Definition color_pi_proj (f: symbol): option {k : nat | k < arity f} :=
    pi_proj arity f l.

  (* Define a function [color_filter] transform CPF type into CoLoR
     type [filter] in non-collpasing. *)

  Notation aterm := (ATerm.term (Sig arity)).

  (* TEST: check the result use in rainbow_top_termin *)

  Definition color_filter (t:aterm) :=
    @AFilterPerm.filter (Sig arity) (color_pi_filter) t.

  (* TEST Replace [color_pi_filter] by [build_pi] to be able to proof non-dup. *)
  (*
  Definition color_filter (t:aterm) :=
    @AFilterPerm.filter (Sig arity) (color_build_pi l) t. *)

  (* Define a function [color_proj] transform CPF type into CoLoR type
     [proj] in projection only. *)

  Definition color_proj (t: aterm) : aterm :=
    @proj (Sig arity) (color_pi_proj) t.

  (* Define a function [color_filter_rules] transform CPF type into
  CoLoR type [filter_rules]. *)

  Notation arules := (list (ATrs.rule (Sig arity))).

  Definition color_filter_rule := @filter_rule (Sig arity).

  Definition color_filter_rules r := List.map (color_filter_rule r).

  (* Define a function [color_proj_rules] transform CPF type into
  CoLoR type [proj_rules]. *)
  
  Definition color_proj_rules (r:arules) :=
    @proj_rules (Sig arity) (color_pi_proj) r. 

  (* Define record type [Perm] in [ARedPair2.v] *)

  Require Import ARedPair2.

  (* TODO *)

  (* Proof this non_dup by using the boolean function in the
     bnon_dup_ok. And declare the boolean non_dup function as a
     variable then add them in the boolean function of
     cpf2color_argfilter.*)

  (*Variable bnon_dup use build_pi to build [nats_lt] *)
    
  (* FIXME: define the function [non_dup] *)

  (* TEST: used color_pi_filter *)
  Lemma pi_perm_ok: @non_dup (Sig arity) (color_pi_filter).

  Proof.
    unfold color_build_pi. 
  Admitted.

  (* Define record type [Proj] in [ARedPair2.v] *)

  (* TEST: with color_pi_filter *)
  Definition color_Perm : Perm (Sig arity) :=
    @mkPerm (Sig arity) (color_pi_filter) (pi_perm_ok).  (* FIXME *)

  (* Definition Sig_perm : Signature := filter_sig (pi_perm perm).*)
 
  Definition color_Sig_perm : Signature := @Sig_perm (Sig arity) color_Perm.

  (*************)
  (* TEST: use color_build_pi *)
  (*
  Lemma pi_perm_ok2: @non_dup (Sig arity) (color_build_pi l).

  Proof.
    unfold color_build_pi. apply bnon_dup_ok.

  Admitted.

  Definition color_Perm2 : Perm (Sig arity) :=
    @mkPerm (Sig arity) (color_build_pi l) (pi_perm_ok2).  (* FIXME *)

  Definition color_Sig_perm2 : Signature := @Sig_perm (Sig arity) color_Perm2. *)

  (*Record Proj := mkProj {
     pi_proj : forall f: Sig, option {k | k < arity f} }.*)
  
  Definition color_Proj : Proj (Sig arity) := @mkProj (Sig arity) color_pi_proj.

End color_pi.