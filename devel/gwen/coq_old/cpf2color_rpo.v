(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2013-08-31

* Translate CPF type into CoLoR type.

*)

Set Implicit Arguments.

Require Import ATrs BinNat cpf cpf_ind Coccinelle2 rpo_extension2
  cpf_util List rpo2 LogicUtil.

Section precedence.

  Variable arity : symbol -> nat.
  Notation Sig := (Sig arity).

  Section status_type.
    
    Variable f : symbol.

    Fixpoint color_status_type
      (l : list(symbol * cpf.arity * nonNegativeInteger * t2))
      : status_type :=
      match l with
        | (g, _, _, t) :: l' =>
          match @eq_symb_dec Sig g f with
            | left _ => match t with
                          | T2_lex => Lex
                          | T2_mul => Mul
                        end
            | right _ => color_status_type l'
          end
        | nil => Lex (* if it is nil return Lex *)
      end.

  End status_type.

  (* Define a section for prec_nat return nat from list of
     statusPrecedence. *)

  Section prec_nat.

    Variable f: symbol.

    Fixpoint color_prec_nat
      (l : list (symbol * cpf.arity * nonNegativeInteger * t2))
      : nat :=
      match l with
        | (g, _, n, _) :: l' =>
          match @eq_symb_dec Sig g f with
            | left _ => let n := nat_of_N n in n
            | right _ => color_prec_nat l'
          end 
        | nil => 0 (* when it is nil return 0 *)
      end.
    
  End prec_nat.
  
  (* Define a function for [status: Sig -> status_type];
     [prec_nat : Sig -> nat] *)

  (* FIXME: it is like the function [trsInt] in poly.v *)
  
  Section S.

    Variable l : list (symbol * cpf.arity * nonNegativeInteger * t2).
    
    Definition status (f: symbol) : status_type := color_status_type f l.

    Definition prec_nat (f: symbol) : nat := color_prec_nat f l.

    (* Proof the lemma [prec_eq_status] by assume the boolean function  *)

    (* Proof a correctness of [prec_eq] *)

    Lemma prec_eq_ok : forall f g,
      prec_eq_bool' Sig prec_nat f g = true <-> prec_eq' Sig prec_nat f g.

    Proof.
      intros f g. gen (prec_eq_bool_ok' Sig prec_nat f g).
      intuition. rewrite H0 in H. hyp.
      case_eq (prec_eq_bool' Sig prec_nat f g); intros; try refl.
      rewrite H1 in H. absurd (prec_eq' Sig prec_nat f g); hyp.
    Qed.

    (* Define a boolean function for status symbol. *)

    Definition bprec_eq_status_symb f g : bool :=
      implb (prec_eq_bool' Sig prec_nat f g)
      (beq_status (status f) (status g)).
    
    (* Correctness proof of boolean function for status symbol. *)

    Lemma bprec_eq_status_symb_ok : forall f g,
      bprec_eq_status_symb f g = true <->
      (prec_eq' Sig prec_nat f g -> status f = status g).

    Proof.
      intros f g. unfold bprec_eq_status_symb, implb.
      case_eq (prec_eq_bool' Sig prec_nat f g); intros.
      rewrite prec_eq_ok in H. rewrite beq_status_ok.
      intuition.
      intuition. rewrite <- prec_eq_ok in H1. rewrite H in H1.
      discr.
    Qed.

    (* FIXME: assume a condition of bprec_eq_status_symb is true,
       this assume is a condition will be formalize in the pathOrder
       function. *)

    Definition list_sig : list symbol := split_list l.
    
    (* FIXME *)
    
    (*
       Variable T : forallb
       (fun x => bprec_eq_status Sig status prec_nat list_sig) list_sig= true.*)

    (*Variable H: forallb (fun f =>
       forallb (fun g => bprec_eq_status_symb f g) list_sig) list_sig = true.*)

    (*Variable H : forall f g, bprec_eq_status_symb f g = true.*)
    
    Lemma prec_eq_status : forall f g, prec_eq' Sig prec_nat f g ->
      status f = status g.
      
    Proof.
      intros f g. erewrite bprec_eq_status_ok.
    (* TODO *)
    Admitted.

    (* Define the record type PRECEDENCE *)
    
    (* Assume variable b of type nat. *)

    Variable bb : nat.

    Definition P : PRECEDENCE Sig :=
      Coccinelle2.mkPrecedence Sig status prec_nat bb prec_eq_status.

    (* Define a function [empty_rpo_infos] to be used in function
       [rpo_eval]. *)
    
    Definition empty_rpo_infos :=
      empty_rpo_infos Sig status prec_nat prec_eq_status bb.

    (* Define a function [rpo_eval] to be used in the function
       [pathOrdering] *)
    
    Definition rpo_eval :=
      @rpo_eval Sig status prec_nat prec_eq_status empty_rpo_infos bb.

  End S.

End precedence.