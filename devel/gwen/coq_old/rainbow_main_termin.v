(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2011-04-06

* CPF correctness checker

*)

Set Implicit Arguments.

Require Import ATrs SN ZArith EqUtil String List ListDec ListForall
  ListUtil ZUtil LogicUtil BoolUtil VecUtil cpf2color cpf ListExtras
  cpf_util RelUtil AVarCond ALoop APosition rainbow_full_termin
  rainbow_top_termin AReverse AUnary cpf2color rainbow_non_termin.

Section S.

  (** [nat_of_string]: convert variable map to natural number *)

  Variable nat_of_string : string  -> nat.

  (** [n: nat] is an artificial extra argument which purpose is to
     make the function [dpProof] structually recursive with respect to
     this argument. *)
  
  Variable n: nat.

  (** [bb] is a variable of [rpo] function. *)

  Variable bb: nat.

  Section Termination.

    (***********************************************************************)
    (** Check that [R] is a trivial proof by stating the set of rules [R] is
       empty valid termination proof for [red R]. *)

    Definition trsTerminationProof_rIsEmpty a (R: arules a) :=
      if is_empty R then OK else Ko _ ErNotEmpty.
    
    (***********************************************************************)
    (** ** Check that [p] is a valid termination proof for [red R]
     - [rIsEmpty] : state that the TRS is terminating since it has no rules.
     - [ruleRemoval]: use a reduction pair where both the weak and the
     strict ordering are monotone. Delete all strictly decreasing
     rules. The remaining rules have to be given. If the ordering
     constraint proof is only an assumption, the
     orderingConstraints-element becomes mandatory.
     - [dpTrans]: switch to dependency pairs. The dependency pairs have to
     be given. If marked is true, then the whole dp-proof is using a notion
     of chain where rewriting with the rules is applied at arbitrary
     positions (including the root). Otherwise, rewriting with the rules is
     not allowed at the root. 
     - [stringReversal]: reverse the strings in both TRSs R and S, i.e., replace
      f(g(h(x))) -&gt; f(x) by h(g(f(x))) -&gt; f(x).  Note that the
      variable in a reversed rule should be same as the variable in the
      original rule.  
     Proving string reversal require two assumptions: AReverse.v: [WF_red_rev_eq]
     - Variables are preserve [brules_preserve_vars]
     - A signature with unary symbols is true [bis_unary].*)
   
    Fixpoint trsTerminationProof a (R: arules a) p :=
      match p with
        | TrsTerminationProof_rIsEmpty =>
          trsTerminationProof_rIsEmpty R
        | TrsTerminationProof_ruleRemoval (Some _) _ _ _ =>
          Ko _ TTrsTerminationProof_ruleRemoval
        | TrsTerminationProof_ruleRemoval None ocp rs p =>
          Match trsTerminationProof_ruleRemoval bb R ocp With R' ===>
                trsTerminationProof R' p
        | TrsTerminationProof_dpTrans dps b dp =>
          trsTerminationProof_dpTrans bb nat_of_string n R dps b dp
        | TrsTerminationProof_semlab _ _ _ =>
          Ko _ TTrsTerminationProof_semlab
        | TrsTerminationProof_unlab rs p =>
          Ko _ TTrsTerminationProof_unlab
        | TrsTerminationProof_stringReversal rs p =>
          if brules_preserve_vars R && @bis_unary (Sig a) (symbol_in_rules rs) then
            trsTerminationProof (reverse_trs R) p
          else Ko _ TTrsTerminationProof_stringReversal
        | TrsTerminationProof_flatContextClosure cs rs p =>
          Ko _ TTrsTerminationProof_flatContextClosure
        | TrsTerminationProof_terminationAssumption i =>
          Ko _ TTrsTerminationProof_terminationAssumption
        (*| TrsTerminationProof_uncurry _ _ _ =>
          Ko _ TTrsTerminationProof_uncurry
        | TrsTerminationProof_bounds _ _ _ _ =>
          Ko _ TTrsTerminationProof_bounds
        | TrsTerminationProof_switchInnermost _ _ =>
          Ko _ TTrsTerminationProof_switchInnermost
        | TrsTerminationProof_split _ _ _ =>
          Ko _ TTrsTerminationProof_split
        | TrsTerminationProof_removeNonApplicableRules _ _ =>
          Ko _  TTrsTerminationProof_removeNonApplicableRules*)
      end.

  End Termination.

  (***********************************************************************)
  (** Relative termination proof. *)

  Section Relative_Termination.

    (***********************************************************************)
    (** Check that [R] is a trivial proof by stating the set of rules [R] is
       empty valid termination proof for [red R]. *)

    Definition relTerminationProof_rIsEmpty a (D : arules a) :=
      if is_empty D then OK else Ko _ ErNotEmptyrIsEmpty.
    
    (***********************************************************************)
    (** Check that [p] is a valid termination proof for [red_mod R D].
     - [rIsEmpty] [sIsEmpty]: state that the relative termination is
       terminating since it has no rules.
     - [ruleRemoval]: use a reduction pair where both the weak and the
     strict ordering are monotone. Delete all strictly decreasing
     rules. The remaining rules have to be given. If the ordering
     constraint proof is only an assumption, the
     orderingConstraints-element becomes mandatory.
     - [stringReversal]: reverse the strings in both R and S, i.e., replace
      f(g(h(x))) -&gt; f(x) by h(g(f(x))) -&gt; f(x).  Note that the
      variable in a reversed rule should be same as the variable in the
      original rule.*)

    Fixpoint relTerminationProof a (R D: arules a) p : result unit :=
      match p with
        | RelativeTerminationProof_rIsEmpty
        | RelativeTerminationProof_sIsEmpty _ => 
          relTerminationProof_rIsEmpty D
        | RelativeTerminationProof_ruleRemoval (Some _) _ _ _ _ =>
          Ko _  TTrsTerminationProof_ruleRemoval 
        | RelativeTerminationProof_ruleRemoval None ocp rs trs p =>
          Match  rel_trsTerminationProof_ruleRemoval R D ocp With D' ===>
                relTerminationProof R D' p
        | RelativeTerminationProof_semlab _ _ _ _ =>
          Ko _ TTrsTerminationProof_semlab 
        | RelativeTerminationProof_unlab _ _ _ =>
          Ko _ TTrsTerminationProof_unlab
        | RelativeTerminationProof_stringReversal rs rs2 dp =>
          if brules_preserve_vars R &&
             brules_preserve_vars D &&
            @bis_unary (Sig a) (symbol_in_rules rs) then
            relTerminationProof (reverse_trs R) (reverse_trs D) dp
          else Ko _ TTrsTerminationProof_stringReversal
        | RelativeTerminationProof_relativeTerminationAssumption _ =>
          Ko _ TTrsTerminationProof_terminationAssumption
        (*| RelativeTerminationProof_uncurry  _ _ _ _ =>
          Ko _ TTrsTerminationProof_uncurry
        | RelativeTerminationProof_equalityRemoval _ =>
          Ko _ TRelativeTerminationProof_equalityRemoval*)
      end.

  End Relative_Termination.

  (***********************************************************************)
  (** ** Check that [p] is a valid termination proof for:
   - Termination proof: [red R]
   - Dependency pair proof: [hd_red_mod R D]. 
   Also check that [p] is a valid non-termination proof for:
   - Non-termination proof: [red R]
   - Relative non-termination proof: [red_mod R D]. *)

  Section main.

    Definition proof a (s:system a) p :=
      match s, p with
        | Red R, Proof_trsTerminationProof p =>
          trsTerminationProof R p
        | Red R, Proof_trsNonterminationProof p =>
          trsNonTerminationProof nat_of_string R p
        | Red_mod E R, Proof_relativeTerminationProof p => (* FIXME *)
          relTerminationProof E R p
        | Red_mod E R, Proof_relativeNonterminationProof p => (* FIXME *)
        (*relativeNonterminationProof nat_of_string E R p *)
          Ko _ Todo
        | Hd_red_mod E R, Proof_dpProof p =>
          dpProof bb nat_of_string n E R p
        | Hd_red_mod E R, Proof_dpNonterminationProof _ =>
          (* TODO: dp_counter example loop? *)
          Ko _ TProof_dpNonterminationProof
        | _, Proof_orderingConstraintProof _ =>
          Ko _ TProof_orderingConstraintProof
        | _, _ => Ko _ EinputProofIncompatible
      end. 
    
    Definition check a (c: certificationProblem) :=
      match c with
        | (_, _, p, _) => Match sys_of_pb a nat_of_string c With s ===> proof s p
      end.
    
    (* how to express the correctness of main ? *)  
    
    Definition not_if (b : bool) P := if b then ~P else P.
    
    (** Define a function for non-termination proof and termination
     proof. At [trsNonterminationProof] change to [false] to be able
     to proof the case of non-termination proof. *)
    
    Definition is_nt_proof p :=
      match p with
        | Proof_trsTerminationProof _ => true
        | Proof_trsNonterminationProof _ => false (* FIXME change to false *)
        | Proof_relativeTerminationProof _ => true (* CHECK *)
        | Proof_relativeNonterminationProof _ => true (* CHECK *)
        | Proof_dpProof _ => true
        | Proof_dpNonterminationProof _ => true (* TODO? *)
        | Proof_orderingConstraintProof _ => true
        (*| Proof_wcrProof _ => true
        | Proof_crProof _ => true
        | Proof_crDisproof _ => true
        | Proof_completionProof _ => true
        | Proof_equationalProof _ => true
        | Proof_equationalDisproof _ => true
        | Proof_complexityProof _ => true
        | Proof_quasiReductiveProof _ => true*)
      end.
    
    (** Define a function for non-termination proof and termination
     proof. If it is [true] then it is a termination proof else
     it is a non-termination proof. *)
    
    Definition is_nontermin_proof (c: certificationProblem) :=
      match c with
        | (_, _, p, _) => is_nt_proof p
      end.

  End main.

End S.