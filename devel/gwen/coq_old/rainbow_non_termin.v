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
  AFilterPerm AReverse AUnary cpf2color AModLoop.

(***********************************************************************)
(** Non Termination proof. *)

Section Non_Termination.
  
  (** [nat_of_string]: convert variable map to natural number *)
  
  Variable nat_of_string : string  -> nat.
  
  (***********************************************************************)
  (** ** Check that [R] is a violation of variable condition, it
     means there is a rule where the [lhs] is a variable, or the [rhs]
     contains variables not occuring in the [lhs] (it is in the
     definition of rewrite rule). 
     
     Definition: A pair [(l,r)] of terms is a rewrite rule if [l] is
     not a variable and [var(l) \subseteq var(r)]. *)
  
  Definition trsNonTerminationProof_variableConditionViolated a (R : arules a)  :=
    if brules_preserve_vars R then Ko _ ErNotVariableConditionViolated else OK.

  (***********************************************************************)
  (** ** Check that [p] is a valid non-termination proof for [red
     R]. Checking that there is a loop in a TRS. *)
  
  (* - [is_loop] is a boolean function testing non-termination in the
     case if there is a loop in TRS. It takes three arguments 
      + t : term
      + ds: [list data] type [list (position * arule)]
      + pos: position ([list nat])

      CPF loop in coq type: 
       [(term * list rewriteStep) * substitution * context]
       
     Use [color_term] to transform a [t: term] in CPF type
     into a [t: term] in CoLoR type.
     
     Use [positionInTerm] return [list position].

     Use [color_rewriteSequence] to return an CoLoR type
     [list data] where [ds: data] has type [position * rule].
     
     - Using [color_rewriteSequence] to return an CoLoR type
     [position = list nat].

     [rewriteStep : (positionInTerm x rule x option boolean x term)]
     [rewriteSequence := term x list rewriteStep]

   *)

  (* Define a function taking an argument of type [positionInTerm] and
       return a list of position. *)

  Fixpoint color_rewriteStep (a: symbol -> nat)
           (rs: list cpf.position * rule * option boolean * term ) :=
    let '(ps, r, _, _) := rs in
    Match color_list_position ps With ps ===>
          Match color_rule a nat_of_string r With r ===> Ok (ps, r).

  (* Define function return [list data]. *)

  Definition color_rewriteSequence a
             (ls:list (list cpf.position * rule * option boolean * term  )):
    result (list (list nat * arule a)) :=
    map (color_rewriteStep a) ls.

  (* Define function translate [context -> list position] *)

  Fixpoint color_position_of_context (c: context) : list nat :=
    match c with
      | Context_box => nil
      | Context_funContext _ l c _ =>
        List.length l :: color_position_of_context c
    end.

  (* FIXME *)
  (* loop = (term * list rewriteStep) * substitution * context *)

  Definition trsNonTerminationProof_loop a (R: arules a) (lo: cpf.loop)
  : result unit :=
    let '((t, ls), _, c) := lo in
    Match color_term a nat_of_string t With t ===>
          Match color_rewriteSequence a ls With ds ===>
          let pos := color_position_of_context c in
          if is_loop R t ds pos
          then OK else Ko _ ErtrsNonTerminationProof_loop. (* FIXME *)

  (***********************************************************************)
  (** ** Check that [p] is a valid non-termination proof for [red R].
     
     - [variableConditionViolated]: There is a rule where the lhs is a
     variable, or the rhs contains variables not occuring in the lhs.
     
     - [loop]: a loop is given by a (non-empty) rewrite-sequence t0 ->+
     tn where additional tn = C[t0 sigma]. *)
  
  (* FIXME *)

  Definition trsNonTerminationProof a (R: arules a) p : result unit :=
    match p with
      | TrsNonterminationProof_variableConditionViolated =>
        trsNonTerminationProof_variableConditionViolated R
      | TrsNonterminationProof_ruleRemoval _ _ =>
        Ko _ TTrsNonterminationProof_ruleRemoval
      | TrsNonterminationProof_stringReversal _ _ =>
        Ko _ TTrsNonterminationProof_stringReversal
      | TrsNonterminationProof_loop (((_, nil), _), _) =>
        Ko _ TTrsNonterminationProof_loop_nil
      | TrsNonterminationProof_loop lo => (* FIXME *)
        trsNonTerminationProof_loop R lo
      | TrsNonterminationProof_dpTrans _ _ _ =>
        Ko _ TTrsNonterminationProof_dpTrans
      | TrsNonterminationProof_nonterminationAssumption _ =>
        Ko _ TTrsNonterminationProof_nonterminationAssumption
      (*| TrsNonterminationProof_nonLoop _ =>
        Ko _ TTrsNonterminationProof_nonLoop
      | TrsNonterminationProof_nonterminationAssumption _ =>
        Ko _ TTrsNonterminationProof_nonterminationAssumption
      | TrsNonterminationProof_innermostLhssIncrease _ _ =>
        Ko _ TTrsNonterminationProof_innermostLhssIncrease*)
    end.

End Non_Termination.

(***********************************************************************)
(** ** Check that [R] is a violation of variable condition for
     [red_mod R D] *)

(* TODO *)
(*
Section Non_Rel_Termination.

  Variable nat_of_string : string  -> nat.  

  Definition relativeNonTerminationProof_variableConditionViolated a (R D: arules a) :=
    if brules_preserve_vars D then Ko _ ErNotVariableConditionViolated else OK.
  
  (***********************************************************************)
  (** ** Check that [p] is a valid non-termination proof for [red_mod
     R D]. Checking that there is a loop in a TRS. *)

  (* Define function return [mod_data = (list data * data)]. *)

  Definition color_mod_data a (ls: list rewriteStep): 
    result ((list (list nat * arule a)) * (list nat * arule a)) :=  
    match ls with
      | nil => (*Ko _ Tmod_data_nil (* TODO ? *)*) Ko _ Todo
      | l :: ls' =>
        Match color_rewriteStep nat_of_string a l With ds ===>
              Match color_rewriteSequence nat_of_string a ls' With mds ===>
              Ok (mds, ds)
    end.

  (* Define a type [list mod_data]. *)
  
  Definition color_list_mod_data a (ls: list (list rewriteStep)):
    result (list ((list (list nat * arule a)) * (list nat * arule a))) :=
    map (color_mod_data a) ls.

  Definition relativeNonTerminationProof_loop a (R D: arules a) (lo: cpf.loop) :
    result unit :=
    let '((t, ls), _, c) := lo in
    Match color_term a nat_of_string t With t ===>
          (* FIXME: (ls: nil) == list (list rewriteSequence) *)
          Match color_list_mod_data a (ls::nil) With mds ===>
          Match color_rewriteSequence nat_of_string a ls With ds ===>
          let pos := color_position_of_context c in
          if is_mod_loop R D t mds ds pos
          then OK else Ko _ ErrelativeNonTerminationProof_loop.
  
  (***********************************************************************)
  (** ** Check that [p] is a valid termination proof for [red_mod R D] 
     
     [variableConditionViolated]: There is a rule where the lhs is a
     variable, or the rhs contains variables not occuring in the lhs.
     
     [loop]: a loop is given by a (non-empty) rewrite-sequence t0 ->+
     tn where additional tn = C[t0 sigma]. *)
  
  Definition relativeNonterminationProof a (R D: arules a)
             (p: relativeNonterminationProof) : result unit :=
    match p with
      | RelativeNonterminationProof_loop lo =>
        relativeNonTerminationProof_loop R D lo
      | RelativeNonterminationProof_trsNonterminationProof _ =>
        Ko _ TRelativeNonterminationProof_trsNonterminationProof
      | RelativeNonterminationProof_variableConditionViolated =>
        relativeNonTerminationProof_variableConditionViolated R D
      | RelativeNonterminationProof_ruleRemoval _ _ _ =>
        Ko _ TRelativeNonterminationProof_ruleRemoval
      | RelativeNonterminationProof_nonterminationAssumption _ =>
        Ko _ TRelativeNonterminationProof_nonterminationAssumption
    end.

End Non_Rel_Termination.*)


(* FIXME *)

 (* Definition color_rewriteStep a (rstep: rewriteStep)
  : result ((list nat) * arule a) :=
    let '(ps, r, _, _) := rstep in
    Match color_list_position ps With ps ===>
          Match color_rule a nat_of_string r With r ===> Ok (ps, r).

  (* Define function return [list data]. *)

  Definition color_rewriteSequence a (ls: list rewriteStep):
    result (list (list nat * arule a)) :=
    map (color_rewriteStep a) ls.

  (* Define function translate [context -> list position] *)

  Fixpoint color_position_of_context (c: context) : list nat :=
    match c with
      | Context_box => nil
      | Context_funContext _ l c _ =>
        List.length l :: color_position_of_context c
    end.

  (* FIXME *)
  (* loop = (term * list rewriteStep) * substitution * context *)

  Definition trsNonTerminationProof_loop a (R: arules a) (lo: cpf.loop)
  : result unit :=
    let '((t, ls), _, c) := lo in
    Match color_term a nat_of_string t With t ===>
          Match color_rewriteSequence a ls With ds ===>
          let pos := color_position_of_context c in
          if is_loop R t ds pos
          then OK else Ko _ ErtrsNonTerminationProof_loop. (* FIXME *)

  (***********************************************************************)
  (** ** Check that [p] is a valid non-termination proof for [red R].
     
     - [variableConditionViolated]: There is a rule where the lhs is a
     variable, or the rhs contains variables not occuring in the lhs.
     
     - [loop]: a loop is given by a (non-empty) rewrite-sequence t0 ->+
     tn where additional tn = C[t0 sigma]. *)
  
  (* FIXME *)

  Definition trsNonTerminationProof a (R: arules a) p : result unit :=
    match p with
      | TrsNonterminationProof_variableConditionViolated =>
        trsNonTerminationProof_variableConditionViolated R
      | TrsNonterminationProof_ruleRemoval _ _ =>
        Ko _ TTrsNonterminationProof_ruleRemoval
      | TrsNonterminationProof_stringReversal _ _ =>
        Ko _ TTrsNonterminationProof_stringReversal
      | TrsNonterminationProof_loop (((_, nil), _), _) =>
        Ko _ TTrsNonterminationProof_loop_nil
      | TrsNonterminationProof_loop lo => (* FIXME *)
        trsNonTerminationProof_loop R lo
      | TrsNonterminationProof_dpTrans _ _ _ =>
        Ko _ TTrsNonterminationProof_dpTrans
      | TrsNonterminationProof_nonLoop _ =>
        Ko _ TTrsNonterminationProof_nonLoop
      | TrsNonterminationProof_nonterminationAssumption _ =>
        Ko _ TTrsNonterminationProof_nonterminationAssumption
      | TrsNonterminationProof_innermostLhssIncrease _ _ =>
        Ko _ TTrsNonterminationProof_innermostLhssIncrease
    end.

End Non_Termination.

(***********************************************************************)
(** ** Check that [R] is a violation of variable condition for
     [red_mod R D] *)

Section Non_Rel_Termination.

  Variable nat_of_string : string  -> nat.  

  Definition relativeNonTerminationProof_variableConditionViolated a (R D: arules a) :=
    if brules_preserve_vars D then Ko _ ErNotVariableConditionViolated else OK.
  
  (***********************************************************************)
  (** ** Check that [p] is a valid non-termination proof for [red_mod
     R D]. Checking that there is a loop in a TRS. *)

  (* Define function return [mod_data = (list data * data)]. *)

  Definition color_mod_data a (ls: list rewriteStep): 
    result ((list (list nat * arule a)) * (list nat * arule a)) :=  
    match ls with
      | nil => (*Ko _ Tmod_data_nil (* TODO ? *)*) Ko _ Todo
      | l :: ls' =>
        Match color_rewriteStep nat_of_string a l With ds ===>
              Match color_rewriteSequence nat_of_string a ls' With mds ===>
              Ok (mds, ds)
    end.

  (* Define a type [list mod_data]. *)
  
  Definition color_list_mod_data a (ls: list (list rewriteStep)):
    result (list ((list (list nat * arule a)) * (list nat * arule a))) :=
    map (color_mod_data a) ls.

  Definition relativeNonTerminationProof_loop a (R D: arules a) (lo: cpf.loop) :
    result unit :=
    let '((t, ls), _, c) := lo in
    Match color_term a nat_of_string t With t ===>
          (* FIXME: (ls: nil) == list (list rewriteSequence) *)
          Match color_list_mod_data a (ls::nil) With mds ===>
          Match color_rewriteSequence nat_of_string a ls With ds ===>
          let pos := color_position_of_context c in
          if is_mod_loop R D t mds ds pos
          then OK else Ko _ ErrelativeNonTerminationProof_loop.
  
  (***********************************************************************)
  (** ** Check that [p] is a valid termination proof for [red_mod R D] 
     
     [variableConditionViolated]: There is a rule where the lhs is a
     variable, or the rhs contains variables not occuring in the lhs.
     
     [loop]: a loop is given by a (non-empty) rewrite-sequence t0 ->+
     tn where additional tn = C[t0 sigma]. *)
  
  Definition relativeNonterminationProof a (R D: arules a)
             (p: relativeNonterminationProof) : result unit :=
    match p with
      | RelativeNonterminationProof_loop lo =>
        relativeNonTerminationProof_loop R D lo
      | RelativeNonterminationProof_trsNonterminationProof _ =>
        Ko _ TRelativeNonterminationProof_trsNonterminationProof
      | RelativeNonterminationProof_variableConditionViolated =>
        relativeNonTerminationProof_variableConditionViolated R D
      | RelativeNonterminationProof_ruleRemoval _ _ _ =>
        Ko _ TRelativeNonterminationProof_ruleRemoval
      | RelativeNonterminationProof_nonterminationAssumption _ =>
        Ko _ TRelativeNonterminationProof_nonterminationAssumption
    end.

End Non_Rel_Termination. *)
