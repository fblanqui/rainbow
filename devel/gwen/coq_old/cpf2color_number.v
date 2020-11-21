(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2011-04-06

* Translate CPF type into CoLoR type.

*)

(* TODO: MOVE this file into cpf_util. *)

Set Implicit Arguments.

Require Import cpf cpf_util.

(****************************************************************************)
(** ** Formalization of polynomial interpretation on domain of natural
numbers. *)

(** Translate [number] of CPF type into CoLoR type. *)

Section number.
 
  Open Scope Z_scope.
    
  Definition color_number n : result integer :=
    match n with
      | Number_integer i => Ok i
      | Number_rational i pos => Ko _ TnumberRational
    end.
  
  Close Scope Z_scope.

  (** Translate [number] in the case of rational numbers. Rationals are
     pairs of Z and positive numbers. *)
  
  Require Import QArith.
  
  Open Scope Q_scope.
  
  Definition color_number_rationals n : result Q :=
    match n with
      | Number_integer i => Ok (inject_Z i) (* i/1 *)
      | Number_rational i pos => Ok (Qmake i pos)
    end.

  Close Scope Q_scope.
 
End number.