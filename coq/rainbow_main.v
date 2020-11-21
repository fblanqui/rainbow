(**
Rainbow, a termination proof certification tool

See the COPYRIGHTS and LICENSE files.

- Kim Quyen LY, 2014-06-30

* CPF correctness checker

 TO BE FINISHED: proving relative termination 
*)

Require Import cpf2color cpf error_monad String rainbow_full_termin
rainbow_relation_termin RelUtil LogicUtil SN.

(***********************************************************************)
(** ** Check that [p] is a valid relative non-termination proof:
       [red_mod R D]. *)

Section S.

  (* maximum number of arguments compared lexicographically in RPO *)
  Variable rpo_arg: nat.

  (* converting variable to natural numbers *)
  Variable nat_of_string : string -> nat.

  (* an argument for structural descreasing *)
  Variable n: nat.

  (* termination argument for unification *)
  Variable uni: nat.

  Definition proof a (s:system a) p :=
    match s, p with
      | Red R, Proof_trsTerminationProof p               =>
        trsTerminationProof nat_of_string rpo_arg n uni n R p
      | Red R, Proof_trsNonterminationProof p            =>
        trsNonTerminationProof nat_of_string R p
      | Red_mod E R, Proof_relativeTerminationProof p    =>
        relTerminationProof E R p (* TODO *)
      | Red_mod E R, Proof_relativeNonterminationProof p =>
        relativeNonterminationProof nat_of_string E R p
      | Hd_red_mod E R, Proof_dpProof p                  =>
        dpProof nat_of_string rpo_arg n uni E R p
      | Hd_red_mod E R, Proof_dpNonterminationProof _    =>
        (* TODO: dp_counter example loop? *)
        Ko _ (Todo TProof_dpNonterminationProof)
      | _, Proof_orderingConstraintProof _               =>
        Ko _ (Todo TProof_orderingConstraintProof)
      | _, _                                             =>
        Ko _ (Error EinputProofIncompatible)
    end.
  
  Definition check a (c: certificationProblem) :=
    match c with
      | (_, _, p, _) => Match sys_of_pb a nat_of_string c With s
                     ===> proof a s p
    end.

  
  (* how to express the correctness of main ? *)  
  
  Definition not_if (b : bool) P := if b then ~P else P.
  
  (** Define a function for non-termination proof and termination
     proof. At [trsNonterminationProof] change to [false] to be able
     to proof the case of non-termination proof. *)
  
  Definition is_termin_proof p :=
    match p with
      | Proof_trsTerminationProof _         => true
      | Proof_trsNonterminationProof _      => false
      | Proof_relativeTerminationProof _    => true
      | Proof_relativeNonterminationProof _ => false
      | Proof_dpProof _                     => true
      | Proof_dpNonterminationProof _       => false
      | Proof_orderingConstraintProof _     => true
      | Proof_wcrProof _                    => true
      | Proof_crProof _                     => true
      | Proof_crDisproof _                  => true
      | Proof_completionProof _             => true
      | Proof_equationalProof _             => true
      | Proof_equationalDisproof _          => true
      | Proof_complexityProof _             => true
      | Proof_quasiReductiveProof _         => true
    end.
  
  (** Define a function for non-termination proof and termination
     proof. If it is [true] then it is a termination proof else
     it is a non-termination proof. *)
  
  Definition is_termin_cert (c : certificationProblem) :=
    match c with (_, _, p, _) => is_termin_proof p end.
  
  (***********************************************************************)
  (** Structure proof of main 

        1. Proof of [red R].

        2. Proof of non termination [red R].

        3. Proof of [red_mod R D].

        4. Proof of non termination [red_mod R D].

        5. Proof of [hd_red_mod R D]. *)

  Lemma check_ok : forall c,
    let a := arity_in_pb c in
    forall s, sys_of_pb a nat_of_string c = Ok s ->
              check a c                   = OK   ->
              not_if (is_termin_cert c) (EIS (rel_of_sys s)).
  
  Proof.
    intros cp a s Hs Hm. unfold check in Hm. rewrite Hs in Hm.
    destruct cp as [[[i st] p] o].
    simpl arity_in_pb in *. simpl sys_of_pb in *. simpl is_termin_proof.
    unfold proof in Hm.
    destruct s; destruct p; try discr; simpl.
    apply WF_notEIS.
    (** 1. Correctness proof of termination problem for [red R]. *)     
    eapply trsTerminationProof_ok.
    (*apply Hs.*) apply Hm.
    (** 2. Correctness proof of non-termination problem for [red R]. *)      
    eapply trsNonTerminationProof_ok.
    apply Hm.
    (** 3. Correctness proof of termination problem for [red_mod R
      D]. *)
    apply WF_notEIS.
    eapply rel_TerminationProof_ok. apply Hs. apply Hm.
    (** 4. Correctness proof of non-termination problem for [red_mod
      R D]. *)
    unfold relativeNonterminationProof in Hm.
    destruct r; simpl; try discr.
    (** Correctness proof of non-termination proof for [red_mod R D]
       in the case of loop. *)
    apply relativeNonTerminationProof_loop_ok in Hm. apply Hm.
    (** Correctness proof of non-termination proof for [red_mod R D] in
        the case of variable condition violated. *)   
    apply relativeNonTerminationProof_variableConditionViolated_ok.
    apply Hm.     
    (** 5. Correctness proof of termination for top termination
       problems (dpProof). [hd_red_mod R (dp R)] *)
    apply WF_notEIS. eapply dpProof_ok. apply Hm.
    (* TODO : other cases *)
  Qed.

End S.
