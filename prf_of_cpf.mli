(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-08-31

converting a cpf proof into a rainbow proof
******************************************************************************)

val term : bool -> Cpf.term -> Problem.term;;
val certificate : Cpf.certificationProblem -> Proof.certificate;;
