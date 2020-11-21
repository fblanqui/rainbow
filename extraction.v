(************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2009-03-24

A set-up for extraction of rainbow.v.
************************************************************************)

(* Allows extract singleton of one contructor, parsing function
newcpf.ml in the case of 'equationalDisproof' element. *)

Set Extraction KeepSingleton.

Extraction Blacklist string list cpf.

Require Import ExtrOcamlBasic ExtrOcamlZInt ExtrOcamlNatInt
               rainbow_main cpf2color NArith.

Cd "tmp".

(*REMARK: we get a problem for compiling tmp/AUnif.ml when doing
Recursive Extraction Library rainbow. *)

Separate Extraction check arity_in_pb.
