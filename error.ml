(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

warnings and errors
******************************************************************************)

open Util;;
open Xml;;
open Printf;;

let pos_of_xml = function
  | Element (_, p, _, _) -> p
  | PCData (_, p) -> p;;

(*****************************************************************************)
(* warnings *)
(*****************************************************************************)

let warning =
  let ws = ref StrSet.empty in fun s ->
    if not (StrSet.mem s !ws) then
      (ws := StrSet.add s !ws; eprintf "Warning: %s.\n" s);;

let ignored s = warning (s ^ " are ignored");;

(*****************************************************************************)
(* errors *)
(*****************************************************************************)

type error_type =
  | ErrorNotSupported of string
  | ErrorXML of string * xml
  | ErrorFormat of string;;

type error = error_type * pos;;

exception Error of error;;

let raise_error e p = raise (Error (e, p));;

let not_supported s = raise_error (ErrorNotSupported s) dummy_pos;;

let error_xml x s = raise_error (ErrorXML (s,x)) (pos_of_xml x);;

let error_fmt s = raise_error (ErrorFormat s) dummy_pos;;

let truncate =
  let max = 80 in fun x ->
    let s = Xml.to_string x in
    if String.length s > max then String.sub s 0 max else s;;

let error_msg = function
  | ErrorNotSupported s -> sprintf "Error: %s not supported." s
  | ErrorXML (s, x) -> sprintf "XML error: %s: %s" s (truncate x)
  | ErrorFormat s -> sprintf "Format error: %s." s;;

let print_error oc (e, p) =
  fprintf oc "UNSUPPORTED \n %s\n%s\n"
    (if p = dummy_pos then "" else error_pos p) (error_msg e);;

let exit_status = function
  | ErrorNotSupported _ -> 2
  | ErrorXML _ | ErrorFormat _ -> 1;;

let run main =
  try main()
  with Error e -> print_error stderr e; exit (exit_status (fst e));;
