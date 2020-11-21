(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-05-29

Generate a log file by exploring the current directory.
******************************************************************************)

open Log;;
open Sys;;

let set_ext, get_ext =
  let ext = ref "cpf" in
    (fun s -> ext := s),
    (fun () -> !ext);;

let main() =
  if Array.length argv > 1 then set_ext argv.(1);
  directory (get_ext()) print_data ".";;

main();;
