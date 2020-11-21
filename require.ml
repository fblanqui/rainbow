(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-05-29

manage modules to import
******************************************************************************)

open Util;;
open Printf;;

let modules_to_require = ref StrSet.empty;;
let modules_to_import = ref StrSet.empty;;

let init_modules () =
  modules_to_require := StrSet.empty;
  modules_to_import := StrSet.empty;;

let rec add s = function
  | [] -> s
  | m :: ms -> add (StrSet.add m s) ms;;

let require ms = modules_to_require := add !modules_to_require ms;;
let import ms = modules_to_import := add !modules_to_import ms;;

(*UNUSED:
let require_module b = bprintf b "Require Import %s.\n";;
let import_module b = bprintf b "Import %s.\n";;*)

let require_import_modules b =
  if !modules_to_require <> StrSet.empty then
    bprintf b "Require Import%a.\n"
      (fun b -> StrSet.iter (prefix " " string b)) !modules_to_require;
  if !modules_to_import <> StrSet.empty then
    bprintf b "Import%a.\n"
      (fun b -> StrSet.iter (prefix " " string b)) !modules_to_import;
  bprintf b "\nOpen Scope nat_scope.\n\n";
  init_modules ();;
