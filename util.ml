(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

modules and functions on basic data structures
******************************************************************************)

open Printf;;
open Lexing;;

(*****************************************************************************)
(* XML positions *)
(*****************************************************************************)

let dummy_pos = 0, 0, 0, 0;;

let error_pos = function
  | 0, 0, 0, 0 -> ""
  | eline, eline_start, emin, emax ->
      sprintf "line %d, character" eline ^
	(if emin = emax then sprintf " %d: " (emin - eline_start)
	 else sprintf "s %d-%d: " (emin - eline_start) (emax - eline_start));;

(*****************************************************************************)
(* Lexing positions *)
(*****************************************************************************)

let lex_pos oc l =
  fprintf oc "file \"%s\", line %d, character %d"
    l.pos_fname l.pos_lnum (l.pos_cnum - l.pos_bol + 1);;

(*****************************************************************************)
(* file extension *)
(*****************************************************************************)

let extension s =
  let s = Filename.basename s in
    try
      let i = String.rindex s '.' in
	Some (String.sub s (i+1) (String.length s-i-1))
    with Not_found -> None;;

(*****************************************************************************)
(* file parsing *)
(*****************************************************************************)
 
let parse_file f s =
  let ic = open_in s in
  let x = f ic in
    close_in ic; x;;

(*****************************************************************************)
(** exit function *)
(*****************************************************************************)

let error s = eprintf "error: %s\n" s; exit 1;;

(*****************************************************************************)
(** generic functions for handling references *)
(*****************************************************************************)

let get_set init =
  let r = ref init in
    (fun () -> !r),
    (fun v -> r := v);;

let get_set_bool () =
  let r = ref false in
    (fun () -> !r),
    (fun () -> r := true);;

(*****************************************************************************)
(** verbose and debug modes *)
(*****************************************************************************)

let get_verbose, set_verbose = get_set_bool ();;
let get_debug, set_debug = get_set_bool ();;
let get_hack, set_hack = get_set_bool ();;

(*****************************************************************************)
(* counters *)
(*****************************************************************************)

let counter () = let k = ref 0 in fun () -> k := succ !k; !k;;

(*****************************************************************************)
(** ordered types *)
(*****************************************************************************)

module type TYP = sig type t end;;

module type ORD = Set.OrderedType

module Ord = struct
  module Make (M : TYP) : ORD with type t = M.t = struct
    type t = M.t
    let compare = Pervasives.compare
  end
end;;

(*****************************************************************************)
(* integers *)
(*****************************************************************************)

module Int = struct type t = int end;;
module IntOrd = Ord.Make (Int);;
module IntSet = Set.Make (IntOrd);;
module IntMap = Map.Make (IntOrd);;

let int_set_of_list fmap =
  let rec aux acc = function
    | [] -> acc
    | x :: xs -> aux (IntSet.union (fmap x) acc) xs
  in aux IntSet.empty;;

(*REMARK: put in cache?*)

let rec nats_decr_lt n =
  if n <= 0 then [] else let p = n-1 in p :: nats_decr_lt p;;

let nats_incr_lt n = List.rev (nats_decr_lt n);;

(*****************************************************************************)
(* characters *)
(*****************************************************************************)

let is_alpha_char_code i = i >= 97 && i <= 122;;
let is_Alpha_char_code i = i >= 65 && i <= 90;;
let is_digit_char_code i = i >= 48 && i <= 57;;

let is_space = function
  | ' ' | '\n' | '\t' -> true
  | _ -> false;;

let is_digit c = is_digit_char_code (Char.code c);;

(*****************************************************************************)
(* printing *)
(*****************************************************************************)

open Printf;;

type 'a bprint = Buffer.t -> 'a -> unit;;
type 'a fprint = out_channel -> 'a -> unit;;

let fprint f oc x =
  let b = Buffer.create 100 in
    f b x; fprintf oc "%s" (Buffer.contents b);;

let sprint f x =
  let b = Buffer.create 100 in
    f b x; sprintf "%s" (Buffer.contents b);;

let string b s = bprintf b "%s" s;;
let int b i = bprintf b "%d" i;;
let int64 b i = bprintf b "%Ld" i;;
let bool b x = bprintf b "%b" x;;

let option f b = function
  | None -> string b "None"
  | Some x -> bprintf b "Some (%a)" f x;;

let pair f sep g b (x, y) = bprintf b "%a%s%a" f x sep g y;;
let first f b (x,_) = f b x;;
let second f b (_,x) = f b x;;

let par f b x = bprintf b "(%a)" f x;;

let prefix s f b x = bprintf b "%s%a" s f x;;
let postfix s f b x = bprintf b "%a%s" f x s;;
let endline f b x = postfix "\n" f b x;;

(*****************************************************************************)
(* lists *)
(*****************************************************************************)

let rec append_map f xs1 xs2 =
  match xs1 with
    | [] -> xs2
    | x1 :: xs -> append_map f xs (f x1 :: xs2);;

let iteri f =
  let rec aux k = function
    | [] -> ()
    | x :: xs -> f k x; aux (k+1) xs
  in aux 1;;

let position x =
  let rec aux k = function
    | [] -> raise Not_found
    | y :: ys -> if x = y then k else aux (k+1) ys
  in aux 0;;

let flat_map f =
  let rec aux = function
    | [] -> []
    | x :: xs -> f x @ aux xs
  in aux;;

let clist x =
  let rec aux k = if k <= 0 then [] else x :: aux (k-1) in aux;;

(* split_last x1 [x2;..;xn;xn+1] = [x1;..;xn], xn+1 *)

(*let rec split_last y = function
  | [] -> [], y
  | x :: xs -> let l, z = split x xs in y :: l, z;;*)

let split_last =
  let rec split_aux prefix prev_elt = function
    | [] -> List.rev prefix, prev_elt
    | x :: xs -> split_aux (prev_elt :: prefix) x xs
  in fun x -> split_aux [] x;;

let map_split_last f =
  let rec split_aux prefix prev_elt = function
    | [] -> List.rev prefix, prev_elt
    | x :: xs -> split_aux (prev_elt :: prefix) (f x) xs
  in fun x -> split_aux [] (f x);;

let repeat n x =
  let rec aux n = if n <= 0 then [] else x :: aux (n-1)
  in aux n;;

let rec last y = function
  | [] -> y
  | x :: xs -> last x xs;;

let rec remove_last = function
  | [] | [_] -> []
  | x :: xs -> x :: remove_last xs;;

let rec remove_first l x =
  match l with
    | [] -> []
    | y :: ys -> if y = x then ys else y :: remove_first ys x;;

let remove_firsts l xs = List.fold_left remove_first l xs;;

let list sep elt =
  let rec aux b = function
    | [] -> ()
    | [x] -> elt b x
    | x :: l -> bprintf b "%a%s%a" elt x sep aux l
  in aux;;

let list_nil nil sep elt =
  let rec aux b = function
    | [] -> bprintf b "%s" nil
    | x :: l -> bprintf b "%a%s%a" elt x sep aux l
  in aux;;

let plist f b = function
  | [] -> f b []
  | l -> par f b l;;

(*****************************************************************************)
(** strings *)
(*****************************************************************************)

let int_of_string s = Scanf.sscanf s " %d " (fun x -> x);;
let int64_of_string s = Scanf.sscanf s " %Ld " (fun x -> x);;
let float_of_string s = Scanf.sscanf s " %f " (fun x -> x);;
let bool_of_string s = Scanf.sscanf s " %b " (fun x -> x);;

module Str = struct type t = string end;;
module StrOrd = Ord.Make (Str);;
module StrSet = Set.Make (StrOrd);;
module StrMap = Map.Make (StrOrd);;

type renaming = string StrMap.t;;

let renaming_map fmap =
  let f s = StrMap.add s (fmap s) in
    fun set -> StrSet.fold f set StrMap.empty;;

let set_add_chk x s =
  if StrSet.mem x s then failwith (x ^ " already declared")
  else StrSet.add x s;;

let add_chk x y m =
  if StrMap.mem x m then failwith (x ^ " already declared")
  else StrMap.add x y m;;

let merge_chk m1 m2 = StrMap.fold add_chk m1 m2;;

let set sep b s = list sep string b (StrSet.elements s);;

let pset sep b = bprintf b "{%a}" (set sep);;

let map sep elt postfix b m =
  list postfix (pair string sep elt) b (StrMap.bindings m);;

let pmap sep elt postfix b = bprintf b "{%a}" (map sep elt postfix);;

(*****************************************************************************)
(* variable map *)
(*****************************************************************************)

let init_var_map, var =
  let v = ref 0 and m = ref StrMap.empty in
    (fun () -> v := 0; m := StrMap.empty),
    (fun s -> try StrMap.find s !m
     with Not_found -> v := succ !v; m := StrMap.add s !v !m; !v);;
