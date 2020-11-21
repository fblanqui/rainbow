(******************************************************************************
Rainbow, a termination proof certification tool
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-05-31

representation of problems in color
******************************************************************************)

open Printf;;
open Util;;
open Problem;;
open Require;;
open Error;;

(*****************************************************************************)
(* coq module *)
(*****************************************************************************)

(*UNUSED:
let coq_module b m k f x =
  bprintf b "Module %s%d.\n%aEnd %s%d.\n\n" m k f x m k;;*)

(*****************************************************************************)
(* datatypes *)
(*****************************************************************************)

let bool b = function
  | true -> bprintf b "true"
  | false -> bprintf b "false";;

let coq_list elt = list_nil "nil" "::" elt;;

let vector elt =
  let rec aux b = function
    | [] -> bprintf b "Vnil"
    | [x] -> bprintf b "Vcons %a Vnil" elt x
    | x::xs -> bprintf b "Vcons %a (%a)" elt x aux xs
  in aux;;

let vector_pat elt =
  let rec aux b = function
    | [] -> bprintf b "Vnil"
    | [x] -> bprintf b "Vcons %a _ Vnil" elt x
    | x::xs -> bprintf b "Vcons %a _ (%a)" elt x aux xs
  in aux;;

let option elt b = function
  | Some x -> bprintf b "Some %a" elt x
  | None -> bprintf b "None";;

let set elt b = SymbSet.iter (elt b);;

(*****************************************************************************)
(* kind of signature: algebraic or varyadic *)
(*****************************************************************************)

type sig_kind = A | V;;

let string_of_sig_kind = function A -> "A" | V -> "V";;

let sig_kind b k = bprintf b "%s" (string_of_sig_kind k);;

let sig_kind_module k m = string_of_sig_kind k ^ m;;

(*****************************************************************************)
(* table of signatures *)
(*****************************************************************************)

let init_amap, new_sig_id, get_amap, parent_sig =
  let n = ref 1 and imap = ref IntMap.empty in
    (fun m -> imap := IntMap.add 1 (m,0) IntMap.empty),
    (fun s m -> n := succ !n; imap := IntMap.add !n (m,s) !imap; !n),
    (fun s -> fst (IntMap.find s !imap)),
    (fun s -> snd (IntMap.find s !imap));;

let arity s f = SymbMap.find f (get_amap s);;

(*****************************************************************************)
(* symbols *)
(*****************************************************************************)
let rec symbol_sig s b =
  let sp = parent_sig s in
  let aux = symbol_sig sp in function
    | Ident s -> bprintf b "M.%s" s
    | Hd f -> bprintf b "(@hd_symb S%d.Sig %a)" sp aux f
    | Int f -> bprintf b "(@int_symb S%d.Sig %a)" sp aux f
    | Label (f, ls) ->
	bprintf b "@mk S%d.Sig _ %a %a" sp aux f (plist (vector aux)) ls;;

let rec symbol_pat s b =
  let sp = parent_sig s in
  let aux = symbol_pat sp in function
    | Ident s -> bprintf b "M.%s" s
    | Hd f -> bprintf b "(hd_symb %a)" aux f
    | Int f -> bprintf b "(int_symb %a)" aux f
    | Label (f, ls) -> bprintf b "mk %a %a"
	aux f (plist (vector_pat aux)) ls;;

(*UNUSED:
let symb_map symb_mapping b = SymbMap.iter (symb_mapping b);;*)

(*****************************************************************************)
(* function definition by case analysis *)
(*****************************************************************************)

let mapping fn s b (f,x) =
  bprintf b "      | %a => %a\n" (symbol_pat s) f fn x;;

let clauses fn s default b l =
  list "" (mapping fn s) b l;
  if List.length l < nb_symbols (get_amap s) then
    bprintf b "      | f => %s\n" default;;

let add_prefix p s = if s = "" then "" else p ^ s;;

let matching x return fn s default b l =
  bprintf b "    match %s%s with\n%a    end."
    x (add_prefix " " return) (clauses fn s default) l;;

let fun_def n x it ot return fn s default b l =
  bprintf b "Definition %s (%s : %s)%s :=\n%a"
    n x it (add_prefix " : " ot) (matching x return fn s default) l;;

let fun_def_symb n ot return fn s default b l =
  fun_def n "f" (sprintf "S%d.Sig" s) ot return fn s default b l;;

(*****************************************************************************)
(* terms *)
(*****************************************************************************)

let fun_symbol s b f = bprintf b "@Fun S%d.Sig %a" s (symbol_sig s) f;;

let var s b i = bprintf b "(@Var S%d.Sig %d)" s i;;

let term_aux terms s =
  let rec aux b = function
    | Var i -> var s b i
    | App (f, ts) ->
	bprintf b "(%a %a)" (fun_symbol s) f (plist (terms aux)) ts
  in aux;;

let term = function
  | A -> term_aux vector
  | V -> term_aux coq_list;;

let word = par (coq_list (symbol_sig 1));;

(*****************************************************************************)
(* rules *)
(*****************************************************************************)

let rule_aux m term s b r =
  bprintf b "@%s.mkRule S%d.Sig\n     %a\n     %a"
    m s (term s) r.trs_lhs (term s) r.trs_rhs;;

let rule k = rule_aux (sig_kind_module k "Trs") (term k);;

let srs_rule b r =
  bprintf b "@Srs.mkRule S1.Sig\n     %a\n     %a"
    word r.srs_lhs word r.srs_rhs;;

(*****************************************************************************)
(* type of symbols *)
(*****************************************************************************)

let symbol_decl b f = bprintf b "\n  | %s : symb" (ident_of_symbol f);;

(* print symbols using ocaml default total ordering *)
let symbol_type b ss = bprintf b "(* set of function symbols *)\n\n\
  Module M.\n  Inductive symb : Type :=%a.\nEnd M.\n\n"
  (list "" symbol_decl) (List.sort Pervasives.compare (SymbSet.elements ss));;

(*****************************************************************************)
(* decidability of equality *)
(*****************************************************************************)

let beq_symb b fs =
  let default_case b fs =
    if not (is_singleton fs) then bprintf b "\n  | _, _ => false" in
  let case b s =
    bprintf b "\n  | %a, %a => true" (symbol_sig 1) s (symbol_sig 1) s in
  bprintf b "Definition beq_symb (f g : M.symb) : bool :=\n  \
    match f, g with%a%a\nend.\n\n" (set case) fs default_case fs;;

let beq_symb_ok b = bprintf b
  "Lemma beq_symb_ok : forall f g : M.symb, beq_symb f g = true <-> f = g.\n\
  Proof. beq_symb_ok. Qed.\n\n"

let decidability_lemma b fs =
  require ["EqUtil"];
  beq_symb b fs;
  beq_symb_ok b;;

(*****************************************************************************)
(* arity function *)
(*****************************************************************************)

let arity_function b amap =
  fun_def "ar" "f" "M.symb" "nat" "" int 1 "0" b (SymbMap.bindings amap);
  bprintf b "\n\n";;
 
(*REMOVE:  let case b f k = bprintf b "\n  | %a => %d" (symbol_pat 1) f k in
    fun b -> bprintf b
      "Definition ar (s : M.symb) : nat :=\n  match s with%a\n  end.\n\n"
      (symb_map case);;*)

(*****************************************************************************)
(* signature module *)
(*****************************************************************************)

let weight k s b amap =
  let new_weight = counter() in
  fun_def "weight" "f" "Sig" "nat" "" (fun b _ -> int b (new_weight()))
    s "0" b (SymbMap.bindings amap);
  bprintf b "\n  \
    Lemma weight_inj : forall f g, weight f = weight g -> f = g.\n  \
    Proof. %aSignature.weight_inj Fs_ok. Qed." sig_kind k;;

let some_symbol_def s b f =
  bprintf b "\n  Definition some_symbol : Sig := %a." (symbol_sig s) f;;

let arity_some_symbol_gt0 b =
  require ["NatUtil"];
  bprintf b "\n  Lemma arity_some_symbol : arity some_symbol > 0.\n  \
    Proof. check_gt. Qed.";;

let arity_some_symbol_eq2 b =
  bprintf b "\n  Lemma arity_some_symbol_eq_2 : arity some_symbol = 2.\n  \
    Proof. refl. Qed.";;

let arity_some_symbol s b amap =
  match symbol_of_arity 2 amap with
    | Some f ->	some_symbol_def s b f;
	arity_some_symbol_gt0 b; arity_some_symbol_eq2 b
    | None ->
	match symbol_of_arity_gt0 amap with
	  | Some f -> some_symbol_def s b f; arity_some_symbol_gt0 b
	  | None ->
	      if not (SymbMap.is_empty amap) then
		some_symbol_def s b (fst (SymbMap.choose amap));;

let sig_module b k s sd pfs fs amap = bprintf b
  "(* signature %d *)\n\n\
  Module S%d.\n  \
    Definition Sig := %s.\n  \
    Definition Fs : list Sig := %a.\n  \
    Lemma Fs_ok : forall f : Sig, In f Fs.\n  \
    Proof. list_ok. Qed.\n  %a%a\n\
  End S%d.\n\n" s s sd pfs fs (weight k s) amap (arity_some_symbol s) amap s;;

let sig_module_of_amap b k s sd amap =
  sig_module b k s sd (coq_list (symbol_sig s)) (symbols_of_map amap) amap;;

let sig_include b k s m amap = bprintf b
  "(* signature %d *)\n\n\
  Module S%d.\n  \
    Include (%s).\n  %a%a\n\
  End S%d.\n\n" s s m (weight k s) amap (arity_some_symbol s) amap s;;

let sig_def = function
  | A -> "ASignature.mkSignature ar beq_symb_ok"
  | V -> "VSignature.mkSignature beq_symb_ok"

let signature k b amap =
  require [sig_kind_module k "Trs"; "ListUtil"; "VecUtil"];
  sig_module_of_amap b k 1 (sig_def k) amap;;

let srs_signature b amap =
  require ["Srs"; "ListUtil"];
  sig_module_of_amap b V 1 (sig_def V) amap;;

(*****************************************************************************)
(* definition of the set of rules *)
(*****************************************************************************)

let rules_aux m rule name s b rs =
  require [m];
  bprintf b "Definition %s : %s.rules S%d.Sig :=\n   %a.\n\n"
    name m s (list_nil "nil" "\n:: " rule) (List.rev rs);;

let rules k name s = rules_aux (sig_kind_module k "Trs") (rule k s) name s;;

let srs_rules = rules_aux "Srs" srs_rule;;

(*****************************************************************************)
(* axioms *)
(*****************************************************************************)

let commut_rule f = {
  trs_lhs = App (f, [Var 0; Var 1]);
  trs_rhs = App (f, [Var 1; Var 0]);
  trs_conds = []};;

let assoc_right_rule f = {
  trs_lhs = App (f, [App (f, [Var 0; Var 1]); Var 2]);
  trs_rhs = App (f, [Var 0; App (f, [Var 1; Var 2])]);
  trs_conds = []};;

let assoc_left_rule f = {
  trs_lhs = App (f, [Var 0; App (f, [Var 1; Var 2])]);
  trs_rhs = App (f, [App (f, [Var 0; Var 1]); Var 2]);
  trs_conds = []};;

let rule_of_equation u v = {
  trs_lhs = u;
  trs_rhs = v;
  trs_conds = []};;

let add_axiom acc = function
  | Builtin (s, Associative) ->
      assoc_left_rule s :: assoc_right_rule s :: acc
  | Builtin (s, Commutative) -> commut_rule s :: acc
  | Builtin (s, AssociativeCommutative) ->
      assoc_right_rule s :: commut_rule s :: acc
  | Equation (u, v) when variables_of_term u = variables_of_term v ->
    rule_of_equation u v :: rule_of_equation v u :: acc
  | Equation _ -> not_supported "erasing equations";;

let rec add_axioms acc = function
  | [] -> acc
  | ax :: axs -> warning "axioms are handled like relative rules";
      add_axioms (add_axiom acc ax) axs;;

(*****************************************************************************)
(* problems *)
(*****************************************************************************)

let amap_of_set ss =
  SymbSet.fold (fun f m -> SymbMap.add f 0 m) ss SymbMap.empty;;

let trs b p =
  if p.trs_strategy <> None then not_supported "strategies";
  match p.trs_algebra with
    | Varyadic ->
	let amap = amap_of_set p.trs_symbols in
	init_amap amap;
	symbol_type b p.trs_symbols;
	decidability_lemma b p.trs_symbols;
	signature V b amap;
	bprintf b "(* rewrite rules *)\n\n";
	rules V "E" 1 b (add_axioms p.trs_le_rules p.trs_axioms);
	rules V "R" 1 b p.trs_rules;
	bprintf b "Definition rel := VTrs.red_mod E R.\n\n"
    | Signature amap ->
	init_amap amap;
	symbol_type b p.trs_symbols;
	decidability_lemma b p.trs_symbols;
	arity_function b amap;
	signature A b amap;
	bprintf b "(* rewrite rules *)\n\n";
	rules A "E" 1 b (add_axioms p.trs_le_rules p.trs_axioms);
	rules A "R" 1 b p.trs_rules;
	bprintf b "Definition rel := ATrs.red_mod E R.\n\n";;

let srs b p =
  if p.srs_strategy <> None then not_supported "strategies";
  let amap = amap_of_set p.srs_symbols in
  init_amap amap;
  symbol_type b p.srs_symbols;
  decidability_lemma b p.srs_symbols;
  srs_signature b amap;
  bprintf b "(* rewrite rules *)\n\n";
  srs_rules "E" 1 b p.srs_le_rules;
  srs_rules "R" 1 b p.srs_rules;
  bprintf b "Definition rel := Srs.red_mod E R.\n\n";;

let genr_problem b = function
  | Trs p -> trs b p
  | Srs p -> srs b p;;
